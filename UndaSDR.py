#!/usr/bin/env python3
"""
Radio FM cu RTL-SDR (Realtek DVB-T / Astrometa) - GUI simplu.

Funcții: căutare automată de posturi, listă memorată (butoane), nume + text RDS,
mute, volum, ieșire audio PipeWire, start/stop.

Fără blacklist și fără reconectare USB: la Start, programul detașează singur
driverul kernel DVB (dvb_usb_rtl28xxu) de pe dongle prin usbfs, iar la Stop /
la ieșire îl reatașează => tunerul TV apare din nou în aplicațiile TV.

Dependențe (doar din apt, nimic din pip):
    sudo apt install rtl-sdr alsa-utils python3-tk python3-numpy     # necesare
    sudo apt install python3-scipy                                   # opțional (doar RDS)
    sudo apt install ffmpeg                                          # opțional (doar înregistrarea)
  - rtl_tcp (din rtl-sdr) citește dongle-ul; programul vorbește cu el pe localhost
  - aplay (din alsa-utils) redă sunetul
  - python3-numpy: demodulare FM, filtrare și scanare
  - python3-scipy: doar decodarea RDS; fără el radioul merge normal, iar caseta
    RDS rămâne dezactivată
  - ffmpeg: doar înregistrarea audio (WAV/FLAC/MP3/AAC); fără el butonul REC
    rămâne dezactivat

Rulare:
    python3 radiosdr.py

Structura fișierului (un singur fișier; secțiunile sunt independente și apar în
ordinea dependențelor, ca să poată fi mutate ușor în module separate):
    1. Dependențe și configurare   detectare numpy/scipy/rtl_tcp/aplay, constante
    2. DSP (numpy)                 filtre, spectru, detecție vârfuri, FmDemod
    3. RDS                         decodor RDS (necesită scipy)
    4. Driver DVB (USB)            detașare/reatașare automată a driverului kernel
    5. Client rtl_tcp              citirea eșantioanelor IQ de la dongle
    6. Audio și înregistrare       ieșire prin aplay; înregistrare prin ffmpeg
    7. Engine                      fire de execuție: citire -> demodulare -> audio; scanare
    8. Texte interfață (I18N)      ro / en / it
    9. Interfață (Tkinter)         ToolTip, App
   10. main
"""
import atexit
import errno
import fcntl
import glob
import json
import math
import os
import queue
import re
import shutil
import socket
import struct
import subprocess
import tempfile
import threading
import time
import tkinter as tk
from tkinter import ttk, messagebox, simpledialog, filedialog


# ============================================================================
#  1. DEPENDENȚE ȘI CONFIGURARE
# ============================================================================
MISSING_DEPS = []        # dependențe necesare care lipsesc (blochează pornirea radioului)

try:
    import numpy as np
    HAS_NUMPY = True
except ImportError:
    HAS_NUMPY = False
    MISSING_DEPS.append("numpy (apt install python3-numpy)")

try:
    from scipy import signal          # folosit doar de decodorul RDS
    HAS_SCIPY = True
except ImportError:
    HAS_SCIPY = False

HAS_RDS_DEPS = HAS_NUMPY and HAS_SCIPY    # RDS e opțional: dezactivat dacă lipsește scipy
HAS_FFMPEG = bool(shutil.which("ffmpeg"))  # înregistrarea e opțională: butonul REC e dezactivat fără ffmpeg

for _tool, _pkg in (("rtl_tcp", "rtl-sdr"), ("aplay", "alsa-utils")):
    if not shutil.which(_tool):
        MISSING_DEPS.append(f"{_tool} (apt install {_pkg})")

try:
    import ctypes
    _LIBC = ctypes.CDLL(None, use_errno=True)
except Exception:
    _LIBC = None
SDR_RATE = 1_920_000
DEC1 = 8
MPX_RATE = SDR_RATE // DEC1       # 240000
DEC2 = 5
AUDIO_RATE = MPX_RATE // DEC2     # 48000
CHUNK = 128_000                   # multiplu de 512 (USB), 40 și 80*8
DEEMPH = 50e-6                    # Europa
CFG_PATH = os.path.expanduser("~/.config/rtl_fm_gui.json")
BAND_START, BAND_END = 87.5, 108.0

RIGHT_PANEL_W = 320               # lățime fixă pentru panoul din dreapta
STATION_BTN_W = 225               # încape "Radio România CUltural FM" + padding
STATION_BTN_H = 52                # spațiu confortabil pentru 2 rânduri (frecvență + nume)
STATION_GAP_X = 8                 # 4px stânga + 4px dreapta
STATION_GAP_Y = 8                 # 4px sus + 4px jos
STATION_ACTIVE_BG = "#ececec"     # fundalul canalului curent (la fel ca la mouse-over)


# ============================================================================
#  2. DSP (numpy)
# ============================================================================
def _firwin_lp(numtaps, cutoff, fs):
    """FIR trece-jos cu fereastră Hamming și câștig 1 la 0 Hz (la fel ca scipy.signal.firwin)."""
    n = np.arange(numtaps) - (numtaps - 1) / 2
    h = np.sinc(2 * cutoff / fs * n) * np.hamming(numtaps)
    return h / h.sum()


def _fir_stream(b, x, hist):
    """FIR cu stare (ultimele len(b)-1 eșantioane de intrare), doar numpy."""
    xp = np.concatenate((hist, x))
    return np.convolve(xp, b, mode="valid"), xp[len(xp) - (len(b) - 1):]


def _onepole(x, a, z):
    """Filtru IIR de ordin 1 (de-emfază): y[n] = (1 - a) * x[n] + a * y[n-1]."""
    g, out = 1.0 - a, []
    for v in x.tolist():
        z = g * v + a * z
        out.append(z)
    return np.array(out), z


def _psd(x):
    """Spectru de putere mediat pe segmente de 4096 puncte (centrat pe frecvența de acordare)."""
    x = x - x.mean()
    n = 4096
    m = len(x) // n
    if m == 0:
        return []
    seg = x[:m * n].reshape(m, n) * np.hanning(n)
    P = (np.abs(np.fft.fftshift(np.fft.fft(seg, axis=1), axes=1)) ** 2).mean(axis=0)
    P[2046:2051] = 0.5 * (P[2044:2046].mean() + P[2051:2053].mean())   # scoate vârful DC
    return P


def channel_db(P, offset_hz, half_bw=50e3):
    """Puterea (dB) dintr-un canal de ±half_bw în jurul unui offset față de frecvența de acordare."""
    if len(P) == 0:
        return -90.0
    res = SDR_RATE / 4096
    lo = max(0, int(round((offset_hz - half_bw) / res)) + 2048)
    hi = min(len(P), int(round((offset_hz + half_bw) / res)) + 2048)
    if hi <= lo:
        return -90.0
    return 10 * math.log10(float(P[lo:hi].sum()) + 1e-20)


def _mean_power(x):
    return float(np.mean(x.real ** 2 + x.imag ** 2))


def _percentile_10(vals):
    return float(np.percentile(vals, 10))


def detect_peaks(freqs, excess, thr_db):
    """Frecvențele ale căror valori depășesc pragul și sunt maxime locale."""
    out = []
    n = len(freqs)
    for i in range(n):
        if excess[i] < thr_db:
            continue
        left = excess[i - 1] if i > 0 else -1e9
        right = excess[i + 1] if i < n - 1 else -1e9
        if excess[i] > left and excess[i] >= right:
            out.append(freqs[i])
    return out


class FmDemod:
    """Demodulator FM în bandă largă: IQ (SDR_RATE) -> MPX (MPX_RATE) -> audio mono (AUDIO_RATE).
    Filtrele se proiectează la primul reset(), ca importul să funcționeze și fără numpy."""

    def __init__(self):
        self._b1 = self._b2 = None
        self._deemph_a = math.exp(-1 / (DEEMPH * MPX_RATE))

    def reset(self):
        if self._b1 is None:
            self._b1 = _firwin_lp(65, 100e3, SDR_RATE)
            self._b2 = _firwin_lp(101, 15e3, MPX_RATE)
        self._z1 = np.zeros(len(self._b1) - 1, dtype=complex)
        self._z2 = np.zeros(len(self._b2) - 1)
        self._zde = 0.0
        self._prev = np.complex128(0)

    def discriminate(self, x):
        """Bloc IQ -> semnal MPX demodulat (folosit și de decodorul RDS)."""
        y, self._z1 = _fir_stream(self._b1, x, self._z1)
        y = y[::DEC1]
        z = np.concatenate(([self._prev], y))
        self._prev = y[-1]
        return np.angle(z[1:] * np.conj(z[:-1])) * (MPX_RATE / (2 * np.pi * 75e3))

    def audio(self, mpx):
        """MPX -> audio mono float32 de formă (N, 1), cu de-emfază și filtrare de 15 kHz."""
        d, self._zde = _onepole(mpx, self._deemph_a, self._zde)
        d, self._z2 = _fir_stream(self._b2, d, self._z2)
        return (d[::DEC2] * 0.8).clip(-1, 1).astype(np.float32).reshape(-1, 1)


# ============================================================================
#  3. RDS (necesită numpy + scipy; opțional)
# ============================================================================
OFFSETS = {"A": 0x0FC, "B": 0x198, "C": 0x168, "Cp": 0x350, "D": 0x1B4}
SYN2NAME = {v: k for k, v in OFFSETS.items()}
BLK_IDX = {"A": 0, "B": 1, "C": 2, "Cp": 2, "D": 3}

PTY_NAMES = [
    "-", "Știri", "Actualități", "Informații", "Sport", "Educație", "Dramă",
    "Cultură", "Știință", "Diverse", "Muzică pop", "Muzică rock",
    "Muzică ușoară", "Clasică ușoară", "Clasică serioasă", "Altă muzică",
    "Meteo", "Economie", "Copii", "Social", "Religie", "Call-in", "Călătorii",
    "Timp liber", "Jazz", "Country", "Muzică națională", "Oldies", "Folk",
    "Documentar", "Test alarmă", "Alarmă",
]

_EBU_HI = (
    "áàéèíìóòúùÑÇŞß¡Ĳ"
    "âäêëîïôöûüñçşğıĳ"
    "ªα©‰Ğěňőπ€£$←↑→↓"
    "º¹²³±İńűµ¿÷°¼½¾§"
    "ÁÀÉÈÍÌÓÒÚÙŘČŠŽÐĿ"
    "ÂÄÊËÎÏÔÖÛÜřčšžđŀ"
    "ÃÅÆŒŷÝÕØÞŊŔĆŚŹŦð"
    "ãåæœŵýõøþŋŕćśźŧ "
)


def rds_char(b):
    if 0x20 <= b < 0x7F:
        return chr(b)
    if b >= 0x80:
        return _EBU_HI[b - 0x80]
    return " "


def _build_crc_table():
    tab = [0] * 65536
    for v in range(65536):
        reg = 0
        for bit in range(15, -1, -1):
            b = (v >> bit) & 1
            fb = ((reg >> 9) & 1) ^ b
            reg = ((reg << 1) & 0x3FF) ^ (fb * 0x1B9)
        tab[v] = reg & 0x3FF
    return tab


CRC_TAB = _build_crc_table() if HAS_RDS_DEPS else []


class _Sampler:
    """Un ceas de simbol + sincronizare pe blocuri de 26 de biți (CRC)."""

    def __init__(self, dec):
        self.dec = dec
        self.sym_t = None
        self.prev_v = None
        self.reg = 0
        self.bitpos = 0
        self.synced = False
        self.prev_match = None
        self.blk_bits = 0
        self.idx = 0
        self.bad = 0
        self.cur = [None] * 4

    @staticmethod
    def _syndrome_name(reg):
        data = (reg >> 10) & 0xFFFF
        return SYN2NAME.get(CRC_TAB[data] ^ (reg & 0x3FF))

    def push_bit(self, bit):
        self.reg = ((self.reg << 1) | bit) & 0x3FFFFFF
        self.bitpos += 1
        if not self.synced:
            if self.bitpos < 26:
                return
            name = self._syndrome_name(self.reg)
            if name is None:
                return
            pm = self.prev_match
            if (pm is not None and self.bitpos - pm[0] == 26
                    and BLK_IDX[name] == (BLK_IDX[pm[1]] + 1) % 4):
                self.synced = True
                self.blk_bits = 0
                self.bad = 0
                self.cur = [None] * 4
                self._on_block(BLK_IDX[name], self.reg, True)
            self.prev_match = (self.bitpos, name)
            return
        self.blk_bits += 1
        if self.blk_bits < 26:
            return
        self.blk_bits = 0
        idx = (self.idx + 1) % 4
        name = self._syndrome_name(self.reg)
        valid = name is not None and BLK_IDX[name] == idx
        self.bad = 0 if valid else self.bad + 1
        self._on_block(idx, self.reg, valid)
        if self.bad >= 8:
            self.synced = False
            self.prev_match = None

    def _on_block(self, idx, reg, valid):
        self.idx = idx
        if idx == 0:
            self.cur = [None] * 4
        self.cur[idx] = (reg >> 10) & 0xFFFF if valid else None
        if idx == 3:
            self.dec._group(self.cur)


class RDSDecoder:
    """Decodor RDS: primește MPX (240 kHz, demodulat FM) și scoate PS/RT/PTY/PI."""

    FS = MPX_RATE
    BB = 12000
    SYM = 1187.5
    T = BB / SYM                   # ~10.1 eșantioane / simbol
    NB = 16
    DECAY = 0.97
    TGAIN = 0.2
    ALPHA = 0.03
    BETA = ALPHA * ALPHA / 4

    def __init__(self):
        if HAS_RDS_DEPS:
            self._lo = np.exp(-2j * np.pi * 57000 * np.arange(80) / self.FS)
            self._hA = signal.firwin(33, 8000, fs=self.FS)
            self._hB = signal.firwin(91, 2700, fs=48000)
            n = int(math.ceil(self.T))
            t = np.arange(n) / self.BB
            h = np.sin(2 * np.pi * t * self.SYM)
            self._g = (h[::-1] / np.sum(h * h)).copy()
        self._lo_cache = {}
        self.reset()

    def reset(self):
        if not HAS_RDS_DEPS:
            self.n_groups = 0
            self.pi = None
            self.pty = None
            self.ps_tmp = [None] * 4
            self.rt = [" "] * 64
            self.rt_ab = None
            self.last_group_t = 0.0
            return
        self._zA = np.zeros(len(self._hA) - 1, dtype=complex)
        self._zB = np.zeros(len(self._hB) - 1, dtype=complex)
        self._zM = np.zeros(len(self._g) - 1)
        self._pend = np.zeros(0)
        self.ph = 0.0
        self.fr = 0.0
        self.mbuf = np.zeros(0)
        self.mbase = 0
        self.tacc = np.zeros(self.NB)
        self.nblk = 0
        self.smp = [_Sampler(self), _Sampler(self)]
        self.n_groups = 0
        self.pi = None
        self.pty = None
        self.ps_tmp = [None] * 4
        self.rt = [" "] * 64
        self.rt_ab = None
        self.last_group_t = 0.0

    def feed(self, mpx):
        if not HAS_RDS_DEPS:
            return
        x = np.concatenate((self._pend, mpx))
        n = len(x) // 80 * 80
        self._pend = x[n:]
        if n == 0:
            return
        x = x[:n]
        lo = self._lo_cache.get(n)
        if lo is None:
            lo = np.tile(self._lo, n // 80)
            self._lo_cache = {n: lo}
        z = x * lo
        y, self._zA = signal.lfilter(self._hA, 1.0, z, zi=self._zA)
        y = y[::5]
        y, self._zB = signal.lfilter(self._hB, 1.0, y, zi=self._zB)
        y = y[::4]
        rms = math.sqrt(float(np.mean(y.real ** 2 + y.imag ** 2))) + 1e-12
        y = y / rms
        r = self._costas(y)
        m, self._zM = signal.lfilter(self._g, 1.0, r, zi=self._zM)
        self._timing(m)
        self._extract_bits()

    def _costas(self, y):
        yr = y.real.tolist()
        yi = y.imag.tolist()
        out = [0.0] * len(yr)
        ph, fr, a, b = self.ph, self.fr, self.ALPHA, self.BETA
        cos, sin = math.cos, math.sin
        for k in range(len(yr)):
            c = cos(ph)
            s = sin(ph)
            i_ = yr[k] * c + yi[k] * s
            q_ = yi[k] * c - yr[k] * s
            out[k] = i_
            e = i_ * q_
            if e > 1.5:
                e = 1.5
            elif e < -1.5:
                e = -1.5
            fr += b * e
            if fr > 0.05:
                fr = 0.05
            elif fr < -0.05:
                fr = -0.05
            ph += fr + a * e
        self.ph = ph % (2 * math.pi)
        self.fr = fr
        return np.array(out)

    def _timing(self, m):
        N = len(m)
        idx = self.mbase + len(self.mbuf) + np.arange(N)
        bins = (((idx / self.T) % 1.0) * self.NB).astype(int)
        w = np.bincount(bins, weights=m * m, minlength=self.NB)
        self.tacc = self.DECAY * self.tacc + w
        self.mbuf = np.concatenate((self.mbuf, m))
        self.nblk += 1
        if self.nblk < 6:
            return
        c = np.sum(self.tacc * np.exp(4j * np.pi * (np.arange(self.NB) + 0.5) / self.NB))
        phi = (np.angle(c) / (4 * np.pi)) % 0.5
        for si, sp in enumerate(self.smp):
            if sp.sym_t is None:
                k = math.ceil((self.mbase + 2) / self.T - phi - 0.5 * si)
                sp.sym_t = (k + phi + 0.5 * si) * self.T
            else:
                cur = (sp.sym_t / self.T - 0.5 * si) % 0.5
                err = ((phi - cur + 0.25) % 0.5) - 0.25
                sp.sym_t += self.TGAIN * err * self.T

    def _extract_bits(self):
        mend = self.mbase + len(self.mbuf)
        for sp in self.smp:
            if sp.sym_t is None:
                continue
            while sp.sym_t < mend - 1:
                rel = sp.sym_t - self.mbase
                i = int(rel)
                if i < 0:
                    sp.sym_t += self.T
                    continue
                f = rel - i
                v = self.mbuf[i] * (1 - f) + self.mbuf[i + 1] * f
                if sp.prev_v is not None:
                    sp.push_bit(1 if v * sp.prev_v < 0 else 0)
                sp.prev_v = v
                sp.sym_t += self.T
        starts = [sp.sym_t for sp in self.smp if sp.sym_t is not None]
        if starts:
            keep = min(int(min(starts) - self.mbase) - 1, len(self.mbuf) - 2)
            if keep > 0:
                self.mbuf = self.mbuf[keep:]
                self.mbase += keep

    @property
    def synced(self):
        return any(sp.synced for sp in self.smp)

    def _group(self, blk):
        A, B, C, D = blk
        if A is not None:
            self.pi = A
        if B is None:
            return
        self.n_groups += 1
        self.last_group_t = time.time()
        gtype = B >> 12
        ver = (B >> 11) & 1
        self.pty = (B >> 5) & 0x1F
        if ver == 1 and C is not None and self.pi is None:
            self.pi = C
        if gtype == 0:
            addr = B & 3
            if D is not None:
                pair = (D >> 8, D & 0xFF)
                self.ps_tmp[addr] = pair
        elif gtype == 2:
            ab = (B >> 4) & 1
            if self.rt_ab is not None and ab != self.rt_ab:
                self.rt = [" "] * 64
            self.rt_ab = ab
            if ver == 0:
                addr = (B & 0xF) * 4
                if C is not None:
                    self._rt_put(addr, C)
                if D is not None:
                    self._rt_put(addr + 2, D)
            else:
                if D is not None:
                    self._rt_put((B & 0xF) * 2, D)

    def _rt_put(self, pos, val):
        if pos + 1 < 64:
            self.rt[pos] = chr(val >> 8) if (val >> 8) == 0x0D else rds_char(val >> 8)
            self.rt[pos + 1] = chr(val & 0xFF) if (val & 0xFF) == 0x0D else rds_char(val & 0xFF)

    @staticmethod
    def _seg_text(segs):
        return "".join(rds_char(s[0]) + rds_char(s[1]) if s else "  " for s in segs)

    def ps_text(self):
        return self._seg_text(self.ps_tmp)

    def rt_text(self):
        s = "".join(self.rt)
        return s.split("\r")[0].strip()

    def pi_hex(self):
        return "----" if self.pi is None else "%04X" % self.pi

    def pty_name(self):
        if self.pty is None:
            return "-"
        return PTY_NAMES[self.pty]


# ============================================================================
#  4. DRIVER DVB (USB): detașare / reatașare automată, fără blacklist și fără replug
# ============================================================================
DVB_DRIVERS = ("dvb_usb_rtl28xxu",)
USB_DRIVERS_DIR = "/sys/bus/usb/drivers"
USB_DEVICES_DIR = "/sys/bus/usb/devices"
DVB_CLASS_DIR = "/sys/class/dvb"
DVB_DEV_DIR = "/dev/dvb"
WAKE_HOLD_SECS = 3.0          # cât ține deschis frontend0 după reatașare (vezi _wake_tuner)
STATE_PATH = os.path.join(tempfile.gettempdir(), f"rtl_fm_gui_{os.getuid()}.json")
_IFACE_RE = re.compile(r"^(\d+-[\d.]+):(\d+)\.(\d+)$")      # ex. 1-2:1.0

# ioctl-uri usbfs (aceleași pe care le folosește libusb_detach_kernel_driver)
USBDEVFS_IOCTL = (3 << 30) | (struct.calcsize("iiP") << 16) | (ord("U") << 8) | 18
USBDEVFS_RESET = (ord("U") << 8) | 20
USBDEVFS_DISCONNECT = (ord("U") << 8) | 22
USBDEVFS_CONNECT = (ord("U") << 8) | 23


class DeviceBusy(Exception):
    """Tunerul TV este deschis de alte programe."""

    def __init__(self, procs):
        super().__init__(", ".join(procs))
        self.procs = procs


class DvbDriverGuard:
    """Eliberează dongle-ul de driverul DVB al kernelului cât timp rulează radioul
    și îl redă înapoi la oprire. Nu cere root dacă ai acces la /dev/bus/usb/*
    (același drept de care are nevoie oricum librtlsdr)."""

    def __init__(self):
        self.detached = []        # [(ifname, devname, ifno, driver)]
        self.last_error = None
        self._rebound = []        # interfețe reatașate efectiv de noi, în apelul curent

    @staticmethod
    def _read(path):
        try:
            with open(path) as f:
                return f.read().strip()
        except OSError:
            return None

    def _bound_interfaces(self):
        out = []
        for drv in DVB_DRIVERS:
            try:
                names = os.listdir(os.path.join(USB_DRIVERS_DIR, drv))
            except OSError:
                continue
            for n in names:
                m = _IFACE_RE.match(n)
                if m:
                    out.append((n, m.group(1), int(m.group(3)), drv))
        return out

    def _devnode(self, devname):
        bus = self._read(f"{USB_DEVICES_DIR}/{devname}/busnum")
        dev = self._read(f"{USB_DEVICES_DIR}/{devname}/devnum")
        if not bus or not dev:
            raise FileNotFoundError(devname)
        return f"/dev/bus/usb/{int(bus):03d}/{int(dev):03d}"

    def _usbfs_ioctl(self, devname, ifno, code):
        fd = os.open(self._devnode(devname), os.O_RDWR)
        try:
            fcntl.ioctl(fd, USBDEVFS_IOCTL, struct.pack("iiP", ifno, code, 0))
        finally:
            os.close(fd)

    def _reset_device(self, devname):
        """Reset USB al dongle-ului (cât timp nicio interfață nu are driver): îl readuce într-o stare
        curată, ca la conectare, înainte ca driverul DVB să facă probe. Ca la `usbreset`."""
        try:
            fd = os.open(self._devnode(devname), os.O_RDWR)
        except OSError:
            return
        try:
            fcntl.ioctl(fd, USBDEVFS_RESET, 0)
            time.sleep(1.0)                    # lasă dispozitivul să se reenumere
        except OSError:
            pass
        finally:
            os.close(fd)

    def _perm_hint(self, devname):
        vid = self._read(f"{USB_DEVICES_DIR}/{devname}/idVendor")
        pid = self._read(f"{USB_DEVICES_DIR}/{devname}/idProduct")
        return (f"Nu am drepturi pe dongle-ul USB. Creează /etc/udev/rules.d/99-rtlsdr.rules cu:  "
                f'SUBSYSTEM=="usb", ATTRS{{idVendor}}=="{vid}", ATTRS{{idProduct}}=="{pid}", MODE="0666"  '
                "apoi: sudo udevadm control --reload && sudo udevadm trigger")

    def _dvb_nodes(self, devname):
        """Nodurile /dev/dvb/adapterN/* ale acestui dongle."""
        base = os.path.realpath(f"{USB_DEVICES_DIR}/{devname}")
        nodes = set()
        for e in glob.glob(os.path.join(DVB_CLASS_DIR, "dvb*")):
            p = os.path.realpath(os.path.join(e, "device"))
            m = re.match(r"dvb(\d+)\.(.+)$", os.path.basename(e))
            if m and (p == base or p.startswith(base + os.sep)):
                nodes.add(f"{DVB_DEV_DIR}/adapter{m.group(1)}/{m.group(2)}")
        return nodes

    def _wake_tuner(self, devname):
        """După ce radioul a folosit dongle-ul ca SDR, cipul Realtek (frontend0) rămâne neinițializat, iar
        tunerul Sony de pe același adaptor prinde semnal, dar nu trimite date. Deschiderea lui frontend0
        în citire-scriere îl repune în stare (ca selectarea tunerului Realtek în teleops sau pornirea Kaffeine),
        deci orice program TV găsește tunerul gata de folosit."""
        node, deadline = None, time.time() + 8.0
        while node is None and time.time() < deadline:
            node = next((n for n in sorted(self._dvb_nodes(devname))
                         if n.endswith("/frontend0") and os.path.exists(n)), None)
            if node is None:
                time.sleep(0.2)
        if node is None:
            return
        try:
            fd = os.open(node, os.O_RDWR)
        except OSError:
            return                              # ocupat sau fără drepturi: nu e grav, TV-ul merge ca înainte
        try:
            time.sleep(WAKE_HOLD_SECS)
        finally:
            os.close(fd)

    def _busy_processes(self, devname):
        """Procesele care țin deschis /dev/dvb/... al acestui dongle (cât se poate vedea)."""
        nodes = self._dvb_nodes(devname)
        if not nodes:
            return []
        procs = set()
        for fd in glob.glob("/proc/[0-9]*/fd/*"):
            try:
                if os.readlink(fd) in nodes:
                    pid = fd.split("/")[2]
                    procs.add(self._read(f"/proc/{pid}/comm") or pid)
            except OSError:
                continue
        return sorted(procs)

    def detach(self, force=False):
        """Detașează driverul DVB de pe dongle. True dacă a detașat ceva."""
        ifs = self._bound_interfaces()
        if not ifs:
            return False                       # deja liber (ex. blacklist vechi)
        if not force:
            busy = sorted({p for _, dn, _, _ in ifs for p in self._busy_processes(dn)})
            if busy:
                raise DeviceBusy(busy)
        for item in ifs:
            ifname, devname, ifno, _ = item
            try:
                self._usbfs_ioctl(devname, ifno, USBDEVFS_DISCONNECT)
            except PermissionError:
                raise RuntimeError(self._perm_hint(devname))
            except OSError as e:
                if e.errno != errno.ENODATA:   # ENODATA = nu era atașat niciun driver
                    raise RuntimeError(f"Nu pot detașa driverul DVB ({ifname}): {e}")
            self.detached.append(item)
            self._save_state()
        return True

    def _reattach_one(self, item):
        ifname, devname, ifno, drv = item
        iface_path = f"{USB_DRIVERS_DIR}/{drv}/{ifname}"

        if os.path.exists(iface_path):
            return True                        # driverul este deja atașat
        if not os.path.isdir(f"{USB_DEVICES_DIR}/{devname}"):
            return True                        # dongle-ul a fost scos între timp

        # Resetarea USB poate determina kernelul să reatașeze automat driverul.
        self._reset_device(devname)
        if os.path.exists(iface_path):
            self._rebound.append(item)
            return True

        for _ in range(15):
            try:
                self._usbfs_ioctl(devname, ifno, USBDEVFS_CONNECT)
                self._rebound.append(item)
                return True
            except OSError as e:
                self.last_error = f"Nu pot reatașa driverul TV ({ifname}): {e}"

                # Verifică din nou: driverul se poate fi atașat între timp.
                if os.path.exists(iface_path):
                    return True
                if e.errno != errno.EBUSY:
                    return False
                time.sleep(0.2)
        return False

    def reattach(self):
        """Redă dongle-ul driverului DVB. Apelat după ce rtl_tcp s-a oprit."""
        left = [it for it in self.detached if not self._reattach_one(it)]
        rebound, self._rebound = self._rebound, []
        self.detached = left
        self._save_state()
        for _, devname, _, _ in rebound:
            self._wake_tuner(devname)
        return not left

    def recover(self):
        """Dacă o rulare anterioară s-a oprit brutal, redă dongle-ul driverului DVB."""
        try:
            with open(STATE_PATH) as f:
                self.detached = [tuple(x) for x in json.load(f)]
        except (OSError, ValueError):
            return
        self.reattach()

    def _save_state(self):
        try:
            if self.detached:
                with open(STATE_PATH, "w") as f:
                    json.dump(self.detached, f)
            elif os.path.exists(STATE_PATH):
                os.remove(STATE_PATH)
        except OSError:
            pass


# ============================================================================
#  5. CLIENT rtl_tcp (înlocuiește pyrtlsdr)
# ============================================================================
def _child_setup():
    # PR_SET_PDEATHSIG: rtl_tcp primește SIGTERM dacă procesul Python moare brusc.
    # (se leagă de thread-ul care a pornit procesul => pornim din thread-ul principal)
    if _LIBC is not None:
        _LIBC.prctl(1, 15)


def _iq_from_raw(raw, chunk):
    """Octeți uint8 intercalați I/Q -> vector complex128 normalizat în [-1, 1]."""
    a = np.frombuffer(raw, dtype=np.uint8)
    x = np.empty(chunk, dtype=np.complex128)
    x.real = a[0::2]
    x.imag = a[1::2]
    x -= 127.5 + 127.5j
    x /= 127.5
    return x


class RtlTcpSdr:
    """Pornește `rtl_tcp` pe localhost și îl comandă prin protocolul lui de 5 octeți.
    Oferă aceeași interfață folosită de Engine: sample_rate, center_freq, gain,
    read_samples_async(), cancel_read_async(), close()."""

    def __init__(self):
        self._lock = threading.Lock()
        self._stop = False
        self._sock = None
        self._errf = tempfile.TemporaryFile()
        with socket.socket() as probe:
            probe.bind(("127.0.0.1", 0))
            port = probe.getsockname()[1]
        self._proc = subprocess.Popen(
            [shutil.which("rtl_tcp"), "-a", "127.0.0.1", "-p", str(port), "-s", str(SDR_RATE)],
            stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=self._errf,
            preexec_fn=_child_setup)
        try:
            self._connect(port)
        except Exception:
            self.close()
            raise

    def _rtl_error(self):
        try:
            self._errf.seek(0)
            lines = [l.strip() for l in self._errf.read().decode(errors="replace").splitlines() if l.strip()]
        except Exception:
            lines = []
        return " | ".join(lines[-2:]) or "rtl_tcp s-a oprit fără mesaj"

    def _connect(self, port):
        deadline = time.time() + 8
        while True:
            if self._proc.poll() is not None:
                raise RuntimeError(self._rtl_error())
            try:
                self._sock = socket.create_connection(("127.0.0.1", port), timeout=0.5)
                break
            except OSError:
                if time.time() > deadline:
                    raise RuntimeError("rtl_tcp nu a pornit la timp: " + self._rtl_error())
                time.sleep(0.1)
        self._sock.settimeout(2.0)
        hdr = self._recv_exact(12)                 # "RTL0" + tip tuner + nr. trepte gain
        if bytes(hdr[:4]) != b"RTL0":
            raise RuntimeError("Răspuns neașteptat de la rtl_tcp")

    def _recv_exact(self, n):
        buf = bytearray(n)
        view = memoryview(buf)
        got = 0
        while got < n:
            try:
                k = self._sock.recv_into(view[got:], n - got)
            except socket.timeout:
                if self._stop:
                    raise ConnectionError("oprit")
                continue
            if k == 0:
                raise ConnectionError("rtl_tcp s-a oprit: " + self._rtl_error())
            got += k
        return buf

    def _cmd(self, code, param):
        with self._lock:
            self._sock.sendall(struct.pack(">BI", code, int(param) & 0xFFFFFFFF))

    @property
    def sample_rate(self):
        return self._rate

    @sample_rate.setter
    def sample_rate(self, v):
        self._rate = int(v)
        self._cmd(0x02, self._rate)

    @property
    def center_freq(self):
        return self._freq

    @center_freq.setter
    def center_freq(self, hz):
        self._freq = int(round(hz))
        self._cmd(0x01, self._freq)

    @property
    def gain(self):
        return self._gain

    @gain.setter
    def gain(self, g):
        self._gain = g
        if g == "auto":
            self._cmd(0x03, 0)                     # tuner AGC
        else:
            self._cmd(0x03, 1)                     # gain manual, în zecimi de dB
            self._cmd(0x04, round(float(g) * 10))

    def read_samples_async(self, cb, chunk):
        nbytes = chunk * 2
        while not self._stop:
            try:
                raw = self._recv_exact(nbytes)
            except (OSError, ConnectionError):
                if self._stop:
                    return
                raise
            cb(_iq_from_raw(raw, chunk), None)

    def cancel_read_async(self):
        self._stop = True
        try:
            self._sock.shutdown(socket.SHUT_RDWR)
        except Exception:
            pass

    def close(self):
        self._stop = True
        if self._sock is not None:
            try:
                self._sock.close()
            except Exception:
                pass
            self._sock = None
        if self._proc.poll() is None:
            self._proc.terminate()
            try:
                self._proc.wait(3)
            except subprocess.TimeoutExpired:
                self._proc.kill()
                self._proc.wait()
        try:
            self._errf.close()
        except Exception:
            pass


# ============================================================================
#  6. AUDIO (aplay) ȘI ÎNREGISTRARE (ffmpeg)
# ============================================================================
def resolve_pipewire_device():
    """Returnează 'pipewire' dacă există în `aplay -L`, altfel None (dispozitiv implicit)."""
    aplay = shutil.which("aplay")
    if not aplay:
        return None
    try:
        out = subprocess.run([aplay, "-L"], capture_output=True, text=True, timeout=5).stdout
    except Exception:
        return None
    for line in out.splitlines():
        if line and not line[0].isspace() and line.strip() == "pipewire":
            return "pipewire"
    return None


def pcm_stereo(a, vol):
    """Audio float32 (N, 1) -> octeți PCM S16_LE stereo (același semnal pe ambele canale)."""
    pcm = (a[:, 0] * (vol * 32767)).clip(-32768, 32767).astype("<i2")
    return np.repeat(pcm, 2).tobytes()


class AplayOutput:
    """Proces `aplay` care primește PCM S16_LE stereo pe stdin."""

    def __init__(self, device=None):
        cmd = [shutil.which("aplay"), "-q", "-t", "raw", "-f", "S16_LE", "-r", str(AUDIO_RATE),
               "-c", "2", "--buffer-time=200000"]
        if device:
            cmd += ["-D", device]
        self._errf = tempfile.TemporaryFile()
        self._proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.DEVNULL,
                                      stderr=self._errf)
        try:
            fcntl.fcntl(self._proc.stdin.fileno(), 1031, 16384)     # F_SETPIPE_SZ: latență mică
        except Exception:
            pass

    @property
    def alive(self):
        return self._proc.poll() is None

    def write(self, pcm):
        self._proc.stdin.write(pcm)
        self._proc.stdin.flush()

    def last_error(self, default=""):
        """Ultima linie scrisă de aplay pe stderr (sau `default`)."""
        self._errf.seek(0)
        msg = self._errf.read().decode(errors="replace").strip().splitlines()
        return msg[-1] if msg else default

    def close(self):
        try:
            self._proc.stdin.close()
        except Exception:
            pass
        self._proc.terminate()
        try:
            self._proc.wait(2)
        except subprocess.TimeoutExpired:
            self._proc.kill()
        self._errf.close()


def default_rec_dir():
    """~/Videos/UndaSDR. Folosește dosarul Videos din XDG dacă sistemul îl are localizat altfel."""
    home = os.path.expanduser("~")
    videos = os.path.join(home, "Videos")
    try:
        with open(os.path.join(home, ".config", "user-dirs.dirs"), encoding="utf-8") as f:
            for line in f:
                m = re.match(r'XDG_VIDEOS_DIR="(.*)"', line.strip())
                if m:
                    path = m.group(1).replace("$HOME", home)
                    if os.path.normpath(path) != os.path.normpath(home):
                        videos = path
                    break
    except OSError:
        pass
    return os.path.join(videos, "UndaSDR")


def recording_path(directory, fmt, label):
    """<dosar>/<label>_<AAAA-LL-ZZ_HH-MM-SS>.<ext>; adaugă _2, _3… dacă fișierul există deja."""
    ext = Recorder.FORMATS[fmt][0]
    safe = re.sub(r'[\\/:*?"<>|\x00-\x1f]+', "_", label.strip())[:80].strip(" ._") or "FM"
    stem = f"{safe}_{time.strftime('%Y-%m-%d_%H-%M-%S')}"
    path = os.path.join(directory, f"{stem}.{ext}")
    n = 2
    while os.path.exists(path):
        path = os.path.join(directory, f"{stem}_{n}.{ext}")
        n += 1
    return path


class Recorder:
    """Înregistrare audio prin ffmpeg. Primește PCM S16_LE stereo (același flux ca aplay),
    la volum 100%, într-un fir separat: un disc lent nu poate bloca redarea."""

    FORMATS = {                 # etichetă: (extensie, argumente ffmpeg pentru codec)
        "WAV": ("wav", ["-c:a", "pcm_s16le"]),
        "FLAC": ("flac", ["-c:a", "flac"]),
        "MP3": ("mp3", ["-c:a", "libmp3lame", "-b:a", "320k"]),
        "AAC": ("m4a", ["-c:a", "aac", "-b:a", "256k"]),
    }

    def __init__(self, path, fmt):
        ffmpeg = shutil.which("ffmpeg")
        if not ffmpeg:
            raise RuntimeError("Lipsește ffmpeg (sudo apt install ffmpeg).")
        self.path = path
        self.t0 = time.time()
        self._closed = False
        self._err = None
        self._errf = tempfile.TemporaryFile()
        self._q = queue.Queue(maxsize=400)              # ~26 s de audio (blocuri de ~66 ms)
        self._proc = subprocess.Popen(
            [ffmpeg, "-hide_banner", "-loglevel", "error", "-y",
             "-f", "s16le", "-ar", str(AUDIO_RATE), "-ac", "2", "-i", "pipe:0",
             "-vn", *self.FORMATS[fmt][1], path],
            stdin=subprocess.PIPE, stdout=subprocess.DEVNULL, stderr=self._errf)
        for _ in range(8):                              # codec lipsă / cale invalidă: ffmpeg iese imediat
            if self._proc.poll() is not None:
                break
            time.sleep(0.05)
        if self._proc.poll() is not None:
            msg = self._last_error() or "ffmpeg s-a oprit"
            self._errf.close()
            try:
                if os.path.getsize(path) == 0:
                    os.remove(path)
            except OSError:
                pass
            raise RuntimeError(msg)
        self._thread = threading.Thread(target=self._writer, daemon=True)
        self._thread.start()

    def _last_error(self):
        self._errf.seek(0)
        lines = [l.strip() for l in self._errf.read().decode(errors="replace").splitlines() if l.strip()]
        return lines[-1] if lines else ""

    def _writer(self):
        try:
            while True:
                data = self._q.get()
                if data is None:
                    return
                self._proc.stdin.write(data)
        except (OSError, ValueError) as e:
            self._err = self._last_error() or str(e)

    def feed(self, pcm):
        if self._closed:
            return
        try:
            self._q.put_nowait(pcm)
        except queue.Full:
            pass                                        # disc/ffmpeg blocat: mai bine pierdem decât să oprim redarea

    @property
    def failed(self):
        """ffmpeg s-a oprit singur (disc plin, cale ștearsă etc.)."""
        return not self._closed and (self._err is not None or self._proc.poll() is not None)

    def stop(self):
        """Termină înregistrarea: scrie ce a rămas în coadă, închide ffmpeg. Returnează (cale, eroare|None)."""
        self._closed = True
        try:
            self._q.put(None, timeout=5)
        except queue.Full:
            pass
        self._thread.join(timeout=15)
        try:
            self._proc.stdin.close()
        except OSError:
            pass
        try:
            self._proc.wait(timeout=15)
        except subprocess.TimeoutExpired:
            self._proc.kill()
            self._proc.wait()
            self._err = self._err or "ffmpeg nu s-a oprit la timp"
        err = self._err
        if err is None and self._proc.returncode != 0:
            err = self._last_error() or f"ffmpeg a ieșit cu codul {self._proc.returncode}"
        if err is None and (not os.path.exists(self.path) or os.path.getsize(self.path) == 0):
            err = "fișierul înregistrat e gol"
        self._errf.close()
        return self.path, err


# ============================================================================
#  7. ENGINE (fire de execuție: citire -> demodulare -> audio, plus scanare)
# ============================================================================
class Engine:
    def __init__(self):
        self.sdr = None
        self.freq = 98.3
        self.volume = 0.7
        self.muted = False
        self.rds_enabled = False
        self.audio_device = resolve_pipewire_device()
        self.audio_enabled = True
        self.mode = "listen"
        self.error = None
        self.level_db = -90.0
        self.rds = RDSDecoder()
        self.demod = FmDemod()
        self.raw_q = queue.Queue(maxsize=30)
        self.audio_q = queue.Queue(maxsize=10)
        self.skip = 0
        self.need_reset = False
        self.reset_ack = threading.Event()
        self._scan_acc = []
        self._scan_done = threading.Event()
        self._threads = []
        self._stop = None
        self.guard = DvbDriverGuard()
        self._rec = None
        self._rec_lock = threading.Lock()
        self.rec_events = queue.Queue()          # (cale, eroare|None) când se încheie o înregistrare
        atexit.register(self.close)

    @property
    def running(self):
        return self.sdr is not None

    # --- pornire / oprire ---------------------------------------------------
    def open(self, gain="auto", force=False):
        if self.sdr is not None:
            return
        if not HAS_NUMPY:
            raise RuntimeError("Lipsește numpy (sudo apt install python3-numpy).")
        if not shutil.which("rtl_tcp"):
            raise RuntimeError("Lipsește rtl_tcp (sudo apt install rtl-sdr).")

        self.audio_device = resolve_pipewire_device()
        self.guard.detach(force=force)
        try:
            sdr = RtlTcpSdr()
            try:
                sdr.sample_rate = SDR_RATE
                sdr.center_freq = self.freq * 1e6
                sdr.gain = "auto" if gain == "auto" else float(gain)
            except Exception:
                sdr.close()
                raise
        except Exception:
            self.guard.reattach()
            raise
        self.sdr = sdr
        self._stop = threading.Event()
        self._drain()
        self.skip = 2
        self.mode = "listen"
        self.need_reset = True
        self._threads = [
            threading.Thread(target=f, args=(sdr, self._stop), daemon=True)
            for f in (self._reader, self._demod, self._audio)
        ]
        for t in self._threads:
            t.start()

    def close(self):
        self.stop_recording()
        if self.sdr is None:
            return
        self._stop.set()
        try:
            self.sdr.cancel_read_async()
        except Exception:
            pass
        for t in self._threads:
            t.join(timeout=2)
        try:
            self.sdr.close()
        except Exception:
            pass
        self.sdr = None
        if not self.guard.reattach():
            self.error = self.guard.last_error

    # --- comenzi ------------------------------------------------------------
    def set_gain(self, g):
        if self.sdr is not None:
            try:
                self.sdr.gain = "auto" if g == "auto" else float(g)
            except Exception as e:
                self.error = f"Gain: {e}"

    def tune(self, mhz, audio=None):
        if abs(mhz - self.freq) > 1e-6:
            self.stop_recording()                # post nou: se salvează înregistrarea curentă
        self.freq = mhz
        if audio is not None:
            self.audio_enabled = audio
        self.mode = "listen"
        if self.sdr is None:
            return
        try:
            self.sdr.center_freq = mhz * 1e6
        except Exception as e:
            self.error = f"Acordare: {e}"
            return
        self._drain()
        self.skip = 4
        self.reset_ack.clear()
        self.need_reset = True
        self.reset_ack.wait(0.6)

    def _drain(self):
        for q in (self.raw_q, self.audio_q):
            try:
                while True:
                    q.get_nowait()
            except queue.Empty:
                pass

    def _reset_states(self):
        self.demod.reset()
        self.rds.reset()

    # --- fire de execuție ---------------------------------------------------
    def _reader(self, sdr, ev):
        def cb(samples, ctx):
            try:
                self.raw_q.put_nowait(samples)
            except queue.Full:
                pass
        try:
            sdr.read_samples_async(cb, CHUNK)
        except Exception as e:
            if not ev.is_set():
                self.error = f"SDR: {e}"

    def _demod(self, sdr, ev):
        while not ev.is_set():
            try:
                x = self.raw_q.get(timeout=0.1)
            except queue.Empty:
                x = None
            if self.need_reset:
                self._reset_states()
                self.need_reset = False
                self.reset_ack.set()
            if x is None:
                continue
            if self.skip > 0:
                self.skip -= 1
                continue
            try:
                pw = _mean_power(x)
                self.level_db = 0.6 * self.level_db + 0.4 * 10 * math.log10(pw + 1e-12)
                if self.mode == "scan":
                    self._scan_acc.append(_psd(x))
                    if len(self._scan_acc) >= 2:
                        self._scan_done.set()
                else:
                    self._listen_block(x)
            except Exception as e:
                self.error = f"Procesare: {e}"

    def _listen_block(self, x):
        d = self.demod.discriminate(x)
        if self.rds_enabled and HAS_RDS_DEPS:
            self.rds.feed(d)
        if not self.audio_enabled:
            return
        try:
            self.audio_q.put_nowait(self.demod.audio(d))
        except queue.Full:
            pass

    def _audio(self, sdr, ev):
        if not shutil.which("aplay"):
            self.error = "Audio: lipsește aplay (sudo apt install alsa-utils)."
            return
        while not ev.is_set():
            out = None
            try:
                out = AplayOutput(self.audio_device or resolve_pipewire_device())
                while not ev.is_set():
                    if not out.alive:
                        raise RuntimeError("aplay s-a oprit")
                    try:
                        a = self.audio_q.get(timeout=0.3)
                    except queue.Empty:
                        continue
                    rec = self._rec
                    if rec is not None:
                        rec.feed(pcm_stereo(a, 1.0))       # înregistrare la volum 100%, fără volum/mute
                    vol = 0.0 if self.muted else self.volume ** 2
                    out.write(pcm_stereo(a, vol))
            except Exception as e:
                if not ev.is_set():
                    self.error = f"Audio: {out.last_error(str(e)) if out else e}"
                    ev.wait(1.5)
            finally:
                if out is not None:
                    out.close()

    # --- înregistrare -------------------------------------------------------
    @property
    def recording(self):
        return self._rec is not None

    def rec_elapsed(self):
        rec = self._rec
        return None if rec is None else time.time() - rec.t0

    def start_recording(self, path, fmt):
        """Pornește înregistrarea fluxului redat (PCM la volum 100%, neafectat de volum/mute)."""
        if self.sdr is None or self.mode != "listen":
            raise RuntimeError("Nu se redă nimic.")
        with self._rec_lock:
            if self._rec is None:
                self._rec = Recorder(path, fmt)

    def stop_recording(self):
        """Oprește și salvează înregistrarea curentă; rezultatul (cale, eroare|None) ajunge în rec_events."""
        with self._rec_lock:
            rec, self._rec = self._rec, None
        if rec is not None:
            self.rec_events.put(rec.stop())

    def check_recording(self):
        """Oprește înregistrarea dacă ffmpeg s-a oprit singur; eroarea ajunge în rec_events."""
        rec = self._rec
        if rec is not None and rec.failed:
            self.stop_recording()
    # --- scanare ------------------------------------------------------------
    def measure_window(self, center_hz, cancel=None):
        if not self.running:
            return None
        self._scan_acc = []
        self._scan_done.clear()
        self.mode = "scan"
        self.sdr.center_freq = center_hz
        self._drain()
        self.skip = 2
        deadline = time.time() + 4.0
        while not self._scan_done.is_set():
            if cancel is not None and cancel.is_set():
                return None
            if time.time() > deadline:
                return None
            self._scan_done.wait(0.05)
        if not self._scan_acc:
            return None
        return np.mean(self._scan_acc[:2], axis=0)

    def scan_band(self, thr_db, progress, cancel):
        self.stop_recording()                    # în timpul scanării nu se redă nimic
        freqs, excess = [], []
        n_win = int(math.ceil((BAND_END - BAND_START) / 1.0))
        for w in range(n_win):
            if cancel.is_set():
                return None
            first = BAND_START + w * 1.0
            centre = (first + 0.45) * 1e6
            P = self.measure_window(centre, cancel=cancel)
            if cancel.is_set():
                return None
            if P is None or len(P) == 0:
                continue
            chans = []
            for k in range(10):
                f = round(first + 0.1 * k, 1)
                if f > BAND_END + 1e-6:
                    continue
                chans.append((f, channel_db(P, f * 1e6 - centre)))
            if not chans:
                continue
            floor = _percentile_10([c[1] for c in chans])
            for f, db in chans:
                freqs.append(f)
                excess.append(db - floor)
            progress((w + 1) / n_win)
        return detect_peaks(freqs, excess, thr_db)


# ============================================================================
#  8. TEXTE INTERFAȚĂ (I18N)
# ============================================================================
I18N = {
    "ro": {
        "tuning": "Acordare & Control",
        "audio_sdr": "Audio & SDR",
        "messages": "Mesaje & Jurnal",
        "warning": "",
        "freq": "Frecvență:",
        "prev": "Precedent",
        "go": "Mergi",
        "next": "Următor",
        "start": "Start",
        "stop": "Stop",
        "mute": "Mute",
        "rds_na": "RDS (instalează python3-scipy)",
        "rec_dir": "Dosar REC",
        "dlg_rec_dir": "Alege dosarul pentru înregistrări",
        "tip_rec_dir": "Dosarul în care se salvează înregistrările audio.\nCurent: {0}\nClic pentru a-l schimba.",
        "tip_rec_fmt": "Formatul înregistrării:\nWAV – PCM 16 bit, fără compresie\nFLAC – compresie fără pierderi\nMP3 – 320 kbps\nAAC – 256 kbps (fișier .m4a)",
        "tip_rec": "Înregistrează sunetul redat în formatul ales,\ncu volum 100% (nu e afectat de volum sau mute).\nSe oprește și se salvează automat la schimbarea\npostului, Stop, eliberare TV sau închiderea ferestrei.",
        "tip_rec_stop": "Oprește înregistrarea și salvează fișierul.",
        "tip_rec_idle": "Se poate înregistra doar cât se redă radio.\nPornește radioul (Start) și alege un post.",
        "tip_rec_na": "Înregistrarea necesită dependența ffmpeg.\nInstalare: sudo apt install ffmpeg\napoi repornește programul.",
        "rec_started": "Înregistrez: {0}",
        "rec_saved": "Înregistrare salvată: {0}",
        "rec_error": "Eroare înregistrare: {0}",
        "rds": "RDS",
        "rds_off": "RDS: oprit",
        "volume": "Volum:",
        "gain": "Gain:",
        "scan": "Caută",
        "cancel": "Anulează",
        "threshold": "Prag (dB):",
        "delete": "Șterge",
        "add": "Adaugă canal",
        "clear": "Golește",
        "edit": "Redenumește",
        "language": "Limbă:",
        "tv_release": "Eliberează pentru TV",
        "listening": "Ascult.",
        "stopped_free": "Oprit (dongle-ul e liber).",
        "tv_free": "Dongle-ul e liber pentru aplicațiile TV.",
        "tv_err": "Eroare TV.",
        "missing_deps": "Nu pot porni: instalează pachetele lipsă.",
        "missing_deps_warn": "Atenție: dependențe lipsă: {}",
        "tv_busy_ask": "Tunerul TV este folosit de: {}.\nContinui? Emisiunea TV se va întrerupe.",
        "tv_busy_status": "Tunerul TV e folosit de {}. Apasă Start ca să îl preiei pentru radio.",
        "sdr_unavail_warn": "Eroare: SDR indisponibil.",
        "sdr_unavail_status": "SDR indisponibil: {}",
        "wait_scan": "Așteaptă terminarea căutării (sau apasă Anulează).",
        "invalid_freq": "Frecvență invalidă (ex: 98.3).",
        "scanning": "Caut posturi în banda FM...",
        "scan_cancelled": "Căutare anulată.",
        "scan_done": "Gata: {} posturi găsite.",
        "scan_err": "Eroare la căutare: {}",
        "rds_no_data": "RDS: fără date",
        "rds_ok": "RDS: OK",
        "rds_lost": "RDS: pierdut",
        "pi_lbl": "PI",
        "gen_lbl": "Gen",
        "stopped_hint": "Oprit (Apasă Start)",
        "err_save_cfg": "Nu pot salva configurarea: {}",
        "dlg_add_title": "Adaugă canal",
        "dlg_add_freq": "Frecvență (87.5–108.0 MHz):",
        "dlg_name_title": "Nume canal",
        "dlg_name_prompt": "Nume (opțional):",
        "dlg_edit_title": "Editează canal",
        "dlg_edit_prompt": "Nume canal:",
        "dlg_select_first": "Selectează mai întâi un canal.",
        "dlg_clear_ask": "Golești toată lista de canale?",
        # Tooltip-uri
        "tip_lang": "Schimbă limba interfeței\n(Română, English, Italiano).",
        "tip_prev": "Sare la postul memorat anterior\ndin lista de canale.",
        "tip_next": "Sare la următorul post memorat\ndin lista de canale.",
        "tip_freq_entry": "Introdu frecvența în MHz (ex: 98.3)\nși apasă Enter sau butonul Mergi.",
        "tip_go": "Acordează radioul direct pe frecvența\nscrisă în căsuță.",
        "tip_nudge_down": "Scade frecvența curentă cu 0.1 MHz\n(pas fin de acordaj).",
        "tip_nudge_up": "Crește frecvența curentă cu 0.1 MHz\n(pas fin de acordaj).",
        "tip_start": "Pornește recepția SDR și detașează\nautomat driverul DVB pentru TV.",
        "tip_stop": "Oprește recepția SDR și redă\ndongle-ul driverului TV.",
        "tip_add": "Adaugă manual un canal nou\nîn lista de posturi.",
        "tip_gain": (
            "Amplificarea (gain) tunerului SDR:\n"
            "• auto: AGC automat, bun la început\n"
            "  și la semnale variate.\n"
            "• Valori mici (0–20 dB): semnale\n  foarte puternice / antenă bună,\n"
            "  evită saturația și posturile fantomă.\n"
            "• Valori mari (30–49.6 dB): semnale\n  slabe, dar crește zgomotul de fond."
        ),
        "tip_mute": "Activează sau dezactivează rapid\nieșirea audio.",
        "tip_volume": "Reglează volumul de redare\nprin PipeWire.",
        "tip_tv_release": "Oprește radioul și reatașează\ndriverul DVB ca să poți folosi TV.",
        "tip_rds": (
            "Când este bifat, citește și afișează\n"
            "datele RDS (nume post, radiotext,\n"
            "PI, gen). Folosește python3-scipy,\n"
            "dependență opțională."
        ),
        "tip_rds_na": (
            "RDS indisponibil: lipsește dependența\n"
            "opțională python3-scipy.\n"
            "Instalare: sudo apt install python3-scipy\n"
            "apoi repornește programul."
        ),
        "tip_scan": "Scanează toată banda FM (87.5–108 MHz)\nși actualizează lista de posturi.",
        "tip_cancel": "Anulează scanarea FM aflată\nîn desfășurare.",
        "tip_threshold": (
            "Prag detectare peste zgomot (dB):\n"
            "• Recomandat: 10–12 dB pentru un\n"
            "  echilibru bun între precizie și viteză.\n"
            "• Prag mai mic (5–8 dB): prinde și\n  posturi slabe, dar crește riscul de\n"
            "  fals pozitive și durează mai mult\n"
            "  filtrarea manuală.\n"
            "• Prag mai mare (15+ dB): mai rapid\n"
            "  și mai precis pe semnale curate,\n"
            "  dar poate rata posturile slabe."
        ),
        "tip_delete": "Șterge canalul selectat\ndin listă.",
        "tip_edit": "Modifică numele canalului\nselectat.",
        "tip_clear": "Șterge toate canalele\ndin listă.",
    },
    "en": {
        "tuning": "Tuning & Control",
        "audio_sdr": "Audio & SDR",
        "messages": "Messages & Log",
        "warning": "",
        "freq": "Frequency:",
        "prev": "Previous",
        "go": "Tune",
        "next": "Next",
        "start": "Start",
        "stop": "Stop",
        "mute": "Mute",
        "rds_na": "RDS (install python3-scipy)",
        "rec_dir": "REC folder",
        "dlg_rec_dir": "Choose the recordings folder",
        "tip_rec_dir": "Folder where audio recordings are saved.\nCurrent: {0}\nClick to change it.",
        "tip_rec_fmt": "Recording format:\nWAV – 16-bit PCM, uncompressed\nFLAC – lossless compression\nMP3 – 320 kbps\nAAC – 256 kbps (.m4a file)",
        "tip_rec": "Records the played audio in the chosen format at\n100% level (not affected by volume or mute).\nStops and saves automatically when the station\nchanges, on Stop, TV release or closing the window.",
        "tip_rec_stop": "Stops recording and saves the file.",
        "tip_rec_idle": "You can only record while the radio is playing.\nStart the radio and pick a station.",
        "tip_rec_na": "Recording requires the ffmpeg dependency.\nInstall: sudo apt install ffmpeg\nthen restart the program.",
        "rec_started": "Recording: {0}",
        "rec_saved": "Recording saved: {0}",
        "rec_error": "Recording error: {0}",
        "rds": "RDS",
        "rds_off": "RDS: off",
        "volume": "Volume:",
        "gain": "Gain:",
        "scan": "Scan",
        "cancel": "Cancel",
        "threshold": "Threshold (dB):",
        "delete": "Delete",
        "add": "Add channel",
        "clear": "Clear",
        "edit": "Rename",
        "language": "Language:",
        "tv_release": "Release for TV",
        "listening": "Listening.",
        "stopped_free": "Stopped (dongle is free).",
        "tv_free": "Dongle is free for TV apps.",
        "tv_err": "TV error.",
        "missing_deps": "Cannot start: install missing packages.",
        "missing_deps_warn": "Warning: missing dependencies: {}",
        "tv_busy_ask": "TV tuner is in use by: {}.\nContinue? TV playback will be interrupted.",
        "tv_busy_status": "TV tuner is in use by {}. Press Start to take it over for radio.",
        "sdr_unavail_warn": "Error: SDR unavailable.",
        "sdr_unavail_status": "SDR unavailable: {}",
        "wait_scan": "Wait for the scan to finish (or press Cancel).",
        "invalid_freq": "Invalid frequency (e.g. 98.3).",
        "scanning": "Scanning FM band...",
        "scan_cancelled": "Scan cancelled.",
        "scan_done": "Done: {} stations found.",
        "scan_err": "Scan error: {}",
        "rds_no_data": "RDS: no data",
        "rds_ok": "RDS: OK",
        "rds_lost": "RDS: lost",
        "pi_lbl": "PI",
        "gen_lbl": "Genre",
        "stopped_hint": "Stopped (Press Start)",
        "err_save_cfg": "Cannot save configuration: {}",
        "dlg_add_title": "Add channel",
        "dlg_add_freq": "Frequency (87.5–108.0 MHz):",
        "dlg_name_title": "Channel name",
        "dlg_name_prompt": "Name (optional):",
        "dlg_edit_title": "Edit channel",
        "dlg_edit_prompt": "Channel name:",
        "dlg_select_first": "Select a channel first.",
        "dlg_clear_ask": "Clear the entire channel list?",
        # Tooltips
        "tip_lang": "Change the interface language\n(Română, English, Italiano).",
        "tip_prev": "Jump to the previous saved station\nin the channel list.",
        "tip_next": "Jump to the next saved station\nin the channel list.",
        "tip_freq_entry": "Enter frequency in MHz (e.g. 98.3)\nand press Enter or Tune.",
        "tip_go": "Tune the radio directly to the\nfrequency entered in the box.",
        "tip_nudge_down": "Decrease current frequency by 0.1 MHz\n(fine tuning step).",
        "tip_nudge_up": "Increase current frequency by 0.1 MHz\n(fine tuning step).",
        "tip_start": "Start SDR reception and automatically\ndetach the DVB TV driver.",
        "tip_stop": "Stop SDR reception and return\nthe dongle to the TV driver.",
        "tip_add": "Manually add a new channel\nto the station list.",
        "tip_gain": (
            "SDR tuner gain:\n"
            "• auto: automatic AGC, good default\n"
            "  for varying signal levels.\n"
            "• Low values (0–20 dB): strong signals\n"
            "  / good antenna, avoids overload\n"
            "  and phantom/mirror stations.\n"
            "• High values (30–49.6 dB): weak\n"
            "  signals, but raises noise floor."
        ),
        "tip_mute": "Quickly mute or unmute\naudio output.",
        "tip_volume": "Adjust playback volume\nthrough PipeWire.",
        "tip_tv_release": "Stop the radio and reattach\nthe DVB driver for TV apps.",
        "tip_rds": (
            "When checked, reads and shows\n"
            "RDS data (station name, radiotext,\n"
            "PI, genre). Uses python3-scipy,\n"
            "an optional dependency."
        ),
        "tip_rds_na": (
            "RDS unavailable: the optional\n"
            "dependency python3-scipy is missing.\n"
            "Install: sudo apt install python3-scipy\n"
            "then restart the program."
        ),
        "tip_scan": "Scan the FM band (87.5–108 MHz)\nand update the station list.",
        "tip_cancel": "Cancel the currently running\nFM scan.",
        "tip_threshold": (
            "Detection threshold above noise (dB):\n"
            "• Recommended: 10–12 dB for a good\n"
            "  balance of accuracy and speed.\n"
            "• Lower (5–8 dB): catches weaker\n"
            "  stations, but increases false\n"
            "  positives and cleanup time.\n"
            "• Higher (15+ dB): faster and\n"
            "  cleaner on strong signals, but\n"
            "  may miss weak stations."
        ),
        "tip_delete": "Delete the selected channel\nfrom the list.",
        "tip_edit": "Rename the selected\nchannel.",
        "tip_clear": "Remove all channels\nfrom the list.",
    },
    "it": {
        "tuning": "Sintonia & Controllo",
        "audio_sdr": "Audio & SDR",
        "messages": "Messaggi & Log",
        "warning": "",
        "freq": "Frequenza:",
        "prev": "Precedente",
        "go": "Vai",
        "next": "Successivo",
        "start": "Avvia",
        "stop": "Ferma",
        "mute": "Muto",
        "rds_na": "RDS (installa python3-scipy)",
        "rec_dir": "Cartella REC",
        "dlg_rec_dir": "Scegli la cartella delle registrazioni",
        "tip_rec_dir": "Cartella in cui si salvano le registrazioni audio.\nAttuale: {0}\nClic per cambiarla.",
        "tip_rec_fmt": "Formato di registrazione:\nWAV – PCM 16 bit, non compresso\nFLAC – compressione senza perdite\nMP3 – 320 kbps\nAAC – 256 kbps (file .m4a)",
        "tip_rec": "Registra l'audio riprodotto nel formato scelto,\na livello 100% (non influenzato da volume o mute).\nSi ferma e salva da solo al cambio di stazione,\nStop, rilascio TV o chiusura della finestra.",
        "tip_rec_stop": "Ferma la registrazione e salva il file.",
        "tip_rec_idle": "Si può registrare solo mentre la radio è in riproduzione.\nAvvia la radio e scegli una stazione.",
        "tip_rec_na": "La registrazione richiede la dipendenza ffmpeg.\nInstalla: sudo apt install ffmpeg\npoi riavvia il programma.",
        "rec_started": "Registro: {0}",
        "rec_saved": "Registrazione salvata: {0}",
        "rec_error": "Errore di registrazione: {0}",
        "rds": "RDS",
        "rds_off": "RDS: disattivato",
        "volume": "Volume:",
        "gain": "Gain:",
        "scan": "Cerca",
        "cancel": "Annulla",
        "threshold": "Soglia (dB):",
        "delete": "Elimina",
        "add": "Aggiungi canale",
        "clear": "Svuota",
        "edit": "Rinominare",
        "language": "Lingua:",
        "tv_release": "Libera per TV",
        "listening": "In ascolto.",
        "stopped_free": "Fermato (dongle libero).",
        "tv_free": "Il dongle è libero per le app TV.",
        "tv_err": "Errore TV.",
        "missing_deps": "Impossibile avviare: installa i pacchetti mancanti.",
        "missing_deps_warn": "Attenzione: dipendenze mancanti: {}",
        "tv_busy_ask": "Il tuner TV è in uso da: {}.\nContinuare? La riproduzione TV verrà interrotta.",
        "tv_busy_status": "Il tuner TV è in uso da {}. Premi Avvia per prenderlo per la radio.",
        "sdr_unavail_warn": "Errore: SDR non disponibile.",
        "sdr_unavail_status": "SDR non disponibile: {}",
        "wait_scan": "Attendi il termine della ricerca (o premi Annulla).",
        "invalid_freq": "Frequenza non valida (es. 98.3).",
        "scanning": "Ricerca nella banda FM...",
        "scan_cancelled": "Ricerca annullata.",
        "scan_done": "Fatto: {} stazioni trovate.",
        "scan_err": "Errore ricerca: {}",
        "rds_no_data": "RDS: nessun dato",
        "rds_ok": "RDS: OK",
        "rds_lost": "RDS: perso",
        "pi_lbl": "PI",
        "gen_lbl": "Genere",
        "stopped_hint": "Fermato (Premi Avvia)",
        "err_save_cfg": "Impossibile salvare la configurazione: {}",
        "dlg_add_title": "Aggiungi canale",
        "dlg_add_freq": "Frequenza (87.5–108.0 MHz):",
        "dlg_name_title": "Nome canale",
        "dlg_name_prompt": "Nome (opzionale):",
        "dlg_edit_title": "Modifica canale",
        "dlg_edit_prompt": "Nome canale:",
        "dlg_select_first": "Seleziona prima un canale.",
        "dlg_clear_ask": "Svuotare l'intera lista dei canali?",
        # Tooltips
        "tip_lang": "Cambia la lingua dell'interfaccia\n(Română, English, Italiano).",
        "tip_prev": "Passa alla stazione salvata precedente\nnella lista canali.",
        "tip_next": "Passa alla stazione salvata successiva\nnella lista canali.",
        "tip_freq_entry": "Inserisci la frequenza in MHz (es. 98.3)\ne premi Invio o Vai.",
        "tip_go": "Sintonizza la radio direttamente sulla\nfrequenza inserita.",
        "tip_nudge_down": "Riduce la frequenza attuale di 0.1 MHz\n(passo fine di sintonia).",
        "tip_nudge_up": "Aumenta la frequenza attuale di 0.1 MHz\n(passo fine di sintonia).",
        "tip_start": "Avvia la ricezione SDR e scollega\nautomaticamente il driver DVB TV.",
        "tip_stop": "Ferma la ricezione SDR e ricollega\nil dongle al driver TV.",
        "tip_add": "Aggiungi manualmente un nuovo canale\nalla lista.",
        "tip_gain": (
            "Guadagno (gain) del tuner SDR:\n"
            "• auto: AGC automatico, utile di base\n"
            "  con livelli di segnale variabili.\n"
            "• Valori bassi (0–20 dB): segnali\n  molto forti / buona antenna, evita\n  saturazione e stazioni fantasma.\n"
            "• Valori alti (30–49.6 dB): segnali\n  deboli, ma alza il rumore di fondo."
        ),
        "tip_mute": "Attiva o disattiva rapidamente\nl'uscita audio.",
        "tip_volume": "Regola il volume di riproduzione\ntramite PipeWire.",
        "tip_tv_release": "Ferma la radio e ricollega\nil driver DVB per le app TV.",
        "tip_rds": (
            "Se spuntato, legge e mostra i\n"
            "dati RDS (nome stazione, radiotext,\n"
            "PI, genere). Usa python3-scipy,\n"
            "dipendenza opzionale."
        ),
        "tip_rds_na": (
            "RDS non disponibile: manca la\n"
            "dipendenza opzionale python3-scipy.\n"
            "Installa: sudo apt install python3-scipy\n"
            "poi riavvia il programma."
        ),
        "tip_scan": "Scansiona la banda FM (87.5–108 MHz)\ne aggiorna la lista stazioni.",
        "tip_cancel": "Annulla la scansione FM\nin corso.",
        "tip_threshold": (
            "Soglia di rilevamento sul rumore (dB):\n"
            "• Consigliato: 10–12 dB per un buon\n"
            "  equilibrio tra precisione e velocità.\n"
            "• Più bassa (5–8 dB): rileva anche\n  stazioni deboli, ma aumenta i falsi\n"
            "  positivi e la pulizia manuale.\n"
            "• Più alta (15+ dB): più rapida e\n"
            "  precisa su segnali forti, ma può\n"
            "  perdere stazioni deboli."
        ),
        "tip_delete": "Elimina il canale selezionato\ndalla lista.",
        "tip_edit": "Rinomina il canale\nselezionato.",
        "tip_clear": "Rimuove tutti i canali\ndalla lista.",
    },
}

ICONS = {
    "prev": "⏮",
    "next": "⏭",
    "go": "▶",
    "start": "▶",
    "stop": "⏹",
    "add": "➕",
    "scan": "🗼",
    "cancel": "✖",
    "delete": "🗑",
    "edit": "✎",
    "clear": "🧹",
    "tv_release": "📺",
    "nudge_down": "−",
    "nudge_up": "+",
    "rec_dir": "📁",
}

LANG_NAMES = {
    "Română": "ro",
    "English": "en",
    "Italiano": "it",
}
CODE_TO_LANG_NAME = {v: k for k, v in LANG_NAMES.items()}


# ============================================================================
#  9. INTERFAȚĂ (Tkinter)
# ============================================================================
class ToolTip:
    def __init__(self, widget, text="", wraplength=280):
        self.widget = widget
        self.text = text
        self.wraplength = wraplength
        self.tip = None
        widget.bind("<Enter>", self._show, add="+")
        widget.bind("<Leave>", self._hide, add="+")
        widget.bind("<ButtonPress>", self._hide, add="+")

    def set_text(self, text):
        self.text = text or ""
        if self.tip is not None:
            self._hide()

    def _show(self, _event=None):
        if not self.text or self.tip is not None:
            return
        try:
            x = self.widget.winfo_rootx() + 12
            y = self.widget.winfo_rooty() + self.widget.winfo_height() + 4
            tw = tk.Toplevel(self.widget)
            tw.wm_overrideredirect(True)
            tw.wm_geometry(f"+{x}+{y}")
            lbl = tk.Label(
                tw,
                text=self.text,
                justify="left",
                wraplength=self.wraplength,
                background="#ffffe0",
                foreground="#111111",
                relief="solid",
                borderwidth=1,
                padx=6,
                pady=3,
                font=("TkDefaultFont", 8),
            )
            lbl.pack()
            self.tip = tw
        except tk.TclError:
            self.tip = None

    def _hide(self, _event=None):
        if self.tip is not None:
            try:
                self.tip.destroy()
            except tk.TclError:
                pass
            self.tip = None


class _NoDefaultButtons:
    """Butoanele OK și Cancel cu același contur: OK nu mai e butonul „implicit” (fără inelul gros)."""

    def buttonbox(self):
        box = tk.Frame(self)
        tk.Button(box, text="OK", width=10, command=self.ok).pack(side="left", padx=5, pady=5)
        tk.Button(box, text="Cancel", width=10, command=self.cancel).pack(side="left", padx=5, pady=5)
        self.bind("<Return>", self.ok)
        self.bind("<Escape>", self.cancel)
        box.pack()


try:
    class _AskString(_NoDefaultButtons, simpledialog._QueryString):
        pass

    class _AskFloat(_NoDefaultButtons, simpledialog._QueryFloat):
        pass
except AttributeError:               # Python fără clasele interne ale simpledialog: dialogul standard
    _AskString = _AskFloat = None


def ask_string(title, prompt, **kw):
    if _AskString is None:
        return simpledialog.askstring(title, prompt, **kw)
    return _AskString(title, prompt, **kw).result


def ask_float(title, prompt, **kw):
    if _AskFloat is None:
        return simpledialog.askfloat(title, prompt, **kw)
    return _AskFloat(title, prompt, **kw).result


class App:
    def __init__(self, root):
        self.root = root
        self.eng = Engine()
        self.stations = {}
        self.selected_freq = None
        self._station_buttons = {}      # freq -> (holder_frame, btn)
        self._last_cols = 0
        self._toolbar_pad = 2           # spațiu deasupra rândului Caută/…/Golește (ajustat la aliniere)
        self._align_pending = False
        self._nudge_pending = False
        self.rec_dir = default_rec_dir()
        self.ui_q = queue.Queue()
        self.scanning = False
        self.scan_cancel = threading.Event()
        self._status_key = None
        self._status_args = ()
        self._status_raw = ""
        self._alert_text = ""
        self.cfg = self._load_cfg()
        self._build_ui()
        self._apply_cfg()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

        self._check_system_status()
        self._poll()

    def _load_cfg(self):
        try:
            with open(CFG_PATH, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return {}

    def _current_window_geometry(self):
        self.root.update_idletasks()
        return {
            "width": max(1080, int(self.root.winfo_width())),
            "height": max(650, int(self.root.winfo_height())),
            "x": int(self.root.winfo_x()),
            "y": int(self.root.winfo_y()),
        }

    def _save_cfg(self):
        win = self._current_window_geometry()
        cfg = {
            "stations": [{"f": f, "n": n} for f, n in sorted(self.stations.items())],
            "freq": self.eng.freq,
            "volume": self.vol_var.get(),
            "muted": bool(self.mute_var.get()),
            "rds_enabled": bool(self.rds_var.get()) and HAS_RDS_DEPS,
            "gain": self.gain_var.get(),
            "thr": self.thr_var.get(),
            "rec_dir": self.rec_dir,
            "rec_fmt": self.rec_fmt_var.get(),
            "language": self.lang.get(),
            "window": win,
        }
        try:
            os.makedirs(os.path.dirname(CFG_PATH), exist_ok=True)
            with open(CFG_PATH, "w", encoding="utf-8") as f:
                json.dump(cfg, f, ensure_ascii=False, indent=1)
        except Exception as e:
            self._set_status_key("err_save_cfg", str(e))

    def _apply_window_cfg(self):
        win = self.cfg.get("window")
        if not isinstance(win, dict):
            return
        try:
            w = max(1080, int(win.get("width", 1240)))
            h = max(650, int(win.get("height", 820)))
            x = win.get("x")
            y = win.get("y")
            if x is not None and y is not None:
                self.root.geometry(f"{w}x{h}+{int(x)}+{int(y)}")
            else:
                self.root.geometry(f"{w}x{h}")
        except Exception:
            pass

    def _apply_cfg(self):
        c = self.cfg
        self._apply_window_cfg()
        for s in c.get("stations", []):
            self.stations[round(float(s["f"]), 2)] = s.get("n", "")
        self.eng.freq = float(c.get("freq", 98.3))
        self.selected_freq = round(self.eng.freq, 2)
        self.vol_var.set(c.get("volume", 70))
        self.mute_var.set(1 if c.get("muted") else 0)
        rds_want = 1 if c.get("rds_enabled") else 0
        self.rds_var.set(rds_want if HAS_RDS_DEPS else 0)
        self.gain_var.set(c.get("gain", "auto"))
        self.thr_var.set(c.get("thr", 10))
        if isinstance(c.get("rec_dir"), str) and c["rec_dir"].strip():
            self.rec_dir = c["rec_dir"]
        if c.get("rec_fmt") in Recorder.FORMATS:
            self.rec_fmt_var.set(c["rec_fmt"])
        lang_code = c.get("language", "ro")
        if lang_code not in self.i18n:
            lang_code = "ro"
        self.lang.set(lang_code)
        self.lang_name_var.set(CODE_TO_LANG_NAME.get(lang_code, "Română"))
        self._apply_translations(save=False)
        self._sync_rds_state(save=False)
        self._on_volume()
        self._on_mute()
        self._refresh_station_buttons(force_layout=True)

    @staticmethod
    def _btn_label(icon_key, text):
        ico = ICONS.get(icon_key, "")
        return f"{ico} {text}".strip() if ico else text

    def _tr(self, key, *args):
        lang = self.lang.get()
        tpl = self.i18n.get(lang, self.i18n["ro"]).get(key, self.i18n["ro"].get(key, key))
        if args:
            try:
                return tpl.format(*args)
            except Exception:
                return tpl
        return tpl

    def _compose_message_box(self):
        parts = []
        if self._alert_text:
            parts.append(self._alert_text)
        cur_status = self.status.get().strip()
        if cur_status and cur_status not in parts:
            parts.append(cur_status)
        self.msg_box_text.set("\n".join(parts))

    def _set_alert_text(self, text):
        self._alert_text = (text or "").strip()
        self._compose_message_box()

    def _set_status_key(self, key, *args):
        self._status_key = key
        self._status_args = args
        self._status_raw = ""
        self.status.set(self._tr(key, *args))
        self._compose_message_box()

    def _set_status_text(self, text):
        self._status_key = None
        self._status_args = ()
        self._status_raw = text
        self.status.set(text)
        self._compose_message_box()

    def _refresh_status_text(self):
        if self._status_key:
            self.status.set(self._tr(self._status_key, *self._status_args))
        elif self._status_raw:
            self.status.set(self._status_raw)
        self._compose_message_box()

    def _build_ui(self):
        r = self.root
        r.title("UndaSDR RTL-SDR")
        r.geometry("1240x820")
        r.minsize(1080, 650)

        shell = ttk.Frame(r, padding=10)
        shell.pack(fill="both", expand=True)

        # Panou lateral drept cu lățime fixă (fără chenar, delimitat prin bare orizontale)
        right = ttk.Frame(shell, width=RIGHT_PANEL_W)
        right.pack(side="right", fill="y", padx=(10, 0))
        right.pack_propagate(False)
        right.bind("<Configure>", self._schedule_nudge_layout)

        # Zona principală din stânga
        m = ttk.Frame(shell)
        m.pack(side="left", fill="both", expand=True)

        self.i18n = I18N
        self.lang = tk.StringVar(value=self.cfg.get("language", "ro"))
        self.lang_name_var = tk.StringVar(value=CODE_TO_LANG_NAME.get(self.lang.get(), "Română"))
        self.i18n_widgets = []          # (widget, key, icon_key_or_None)
        self.i18n_tips = []             # (ToolTip, tip_key)

        def add_tip(widget, tip_key):
            tt = ToolTip(widget, self._tr(tip_key))
            self.i18n_tips.append((tt, tip_key))
            return tt

        def label(parent, key, **kwargs):
            w = ttk.Label(parent, text=self._tr(key), **kwargs)
            self.i18n_widgets.append((w, key, None))
            return w

        def button(parent, key, command, icon_key=None, tip_key=None, **kwargs):
            txt = self._btn_label(icon_key or key, self._tr(key))
            w = ttk.Button(parent, text=txt, command=command, **kwargs)
            self.i18n_widgets.append((w, key, icon_key or key))
            if tip_key:
                add_tip(w, tip_key)
            return w

        self.right_frame = right

        # --- Panou dreapta: ultimul rând, mereu jos: [Dosar REC] | [format] [REC] ---
        rec_row = ttk.Frame(right)
        rec_row.pack(side="bottom", fill="x")
        ttk.Separator(right, orient="horizontal").pack(side="bottom", fill="x", pady=(6, 8))
        rec_row.columnconfigure(0, weight=1, uniform="rec_pair")
        rec_row.columnconfigure(1, weight=1, uniform="rec_pair")
        self.btn_rec_dir = button(rec_row, "rec_dir", self.choose_rec_dir, icon_key="rec_dir")
        self.btn_rec_dir.grid(row=0, column=0, sticky="ew", padx=(0, 3))
        self._tip_rec_dir = ToolTip(self.btn_rec_dir, "")
        fmt_box = ttk.Frame(rec_row)
        fmt_box.grid(row=0, column=1, sticky="ew", padx=(3, 0))
        self.rec_fmt_var = tk.StringVar(value="FLAC")
        self.rec_fmt_box = ttk.Combobox(fmt_box, textvariable=self.rec_fmt_var, state="readonly",
                                        values=tuple(Recorder.FORMATS), width=5)
        self.rec_fmt_box.bind("<<ComboboxSelected>>", lambda e: self._save_cfg())
        self._tip_rec_fmt = ToolTip(self.rec_fmt_box, "")
        self.btn_rec = ttk.Button(fmt_box, text="● REC", width=8, command=self.toggle_rec, state="disabled")
        self.btn_rec.pack(side="right", padx=(4, 0))          # întâi REC: la lățime mică se strânge selectorul
        self.rec_fmt_box.pack(side="left", fill="x", expand=True)
        self._tip_rec = ToolTip(self.btn_rec, "")

        # --- Panou dreapta: 1) Limbă pe același rând ---
        langrow = ttk.Frame(right)
        langrow.pack(fill="x", pady=(2, 8))
        label(langrow, "language").pack(side="left")
        self.lang_box = ttk.Combobox(
            langrow,
            textvariable=self.lang_name_var,
            values=tuple(LANG_NAMES.keys()),
            state="readonly",
            width=12,
        )
        self.lang_box.pack(side="right")
        self.lang_box.bind("<<ComboboxSelected>>", lambda e: self._change_language())
        add_tip(self.lang_box, "tip_lang")

        ttk.Separator(right, orient="horizontal").pack(fill="x", pady=(0, 8))

        # --- Panou dreapta: 2) Acordare & control (fără chenar, perechi simetrice) ---
        tune_box = ttk.Frame(right)
        tune_box.pack(fill="x", pady=(0, 6))
        sec_tune = label(tune_box, "tuning", font=("TkDefaultFont", 9, "bold"), anchor="center")
        sec_tune.pack(fill="x", pady=(0, 6))

        step_row = ttk.Frame(tune_box)
        step_row.pack(fill="x", pady=(0, 6))
        self._step_row = step_row
        step_row.bind("<Configure>", self._schedule_row_align)
        step_row.columnconfigure(0, weight=1, uniform="step_pair")
        step_row.columnconfigure(1, weight=1, uniform="step_pair")
        button(step_row, "prev", lambda: self.step_station(-1), icon_key="prev", tip_key="tip_prev").grid(
            row=0, column=0, sticky="ew", padx=(0, 3)
        )
        button(step_row, "next", lambda: self.step_station(1), icon_key="next", tip_key="tip_next").grid(
            row=0, column=1, sticky="ew", padx=(3, 0)
        )

        # Frecvență -> [- + poziționate cu offset față de mijlocul imaginar al panoului și al spațiului dintre butoane] -> [căsuță] [MHz] [Mergi]
        go_row = ttk.Frame(tune_box)
        go_row.pack(fill="x", pady=(0, 6))
        self._go_row = go_row
        go_row.bind("<Configure>", self._schedule_nudge_layout)
        self._freq_lbl = label(go_row, "freq")
        self._freq_lbl.pack(side="left")

        nudge_slot = tk.Frame(go_row, height=32)
        nudge_slot.pack(side="left", fill="x", expand=True, padx=(4, 4))
        nudge_slot.pack_propagate(False)
        self._nudge_slot = nudge_slot

        b_down = ttk.Button(nudge_slot, text=ICONS["nudge_down"], width=2, command=lambda: self.nudge(-0.1))
        add_tip(b_down, "tip_nudge_down")
        b_up = ttk.Button(nudge_slot, text=ICONS["nudge_up"], width=2, command=lambda: self.nudge(0.1))
        add_tip(b_up, "tip_nudge_up")
        self._btn_nudge_down = b_down
        self._btn_nudge_up = b_up

        btn_go = button(go_row, "go", self.go_entry, icon_key="go", tip_key="tip_go", width=7)
        btn_go.pack(side="right")
        self._btn_go = btn_go
        self._mhz_lbl = ttk.Label(go_row, text="MHz")
        self._mhz_lbl.pack(side="right", padx=(0, 4))
        self.ent = ttk.Entry(go_row, width=6, justify="center")
        self.ent.pack(side="right", padx=(0, 4))
        self.ent.bind("<Return>", lambda e: self.go_entry())
        add_tip(self.ent, "tip_freq_entry")

        pwr_row = ttk.Frame(tune_box)
        pwr_row.pack(fill="x")
        pwr_row.columnconfigure(0, weight=1, uniform="pwr_pair")
        pwr_row.columnconfigure(1, weight=1, uniform="pwr_pair")
        self.btn_power = button(pwr_row, "start", self.toggle_power, icon_key="start", tip_key="tip_start")
        self.btn_power.grid(row=0, column=0, sticky="ew", padx=(0, 3))
        button(pwr_row, "add", self.add_station, icon_key="add", tip_key="tip_add").grid(
            row=0, column=1, sticky="ew", padx=(3, 0)
        )

        ttk.Separator(right, orient="horizontal").pack(fill="x", pady=(4, 8))

        # --- Panou dreapta: 3) Audio & SDR (fără selector de ieșire, fixat pe PipeWire) ---
        audio_box = ttk.Frame(right)
        audio_box.pack(fill="x", pady=(0, 6))
        sec_audio = label(audio_box, "audio_sdr", font=("TkDefaultFont", 9, "bold"), anchor="center")
        sec_audio.pack(fill="x", pady=(0, 6))

        gainrow = ttk.Frame(audio_box)
        gainrow.pack(fill="x", pady=(0, 8))
        label(gainrow, "gain").pack(side="left")
        self.gain_var = tk.StringVar(value="auto")
        g = ttk.Combobox(gainrow, textvariable=self.gain_var, width=8, state="readonly",
                         values=["auto", "0", "10", "20", "30", "40", "49.6"])
        g.pack(side="right")
        g.bind("<<ComboboxSelected>>", lambda e: self.eng.set_gain(self.gain_var.get()))
        add_tip(g, "tip_gain")

        muterow = ttk.Frame(audio_box)
        muterow.pack(fill="x", pady=(0, 2))
        self.mute_var = tk.IntVar(value=0)
        self.mute_btn = ttk.Checkbutton(muterow, text=self._tr("mute"),
                                        variable=self.mute_var, command=self._on_mute)
        self.mute_btn.pack(side="left")
        self.i18n_widgets.append((self.mute_btn, "mute", None))
        add_tip(self.mute_btn, "tip_mute")
        self.lbl_vol_pct = ttk.Label(muterow, text="70%")
        self.lbl_vol_pct.pack(side="right")

        volrow = ttk.Frame(audio_box)
        volrow.pack(fill="x", pady=(0, 8))
        label(volrow, "volume").pack(side="left", padx=(0, 6))
        self.vol_var = tk.DoubleVar(value=70)
        sc = ttk.Scale(volrow, from_=0, to=100, variable=self.vol_var,
                       command=lambda v: self._on_volume())
        sc.pack(side="left", fill="x", expand=True)
        add_tip(sc, "tip_volume")

        button(audio_box, "tv_release", self.release_for_tv,
               icon_key="tv_release", tip_key="tip_tv_release").pack(fill="x")

        ttk.Separator(right, orient="horizontal").pack(fill="x", pady=(4, 8))

        # --- Panou dreapta: 4) Zonă frecvență / RDS / nume + casetă separată mesaje ---
        status_box = ttk.Frame(right)
        status_box.pack(fill="both", expand=True)

        status_hdr = ttk.Frame(status_box)
        status_hdr.pack(fill="x", pady=(0, 2))
        self.rds_var = tk.IntVar(value=0)
        self.rds_btn = ttk.Checkbutton(
            status_hdr,
            text=self._tr("rds" if HAS_RDS_DEPS else "rds_na"),
            variable=self.rds_var,
            command=lambda: self._sync_rds_state(save=True),
        )
        self.rds_btn.pack(side="left")
        self.i18n_widgets.append((self.rds_btn, "rds" if HAS_RDS_DEPS else "rds_na", None))
        add_tip(self.rds_btn, "tip_rds" if HAS_RDS_DEPS else "tip_rds_na")

        self.lbl_freq = ttk.Label(status_box, text="--.- MHz", font=("TkDefaultFont", 18, "bold"),
                                  anchor="center", justify="center")
        self.lbl_freq.pack(fill="x")

        self.lbl_ps = ttk.Label(status_box, text="", font=("TkDefaultFont", 12, "bold"),
                                wraplength=RIGHT_PANEL_W - 16, anchor="center", justify="center")
        self.lbl_ps.pack(fill="x", pady=(1, 0))

        self.lbl_rt = ttk.Label(status_box, text="", font=("TkDefaultFont", 9, "italic"),
                                wraplength=RIGHT_PANEL_W - 16, anchor="center", justify="center")
        self.lbl_rt.pack(fill="x", pady=(1, 1))

        self.lbl_info = ttk.Label(status_box, text="", font=("TkDefaultFont", 8),
                                  wraplength=RIGHT_PANEL_W - 16, anchor="center", justify="center")
        self.lbl_info.pack(fill="x", pady=(0, 4))

        # Casetă separată pentru mesaje de stare, erori și avertismente (folosește spațiul rezervat)
        self.msg_frame = ttk.LabelFrame(status_box, text=self._tr("messages"), padding=(6, 4))
        self.msg_frame.pack(fill="both", expand=True, pady=(2, 0))
        self.i18n_widgets.append((self.msg_frame, "messages", None))

        self.status = tk.StringVar(value="")
        self.msg_box_text = tk.StringVar(value="")
        self.lbl_msg_box = ttk.Label(
            self.msg_frame,
            textvariable=self.msg_box_text,
            wraplength=RIGHT_PANEL_W - 28,
            anchor="nw",
            justify="left",
            font=("TkDefaultFont", 8),
        )
        self.lbl_msg_box.pack(fill="both", expand=True)

        # --- Conținut principal sus (stânga): grafic frecvențe ridicat + rând aliniat + listă ---
        scale_row = ttk.Frame(m)
        scale_row.pack(fill="x", pady=(0, 2))
        self.tune_canvas = tk.Canvas(scale_row, height=60, highlightthickness=0)
        self.tune_canvas.pack(fill="x", expand=True)
        self.tune_canvas.bind("<Configure>", self._draw_frequency_scale)
        self.tune_canvas.bind("<Button-1>", self._scale_click)
        self.tune_canvas.bind("<B1-Motion>", self._scale_click)

        row = ttk.Frame(m)
        row.pack(fill="x", pady=(self._toolbar_pad, 6))
        self._toolbar_row = row
        row.bind("<Configure>", self._schedule_row_align)
        self.btn_scan = button(row, "scan", self.start_scan, icon_key="scan", tip_key="tip_scan")
        self.btn_scan.pack(side="left")
        self.btn_cancel = button(row, "cancel", self.scan_cancel.set,
                                 icon_key="cancel", tip_key="tip_cancel", state="disabled")
        self.btn_cancel.pack(side="left", padx=4)
        label(row, "threshold").pack(side="left", padx=(10, 0))
        self.thr_var = tk.IntVar(value=10)
        sp_thr = ttk.Spinbox(row, from_=3, to=30, width=4, textvariable=self.thr_var)
        sp_thr.pack(side="left", padx=2)
        add_tip(sp_thr, "tip_threshold")
        button(row, "clear", self.clear_stations, icon_key="clear", tip_key="tip_clear").pack(
            side="right", padx=2
        )
        button(row, "edit", self.edit_station, icon_key="edit", tip_key="tip_edit").pack(
            side="right", padx=2
        )
        button(row, "delete", self.delete_station, icon_key="delete", tip_key="tip_delete").pack(
            side="right", padx=2
        )

        # Zonă de butoane cu dimensiune fixă și reflow automat la redimensionare
        fr = ttk.Frame(m)
        fr.pack(fill="both", expand=True)
        bg = ttk.Style(r).lookup("TFrame", "background") or r.cget("bg")
        self.stations_canvas = tk.Canvas(fr, highlightthickness=0, bg=bg)
        self.stations_sb = ttk.Scrollbar(fr, orient="vertical", command=self.stations_canvas.yview)
        self.stations_canvas.configure(yscrollcommand=self.stations_sb.set)
        self.stations_sb.pack(side="right", fill="y")
        self.stations_canvas.pack(side="left", fill="both", expand=True)

        self.stations_inner = ttk.Frame(self.stations_canvas)
        self._stations_win = self.stations_canvas.create_window(
            (0, 0), window=self.stations_inner, anchor="nw"
        )
        self.stations_inner.bind("<Configure>", self._on_stations_inner_configure)
        self.stations_canvas.bind("<Configure>", self._on_stations_canvas_configure)
        self.stations_canvas.bind_all("<MouseWheel>", self._on_mousewheel, add="+")
        self.stations_canvas.bind_all("<Button-4>", self._on_mousewheel, add="+")
        self.stations_canvas.bind_all("<Button-5>", self._on_mousewheel, add="+")

        self.prog = ttk.Progressbar(m, maximum=1.0)
        self._schedule_nudge_layout()
        self._schedule_row_align()

    def _schedule_nudge_layout(self, _event=None):
        if not self._nudge_pending:
            self._nudge_pending = True
            self.root.after_idle(self._layout_nudge_buttons)

    def _layout_nudge_buttons(self):
        """Poziționează butoanele - și + cu offset raportat la mijlocul imaginar al panoului
        din dreapta și al spațiului dintre butoane, fără tăiere pe verticală."""
        self._nudge_pending = False
        self.root.update_idletasks()
        slot = self._nudge_slot
        btn_w = max(22, self._btn_nudge_down.winfo_reqwidth())
        btn_h = max(24, self._btn_nudge_down.winfo_reqheight())

        min_slot_h = btn_h + 6
        if int(slot.cget("height")) < min_slot_h:
            slot.configure(height=min_slot_h)

        slot_w = slot.winfo_width()
        slot_h = max(slot.winfo_height(), min_slot_h)
        if slot_w <= 4:
            slot_w = max(48, RIGHT_PANEL_W // 4)

        panel_w = max(self.right_frame.winfo_width(), RIGHT_PANEL_W)
        panel_mid_x = panel_w / 2.0
        slot_root_x = slot.winfo_rootx() - self.right_frame.winfo_rootx()
        local_panel_mid = max(6.0, min(slot_w - 6.0, panel_mid_x - slot_root_x))

        gap = max(2, int(round(slot_w * 0.05)))
        center_offset = (btn_w + gap) * 0.35
        mid_x = local_panel_mid + center_offset
        y = max(1, (slot_h - btn_h) // 2)

        x_minus = max(0, min(slot_w - btn_w * 2 - gap, int(round(mid_x - gap / 2.0 - btn_w))))
        x_plus = min(slot_w - btn_w, x_minus + btn_w + gap)

        self._btn_nudge_down.place(x=x_minus, y=y, width=btn_w, height=btn_h)
        self._btn_nudge_up.place(x=x_plus, y=y, width=btn_w, height=btn_h)

    def _schedule_row_align(self, _event=None):
        if not self._align_pending:
            self._align_pending = True
            self.root.after_idle(self._align_toolbar_row)

    def _align_toolbar_row(self):
        """Rândul Caută/…/Golește (stânga) continuă rândul Precedent/Următor (dreapta): același nivel."""
        self._align_pending = False
        self.root.update_idletasks()
        dy = self._step_row.winfo_rooty() - self._toolbar_row.winfo_rooty()
        new = max(0, self._toolbar_pad + dy)
        if new != self._toolbar_pad:
            self._toolbar_pad = new
            self._toolbar_row.pack_configure(pady=(new, 6))
            self.root.after_idle(self._align_toolbar_row)

    def _on_stations_inner_configure(self, _event=None):
        self.stations_canvas.configure(scrollregion=self.stations_canvas.bbox("all"))

    def _on_stations_canvas_configure(self, event):
        cols = self._calc_cols(event.width)
        if cols != self._last_cols:
            self._layout_station_buttons(cols)

    @staticmethod
    def _calc_cols(width):
        cell_w = STATION_BTN_W + STATION_GAP_X
        return max(1, (max(1, width) - STATION_GAP_X) // cell_w)

    def _on_mousewheel(self, event):
        try:
            bbox = self.stations_canvas.bbox("all")
            if not bbox:
                return
            if bbox[3] - bbox[1] <= self.stations_canvas.winfo_height():
                return
            if event.num == 4 or (getattr(event, "delta", 0) > 0):
                self.stations_canvas.yview_scroll(-2, "units")
            elif event.num == 5 or (getattr(event, "delta", 0) < 0):
                self.stations_canvas.yview_scroll(2, "units")
        except tk.TclError:
            pass

    @staticmethod
    def _fmt_freq(f):
        return f"{f:.1f}" if abs(f * 10 - round(f * 10)) < 1e-6 else f"{f:.2f}"

    def _station_btn_text(self, f, n):
        f_str = f"{self._fmt_freq(f)} MHz"
        label_name = n.strip() if n else "-"
        return f"{label_name}\n{f_str}"

    def _refresh_station_buttons(self, force_layout=False):
        for w in self.stations_inner.winfo_children():
            w.destroy()
        self._station_buttons.clear()

        for f, n in sorted(self.stations.items()):
            holder = tk.Frame(
                self.stations_inner,
                width=STATION_BTN_W,
                height=STATION_BTN_H,
            )
            holder.pack_propagate(False)
            btn = tk.Button(
                holder,
                text=self._station_btn_text(f, n),
                justify="center",
                anchor="center",
                relief="groove",
                bd=2,
                command=lambda freq=f: self._on_station_button_click(freq),
            )
            btn.pack(fill="both", expand=True)
            btn.bind("<Button-3>", lambda e, freq=f: self._on_station_right_click(freq))
            self._station_buttons[f] = (holder, btn)

        avail_w = self.stations_canvas.winfo_width() or (self.root.winfo_width() - RIGHT_PANEL_W - 50) or 840
        cols = self._calc_cols(avail_w)
        if force_layout or cols != self._last_cols:
            self._layout_station_buttons(cols)
        else:
            self._layout_station_buttons(self._last_cols or cols)
        self._highlight_active_station()

    def _layout_station_buttons(self, cols):
        self._last_cols = max(1, cols)
        sorted_items = sorted(self._station_buttons.items())
        for idx, (_f, (holder, _btn)) in enumerate(sorted_items):
            r_idx, c_idx = divmod(idx, self._last_cols)
            holder.grid(
                row=r_idx,
                column=c_idx,
                padx=(STATION_GAP_X // 2, STATION_GAP_X // 2),
                pady=(STATION_GAP_Y // 2, STATION_GAP_Y // 2),
                sticky="nw",
            )
        self.stations_inner.update_idletasks()
        total_w = self._last_cols * (STATION_BTN_W + STATION_GAP_X)
        total_rows = max(1, (len(sorted_items) + self._last_cols - 1) // self._last_cols)
        total_h = total_rows * (STATION_BTN_H + STATION_GAP_Y)
        self.stations_canvas.itemconfigure(self._stations_win, width=total_w, height=total_h)
        self.stations_canvas.configure(scrollregion=(0, 0, total_w, total_h))

    def _highlight_active_station(self):
        cur = round(self.eng.freq, 2)
        default_bg = self.root.cget("bg")
        for f, (_holder, btn) in self._station_buttons.items():
            is_cur = abs(f - cur) < 0.015
            is_sel = self.selected_freq is not None and abs(f - self.selected_freq) < 0.015
            if is_cur:
                btn.configure(relief="sunken", bg=STATION_ACTIVE_BG, font=("TkDefaultFont", 9, "bold"))
            elif is_sel:
                btn.configure(relief="raised", bg="#e6e6e6", font=("TkDefaultFont", 9, "bold"))
            else:
                btn.configure(relief="groove", bg=default_bg, font=("TkDefaultFont", 9, "normal"))

    def _on_station_button_click(self, freq):
        self.selected_freq = round(freq, 2)
        self._highlight_active_station()
        self.tune(freq)

    def _on_station_right_click(self, freq):
        self.selected_freq = round(freq, 2)
        self._highlight_active_station()
        self.edit_station()

    def release_for_tv(self):
        """Oprește radioul (dacă rulează) și redă dongle-ul driverului TV."""
        if self.scanning:
            return
        if self.eng.running:
            self.toggle_power()
        else:
            self.eng.guard.reattach()
        if not self.eng.guard.detached:
            self._set_status_key("tv_free")
        else:
            self._set_status_text(self.eng.guard.last_error or self._tr("tv_err"))

    def _sync_power_button(self):
        if self.eng.running:
            self.btn_power.configure(text=self._btn_label("stop", self._tr("stop")))
        else:
            self.btn_power.configure(text=self._btn_label("start", self._tr("start")))

    def _apply_translations(self, save=True):
        for widget, key, icon_key in self.i18n_widgets:
            raw = self._tr(key)
            txt = self._btn_label(icon_key, raw) if icon_key else raw
            try:
                widget.configure(text=txt)
            except tk.TclError:
                pass
        for tt, tip_key in self.i18n_tips:
            tt.set_text(self._tr(tip_key))
        self._sync_power_button()
        self._refresh_rec_ui()
        if MISSING_DEPS:
            self._set_alert_text(self._tr("missing_deps_warn", " | ".join(MISSING_DEPS)))
        self._refresh_status_text()
        self._schedule_nudge_layout()
        self._schedule_row_align()
        if save:
            self._save_cfg()

    def _change_language(self):
        code = LANG_NAMES.get(self.lang_name_var.get(), "ro")
        self.lang.set(code)
        self._apply_translations(save=True)

    def _draw_frequency_scale(self, _event=None):
        """Grafic de frecvențe scalabil, ridicat mai sus împreună cu cifrele și indicator scurt."""
        c = self.tune_canvas
        c.delete("all")
        width = max(c.winfo_width(), 2)
        h = max(c.winfo_height(), 46)
        pad_x = max(10, min(20, int(round(width * 0.015))))
        left, right = pad_x, max(pad_x + 2, width - pad_x)

        top_lbl_y = max(1, int(round(h * 0.02)))
        y = max(18, int(round(h * 0.40)))
        num_y = min(h - 2, y + max(11, int(round(h * 0.22))))

        c.create_line(left, y, right, y)
        px_per_mhz = (right - left) / (BAND_END - BAND_START)
        step = 0.1 if px_per_mhz >= 8 else (0.2 if px_per_mhz >= 4 else 0.5)
        count = int(round((BAND_END - BAND_START) / step))
        for i in range(count + 1):
            f = BAND_START + i * step
            x = left + (f - BAND_START) * px_per_mhz
            major = abs(f - round(f)) < 0.001
            mid = not major and abs(f * 2 - round(f * 2)) < 0.001
            tick = 13 if major else (8 if mid else 4)
            c.create_line(x, y - tick / 2, x, y + tick / 2)
            if major:
                c.create_text(x, num_y, text=f"{f:.0f}", anchor="n", font=("TkDefaultFont", 8))

        f = max(BAND_START, min(BAND_END, self.eng.freq))
        x = left + (f - BAND_START) * px_per_mhz
        ind_top = max(top_lbl_y + 9, y - 9)
        ind_bot = min(num_y - 2, y + 5)
        c.create_line(x, ind_top, x, ind_bot, width=2)
        c.create_text(x, top_lbl_y, text=f"{f:.1f} MHz", anchor="n", font=("TkDefaultFont", 8, "bold"))

    def _scale_click(self, event):
        width = self.tune_canvas.winfo_width()
        pad_x = max(10, min(20, int(round(width * 0.015))))
        left, right = pad_x, width - pad_x
        if right <= left:
            return
        f = BAND_START + (event.x - left) / (right - left) * (BAND_END - BAND_START)
        self.tune(round(max(BAND_START, min(BAND_END, f)), 1))

    def _target_freq_for_action(self):
        if self.selected_freq is not None and self.selected_freq in self.stations:
            return self.selected_freq
        cur = round(self.eng.freq, 2)
        if cur in self.stations:
            return cur
        return None

    def add_station(self):
        if self.scanning:
            return
        freq = ask_float(self._tr("dlg_add_title"), self._tr("dlg_add_freq"),
                         initialvalue=self.eng.freq, minvalue=BAND_START,
                         maxvalue=BAND_END, parent=self.root)
        if freq is None:
            return
        freq = round(freq, 1)
        key = round(freq, 2)
        name = ask_string(self._tr("dlg_name_title"), self._tr("dlg_name_prompt"),
                          initialvalue=self.stations.get(key, ""),
                          parent=self.root)
        if name is None:
            return
        self.stations[key] = name.strip()
        self.selected_freq = key
        self._refresh_station_buttons()
        self._save_cfg()

    def edit_station(self):
        key = self._target_freq_for_action()
        if key is None:
            messagebox.showinfo(self.root.title(), self._tr("dlg_select_first"), parent=self.root)
            return
        name = ask_string(self._tr("dlg_edit_title"), self._tr("dlg_edit_prompt"),
                          initialvalue=self.stations.get(key, ""), parent=self.root)
        if name is not None:
            self.stations[key] = name.strip()
            self._refresh_station_buttons()
            self._save_cfg()

    def clear_stations(self):
        if self.scanning:
            return
        if self.stations and messagebox.askyesno(self.root.title(), self._tr("dlg_clear_ask"), parent=self.root):
            self.stations.clear()
            self.selected_freq = None
            self._refresh_station_buttons()
            self._save_cfg()

    def delete_station(self):
        key = self._target_freq_for_action()
        if key is not None and not self.scanning:
            self.stations.pop(key, None)
            if self.selected_freq == key:
                self.selected_freq = None
            self._refresh_station_buttons()
            self._save_cfg()

    def step_station(self, d):
        fs = sorted(self.stations)
        if not fs:
            return
        cur = self.eng.freq
        if d > 0:
            nxt = next((f for f in fs if f > cur + 0.01), fs[0])
        else:
            nxt = next((f for f in reversed(fs) if f < cur - 0.01), fs[-1])
        self.selected_freq = round(nxt, 2)
        self.tune(nxt)

    def _check_system_status(self):
        if MISSING_DEPS:
            self._set_alert_text(self._tr("missing_deps_warn", " | ".join(MISSING_DEPS)))
            self._set_status_key("missing_deps")
            self.btn_power.config(state="disabled")
            self.btn_scan.config(state="disabled")
        else:
            self._set_alert_text("")
            self.eng.guard.recover()
            self.start_radio()

    def start_radio(self, user=False, force=False):
        if MISSING_DEPS:
            return
        try:
            self.eng.open(self.gain_var.get(), force=force)
            self._sync_power_button()
            self._set_status_key("listening")
            self._set_alert_text("")
        except DeviceBusy as e:
            self._sync_power_button()
            who = ", ".join(e.procs)
            if user and messagebox.askyesno(
                    self.root.title(),
                    self._tr("tv_busy_ask", who),
                    parent=self.root):
                self.start_radio(user=True, force=True)
            else:
                self._set_status_key("tv_busy_status", who)
        except Exception as e:
            self._sync_power_button()
            self._set_alert_text(self._tr("sdr_unavail_warn"))
            self._set_status_key("sdr_unavail_status", str(e)[:300])

    def toggle_power(self):
        if self.scanning:
            return
        if self.eng.running:
            self.eng.close()
            self._sync_power_button()
            self._set_status_key("stopped_free")
        else:
            self.start_radio(user=True)

    def tune(self, f):
        if self.scanning:
            self._set_status_key("wait_scan")
            return
        f = max(64.0, min(110.0, round(f, 2)))
        self.selected_freq = f
        if not self.eng.running and not MISSING_DEPS:
            self.eng.freq = f
            self.start_radio(user=True)
        self.eng.audio_enabled = True
        self.eng.tune(f)
        self._highlight_active_station()
        self._save_cfg()

    def nudge(self, d):
        self.tune(self.eng.freq + d)

    def go_entry(self):
        try:
            self.tune(float(self.ent.get().replace(",", ".")))
        except ValueError:
            self._set_status_key("invalid_freq")

    def _on_volume(self):
        val = float(self.vol_var.get())
        self.eng.volume = val / 100.0
        self.lbl_vol_pct.config(text=f"{round(val)}%")

    def _on_mute(self):
        self.eng.muted = bool(self.mute_var.get())

    def _sync_rds_state(self, save=True):
        if not HAS_RDS_DEPS:
            self.rds_var.set(0)
            self.rds_btn.state(["disabled"])
            self.eng.rds_enabled = False
            self.eng.rds.reset()
        else:
            self.rds_btn.state(["!disabled"])
            enabled = bool(self.rds_var.get())
            self.eng.rds_enabled = enabled
            if not enabled:
                self.eng.rds.reset()
        if save:
            self._save_cfg()

    # --- înregistrare -------------------------------------------------------
    def choose_rec_dir(self):
        start = self.rec_dir
        while start and not os.path.isdir(start):
            start = os.path.dirname(start)
        d = filedialog.askdirectory(initialdir=start or os.path.expanduser("~"),
                                    title=self._tr("dlg_rec_dir"), parent=self.root)
        if d:
            self.rec_dir = d
            self._save_cfg()
            self._refresh_rec_ui()

    def toggle_rec(self):
        if self.eng.recording:
            self.eng.stop_recording()
            self._drain_rec_events()
            self._refresh_rec_ui()
            return
        if not (HAS_FFMPEG and self.eng.running and not self.scanning):
            return
        freq = self.eng.freq
        name = self.stations.get(round(freq, 2), "").strip()
        label = f"{name or 'FM'}_{self._fmt_freq(freq)}MHz"
        fmt = self.rec_fmt_var.get()
        try:
            os.makedirs(self.rec_dir, exist_ok=True)
            path = recording_path(self.rec_dir, fmt, label)
            self.eng.start_recording(path, fmt)
        except Exception as e:
            self._set_status_key("rec_error", str(e)[:300])
            return
        self._set_status_key("rec_started", os.path.basename(path))
        self._refresh_rec_ui()

    def _drain_rec_events(self):
        try:
            while True:
                path, err = self.eng.rec_events.get_nowait()
                if err:
                    self._set_status_key("rec_error", err)
                else:
                    self._set_status_key("rec_saved", os.path.basename(path))
        except queue.Empty:
            pass

    @staticmethod
    def _set_tip(tip, text):
        if tip.text != text:                      # set_text ascunde tooltip-ul afișat: doar la schimbare
            tip.set_text(text)

    def _refresh_rec_ui(self):
        """Starea butonului REC (activ doar cât se redă, cu ffmpeg instalat) și textele din tooltip-uri."""
        elapsed = self.eng.rec_elapsed()
        can = HAS_FFMPEG and self.eng.running and not self.scanning
        if elapsed is not None:
            secs = int(elapsed)
            text, state = f"■ {secs // 60:02d}:{secs % 60:02d}", "normal"
            tip = self._tr("tip_rec_stop")
        else:
            text, state = "● REC", ("normal" if can else "disabled")
            tip = self._tr("tip_rec" if can else ("tip_rec_idle" if HAS_FFMPEG else "tip_rec_na"))
        if str(self.btn_rec.cget("text")) != text:
            self.btn_rec.configure(text=text)
        if str(self.btn_rec.cget("state")) != state:
            self.btn_rec.configure(state=state)
        self._set_tip(self._tip_rec, tip)
        self._set_tip(self._tip_rec_dir, self._tr("tip_rec_dir", self.rec_dir))
        self._set_tip(self._tip_rec_fmt, self._tr("tip_rec_fmt"))

    def start_scan(self):
        if self.scanning or MISSING_DEPS:
            return
        if not self.eng.running:
            self.start_radio(user=True)
            if not self.eng.running:
                return
        self.eng.stop_recording()
        self.scanning = True
        self.prog.pack(fill="x", pady=(8, 0))
        self.prog["value"] = 0
        self.scan_cancel.clear()
        self.btn_scan.config(state="disabled")
        self.btn_cancel.config(state="normal")
        threading.Thread(target=self._scan_thread, args=(int(self.thr_var.get()),), daemon=True).start()

    def _scan_thread(self, thr):
        e = self.eng
        q = self.ui_q
        prev_freq = e.freq
        try:
            q.put(("status_key", ("scanning", ())))
            found = e.scan_band(thr, lambda p: q.put(("progress", p)), self.scan_cancel)
            if found is None:
                q.put(("status_key", ("scan_cancelled", ())))
                return
            old = dict(self.stations)
            new_stations = {round(f, 2): old.get(round(f, 2), "") for f in found}
            q.put(("set_stations", new_stations))
            q.put(("status_key", ("scan_done", (len(found),))))
        except Exception as ex:
            q.put(("status_key", ("scan_err", (str(ex),))))
        finally:
            e.mode = "listen"
            try:
                e.audio_enabled = True
                if e.running:
                    e.tune(prev_freq)
            except Exception:
                pass
            q.put(("scan_done", None))

    def _poll(self):
        try:
            while True:
                kind, val = self.ui_q.get_nowait()
                if kind == "status_key":
                    k, args = val
                    self._set_status_key(k, *args)
                elif kind == "status":
                    self._set_status_text(val)
                elif kind == "progress":
                    self.prog["value"] = val
                elif kind == "set_stations":
                    self.stations = val
                    self._refresh_station_buttons()
                    self._save_cfg()
                elif kind == "scan_done":
                    self.scanning = False
                    self.btn_scan.config(state="normal")
                    self.btn_cancel.config(state="disabled")
                    self.prog["value"] = 0
                    self.prog.pack_forget()
                    self._highlight_active_station()
                    self._save_cfg()
        except queue.Empty:
            pass

        e = self.eng
        if e.error:
            self._set_status_text(e.error)
            e.error = None
        e.check_recording()
        self._drain_rec_events()
        self._refresh_rec_ui()

        self.lbl_freq.config(text=f"{e.freq:.1f} MHz")
        self._draw_frequency_scale()
        self._highlight_active_station()
        try:
            has_focus = self.root.focus_get() is self.ent
        except Exception:
            has_focus = False
        if not has_focus:
            self.ent.delete(0, "end")
            self.ent.insert(0, f"{e.freq:.1f}")

        known = self.stations.get(round(e.freq, 2), "")
        if e.running:
            if self.eng.rds_enabled and HAS_RDS_DEPS:
                r = e.rds
                ps = r.ps_text().strip()
                self.lbl_ps.config(text=ps or known)
                self.lbl_rt.config(text=r.rt_text())
                if r.n_groups == 0:
                    rds_state = self._tr("rds_no_data")
                elif time.time() - r.last_group_t < 3:
                    rds_state = self._tr("rds_ok")
                else:
                    rds_state = self._tr("rds_lost")
                self.lbl_info.config(
                    text=f"{rds_state}   {self._tr('pi_lbl')}: {r.pi_hex()}   {self._tr('gen_lbl')}: {r.pty_name()}"
                )
            else:
                self.lbl_ps.config(text=known)
                self.lbl_rt.config(text="")
                self.lbl_info.config(text=self._tr("rds_off"))
        else:
            self.lbl_ps.config(text=known)
            self.lbl_rt.config(text="")
            if not MISSING_DEPS:
                self.lbl_info.config(text=self._tr("stopped_hint"))

        self.root.after(200, self._poll)

    def on_close(self):
        self.scan_cancel.set()
        self._save_cfg()
        self.eng.close()
        self.root.destroy()


# ============================================================================
#  10. MAIN
# ============================================================================
def main():
    root = tk.Tk()
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
