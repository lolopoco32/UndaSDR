#!/usr/bin/env python3
"""
Radio FM cu RTL-SDR (Realtek DVB-T / Astrometa) - GUI simplu.

Funcții: căutare automată de posturi, listă memorată (butoane), nume + text RDS,
mute, volum, ieșire audio PipeWire, start/stop, plus mod Aviație / Radioamatori
cu două grafice scalabile, marcaje cu HOLD, decodare mesaje și panou carduri.

Fără blacklist și fără reconectare USB: la Start, programul detașează singur
driverul kernel DVB (dvb_usb_rtl28xxu) de pe dongle prin usbfs, iar la Stop /
la ieșire îl reatașează => tunerul TV apare din nou în aplicațiile TV.

Dependențe (doar din apt, nimic din pip):
    sudo apt install rtl-sdr alsa-utils python3-tk python3-numpy     # necesare
    sudo apt install python3-scipy                                   # opțional (doar RDS)
    sudo apt install ffmpeg                                          # opțional (doar înregistrarea)
  - rtl_tcp (din rtl-sdr) citește dongle-ul; programul vorbește cu el pe localhost
  - aplay (din alsa-utils) redă sunetul
  - python3-numpy: demodulare FM/AM/NFM, filtrare, scanare și decodare pachete
  - python3-scipy: doar decodarea RDS; fără el radioul merge normal, iar caseta
    RDS rămâne dezactivată
  - pw-dump (din pipewire-bin, vine odată cu PipeWire): doar lista dispozitivelor pentru selectorul
    de ieșire audio; nu trebuie instalat nimic în plus. Fără el rămâne ieșirea implicită
  - ffmpeg: doar înregistrarea audio (WAV/FLAC/MP3/AAC); fără el butonul REC
    rămâne dezactivat

Rulare:
    python3 undasdr-v3.py
"""
import atexit
from collections import deque
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
import traceback
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
CFG_PATH = os.path.expanduser("~/.config/UndaSDR/config.json")
OLD_CFG_PATH = os.path.expanduser("~/.config/rtl_fm_gui.json")     # locul vechi: citit o dată, dacă cel nou nu există încă
BAND_START, BAND_END = 87.5, 108.0

AIR_BAND_START, AIR_BAND_END = 118.0, 137.0
AIR_STEP_MHZ = 0.025
HAM_VHF_START, HAM_VHF_END = 144.0, 146.0
HAM_UHF_START, HAM_UHF_END = 430.0, 440.0
HAM_STEP_MHZ = 0.0125
HF_DIRECT_BELOW_HZ = 24.0e6                 # sub această frecvență R820T are nevoie de „direct sampling”
LISTEN_MODES = ("am", "nfm", "usb", "lsb")  # moduri cu squelch și nivel de canal (FM broadcast nu are)

# Benzile din modul SDR: id, nume (ro, en, it), start MHz, stop MHz, pas MHz, mod, frecvență implicită MHz.
# Mod: "am" | "nfm" | "fm" (WFM) | "usb" | "lsb". „air” are graficul lui; restul folosesc graficul generic.
BANDS = [
    ("mw",     ("AM comercial (MW)", "AM broadcast (MW)", "AM commerciale (MW)"), 0.531, 1.602, 0.009, "am", 0.909),
    ("ham160", ("Radioamatori 160 m", "Amateur 160 m", "Radioamatori 160 m"), 1.810, 2.000, 0.001, "lsb", 1.850),
    ("ham80",  ("Radioamatori 80 m", "Amateur 80 m", "Radioamatori 80 m"), 3.500, 3.800, 0.001, "lsb", 3.700),
    ("sw49",   ("Unde scurte 49 m", "Shortwave 49 m", "Onde corte 49 m"), 5.900, 6.200, 0.005, "am", 6.000),
    ("ham40",  ("Radioamatori 40 m", "Amateur 40 m", "Radioamatori 40 m"), 7.000, 7.200, 0.001, "lsb", 7.100),
    ("sw41",   ("Unde scurte 41 m", "Shortwave 41 m", "Onde corte 41 m"), 7.200, 7.450, 0.005, "am", 7.300),
    ("sw31",   ("Unde scurte 31 m", "Shortwave 31 m", "Onde corte 31 m"), 9.400, 9.900, 0.005, "am", 9.600),
    ("ham30",  ("Radioamatori 30 m", "Amateur 30 m", "Radioamatori 30 m"), 10.100, 10.150, 0.001, "usb", 10.120),
    ("sw25",   ("Unde scurte 25 m", "Shortwave 25 m", "Onde corte 25 m"), 11.600, 12.100, 0.005, "am", 11.800),
    ("ham20",  ("Radioamatori 20 m", "Amateur 20 m", "Radioamatori 20 m"), 14.000, 14.350, 0.001, "usb", 14.200),
    ("sw19",   ("Unde scurte 19 m", "Shortwave 19 m", "Onde corte 19 m"), 15.100, 15.800, 0.005, "am", 15.400),
    ("sw16",   ("Unde scurte 16 m", "Shortwave 16 m", "Onde corte 16 m"), 17.480, 17.900, 0.005, "am", 17.700),
    ("ham17",  ("Radioamatori 17 m", "Amateur 17 m", "Radioamatori 17 m"), 18.068, 18.168, 0.001, "usb", 18.130),
    ("ham15",  ("Radioamatori 15 m", "Amateur 15 m", "Radioamatori 15 m"), 21.000, 21.450, 0.001, "usb", 21.300),
    ("sw13",   ("Unde scurte 13 m", "Shortwave 13 m", "Onde corte 13 m"), 21.450, 21.850, 0.005, "am", 21.600),
    ("ham12",  ("Radioamatori 12 m", "Amateur 12 m", "Radioamatori 12 m"), 24.890, 24.990, 0.001, "usb", 24.950),
    ("sw11",   ("Unde scurte 11 m", "Shortwave 11 m", "Onde corte 11 m"), 25.670, 26.100, 0.005, "am", 25.800),
    ("cb",     ("CB 11 m", "CB 11 m", "CB 11 m"), 26.965, 27.405, 0.010, "am", 27.185),
    ("ham10",  ("Radioamatori 10 m", "Amateur 10 m", "Radioamatori 10 m"), 28.000, 29.700, 0.005, "usb", 28.500),
    ("ham6",   ("Radioamatori 6 m", "Amateur 6 m", "Radioamatori 6 m"), 50.000, 52.000, 0.0125, "nfm", 51.500),
    ("fmbc",   ("Radio FM", "FM broadcast", "Radio FM"), 87.5, 108.0, 0.1, "fm", 100.0),
    ("air",    ("Aviație AM", "Aviation AM", "Aviazione AM"), AIR_BAND_START, AIR_BAND_END, AIR_STEP_MHZ, "am", 118.275),
    ("vhf",    ("Radioamatori 2 m", "Amateur 2 m", "Radioamatori 2 m"), HAM_VHF_START, HAM_VHF_END, HAM_STEP_MHZ, "nfm", 145.500),
    ("marine", ("Marină VHF", "Marine VHF", "Marina VHF"), 156.0, 162.6, 0.025, "nfm", 156.800),
    ("uhf",    ("Radioamatori 70 cm", "Amateur 70 cm", "Radioamatori 70 cm"), HAM_UHF_START, HAM_UHF_END, HAM_STEP_MHZ, "nfm", 433.500),
    ("pmr",    ("PMR446", "PMR446", "PMR446"), 446.0, 446.2, 0.0125, "nfm", 446.100),
    ("srd",    ("SRD 868", "SRD 868", "SRD 868"), 863.0, 870.0, 0.025, "nfm", 868.300),
    ("ham23",  ("Radioamatori 23 cm", "Amateur 23 cm", "Radioamatori 23 cm"), 1240.0, 1300.0, 0.0125, "nfm", 1296.500),
]
BAND_BY_ID = {b[0]: b for b in BANDS}
_LANG_IDX = {"ro": 0, "en": 1, "it": 2}


def band_name(bid, lang):
    return BAND_BY_ID[bid][1][_LANG_IDX.get(lang, 0)]


# Pas fin (MHz) pentru butoanele − / + și filtrul recomandat (kHz, lățime totală), pe fiecare bandă.
# Pasul fin e mai mic decât pasul de canal: servește la centrarea exactă pe semnal.
BAND_FINE = {"mw": 0.001, "sw49": 0.001, "sw41": 0.001, "sw31": 0.001, "sw25": 0.001, "sw19": 0.001, "sw16": 0.001,
             "sw13": 0.001, "sw11": 0.001, "cb": 0.001, "air": 0.001,
             "ham160": 0.0001, "ham80": 0.0001, "ham40": 0.0001, "ham30": 0.0001, "ham20": 0.0001, "ham17": 0.0001,
             "ham15": 0.0001, "ham12": 0.0001, "ham10": 0.0001,
             "ham6": 0.0025, "vhf": 0.0025, "marine": 0.0025, "uhf": 0.0025, "pmr": 0.0025, "ham23": 0.0025,
             "srd": 0.005, "fmbc": 0.01}
BAND_BW = {"mw": 9.0, "sw49": 8.0, "sw41": 8.0, "sw31": 8.0, "sw25": 8.0, "sw19": 8.0, "sw16": 8.0, "sw13": 8.0,
           "sw11": 8.0, "cb": 10.0, "air": 10.0,
           "ham160": 2.7, "ham80": 2.7, "ham40": 2.7, "ham30": 2.4, "ham20": 2.7, "ham17": 2.7, "ham15": 2.7,
           "ham12": 2.7, "ham10": 2.7,
           "ham6": 16.0, "vhf": 16.0, "marine": 16.0, "uhf": 16.0, "pmr": 12.5, "ham23": 16.0, "srd": 25.0,
           "fmbc": 200.0}


def band_fine_step(bid):
    return BAND_FINE.get(bid, BAND_BY_ID[bid][4])


def band_rec_bw(bid):
    return BAND_BW.get(bid, BW_DEFAULT[bw_key(BAND_BY_ID[bid][5])])


def band_label(bid, lang):
    b = BAND_BY_ID[bid]
    return f"{band_name(bid, lang)} ({b[2]:g}–{b[3]:g})"


# Ce poate recepționa fiecare tuner (tipul vine în antetul rtl_tcp): intervale în MHz.
TUNER_NAMES = {1: "E4000", 2: "FC0012", 3: "FC0013", 4: "FC2580", 5: "R820T/R820T2", 6: "R828D"}
_TUNER_VHF = {1: [(52.0, 1100.0), (1250.0, 2200.0)], 2: [(22.0, 948.0)], 3: [(22.0, 1100.0)],
              4: [(146.0, 308.0), (438.0, 924.0)], 5: [(24.0, 1766.0)], 6: [(24.0, 1766.0)]}
_HF_RANGE = [(0.5, 24.0)]


def detect_hf_mode(tuner_type, log_text, override="auto"):
    """Cum recepționează dongle-ul HF (sub 24 MHz): "native" = RTL-SDR Blog V4 (upconverter), "direct" = RTL-SDR Blog V3
    (direct sampling), None = deloc. R820T / R828D obișnuite (și Astrometa) NU au HF. Se deduce din ce raportează rtl_tcp;
    `override` din configurare ("direct" / "native" / "off") are prioritate."""
    if override in ("direct", "native"):
        return override
    if override == "off":
        return None
    t = (log_text or "").lower()
    if "blog v4" in t or "rtl-sdr blog v4" in t:
        return "native"
    if "blog v3" in t or "rtl-sdr blog v3" in t:
        return "direct" if tuner_type == 5 else None
    return None


def parse_device_label(log_text):
    m = re.search(r"Using device \d+:\s*(.+)", log_text or "")
    return m.group(1).strip() if m else ""


def tuner_supported_ranges(tuner_type, hf_mode=None):
    """Intervalele (MHz) pe care dongle-ul le poate recepționa; HF doar dacă `hf_mode` e "direct" sau "native"."""
    merged = []
    for a, b in sorted((_HF_RANGE if hf_mode in ("direct", "native") else []) + _TUNER_VHF.get(tuner_type, _TUNER_VHF[5])):
        if merged and a <= merged[-1][1] + 1e-9:
            merged[-1] = (merged[-1][0], max(merged[-1][1], b))
        else:
            merged.append((a, b))
    return merged


def unsupported_parts(lo, hi, ranges):
    """Părțile din [lo, hi] care NU sunt acoperite de niciun interval din `ranges`."""
    parts, cur = [], lo
    for a, b in sorted(ranges):
        if b <= cur:
            continue
        if a > cur:
            parts.append((cur, min(a, hi)))
        cur = max(cur, b)
        if cur >= hi:
            break
    if cur < hi:
        parts.append((cur, hi))
    return [(a, b) for a, b in parts if b - a > 1e-9]

MARKER_TTL_SECS = 14.0
MARKER_MAX_HITS = 6

# Cascadă (waterfall): rezoluția = mărimea FFT (lățimea unui bin = SDR_RATE / FFT), viteza = rânduri / secundă
WF_RES = {"7.5 kHz": 256, "3.75 kHz": 512, "1.88 kHz": 1024, "0.94 kHz": 2048,
          "0.47 kHz": 4096, "0.23 kHz": 8192, "0.12 kHz": 16384}
WF_SPEEDS = {"0.5/s": 0.5, "1/s": 1.0, "2/s": 2.0, "3/s": 3.0, "5/s": 5.0, "8/s": 8.0,
             "10/s": 10.0, "12/s": 12.0, "15/s": 15.0, "30/s": 30.0}
WF_BLOCK_RATE = 15.0              # blocuri IQ pe secundă (CHUNK / SDR_RATE); peste asta, un bloc dă mai multe rânduri
WF_SENS = {("%+d dB" % v if v else "0 dB"): float(v) for v in range(-12, 13, 2)}   # + = mai multe culori
WF_ZOOM = {"×1": 1, "×2": 2, "×4": 4, "×8": 8, "×16": 16, "×32": 32, "×64": 64}   # decupare în jurul frecvenței acordate
WF_DEFAULT_RES, WF_DEFAULT_SPEED, WF_DEFAULT_SENS = "1.88 kHz", "10/s", "0 dB"
WF_EDGE = 0.10                    # fracțiunea tăiată la fiecare margine (acolo filtrul dongle-ului scade)
WF_RANGE_DB = 40.0                # dB între fundal (gri) și culoarea maximă
WF_MAX_ROWS = 600                 # istoricul păstrat (rânduri)

AUTO_SQL_MARGIN = 4.0             # dB peste zgomotul de fond la care se deschide squelch-ul automat
AUTO_SQL_SETTLE = 6               # blocuri ignorate după acordare (nivelul se stabilizează)
AUTO_SQL_WARM = 8                 # blocuri folosite la măsurarea inițială a zgomotului

RIGHT_PANEL_W = 320               # lățime fixă pentru panoul din dreapta
STATION_BTN_W = 225               # încape "Radio România CUltural FM" + padding
STATION_BTN_H = 52                # spațiu confortabil pentru 2 rânduri (frecvență + nume)
STATION_GAP_X = 8                 # 4px stânga + 4px dreapta
STATION_GAP_Y = 8                 # 4px sus + 4px jos
STATION_ACTIVE_BG = "#ececec"     # fundalul canalului curent (la fel ca la mouse-over)
SCALE_AXIS_Y = 30                 # poziția axei în canvasul scalei
SCALE_H = 58                      # înălțimea canvasului scalei (axă + cifre)
TOOLBAR_MIN_GAP = 6               # spațiu minim între cifrele scalei și rândul de butoane de sub ea
RIGHT_GAP = 4                     # spațiu vertical uniform între rândurile panoului din dreapta

_MSG_LANG = "ro"                  # limba curentă pentru mesajele din straturile de jos (driver, rtl_tcp, audio...)


def set_msg_lang(code):
    global _MSG_LANG
    _MSG_LANG = code


def _L(key, *args):
    """Mesaj localizat (din I18N) pentru erorile generate în afara interfeței."""
    tbl = I18N.get(_MSG_LANG) or I18N["ro"]
    tpl = tbl.get(key) or I18N["ro"].get(key, key)
    try:
        return tpl.format(*args) if args else tpl
    except Exception:
        return tpl


# ============================================================================
#  2. DSP (numpy) ȘI DECODOR MESAJE AFSK / AX.25
# ============================================================================
def _firwin_lp(numtaps, cutoff, fs):
    """FIR trece-jos cu fereastră Hamming și câștig 1 la 0 Hz (la fel ca scipy.signal.firwin)."""
    n = np.arange(numtaps) - (numtaps - 1) / 2
    h = np.sinc(2 * cutoff / fs * n) * np.hamming(numtaps)
    return h / h.sum()


def _fir_stream(b, x, hist):
    """FIR cu stare (ultimele len(b)-1 eșantioane de intrare), doar numpy.
    Pentru semnal complex convoluția se face separat pe parte reală și imaginară (mai rapid, același rezultat)."""
    xp = np.concatenate((hist, x))
    if np.iscomplexobj(xp):
        y = np.convolve(xp.real, b, mode="valid") + 1j * np.convolve(xp.imag, b, mode="valid")
    else:
        y = np.convolve(xp, b, mode="valid")
    return y, xp[len(xp) - (len(b) - 1):]


def _psd(x):
    """Spectru de putere mediat pe segmente de 4096 puncte (centrat pe frecvența de acordare)."""
    x = x - x.mean()
    n = 4096
    m = len(x) // n
    if m == 0:
        return []
    seg = x[:m * n].reshape(m, n) * np.hanning(n)
    P = (np.abs(np.fft.fftshift(np.fft.fft(seg, axis=1), axes=1)) ** 2).mean(axis=0)
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


def _fir_stream_cx(b, x, hist):
    """Ca _fir_stream, dar cu coeficienți complecși (filtrul de bandă laterală). 4 convoluții reale."""
    xp = np.concatenate((hist, x))
    xr, xi, br, bi = xp.real, xp.imag, b.real, b.imag
    cv = lambda p, q: np.convolve(p, q, mode="valid")
    y = (cv(xr, br) - cv(xi, bi)) + 1j * (cv(xr, bi) + cv(xi, br))
    return y, xp[len(xp) - (len(b) - 1):]


# Lățimea benzii de recepție (kHz, lățime TOTALĂ) pe moduri: presetări, limite și valori implicite.
BW_PRESETS = {
    "fm": [("WFM 250", 250.0), ("WFM 220", 220.0), ("WFM 200", 200.0), ("WFM 180", 180.0), ("WFM 150", 150.0),
           ("WFM 120", 120.0), ("WFM 100", 100.0)],
    "am": [("AM 4", 4.0), ("AM 5", 5.0), ("AM 6", 6.0), ("AM 8", 8.0), ("AM 9", 9.0), ("AM 10", 10.0), ("AM 12", 12.0),
           ("AM 15", 15.0), ("AM 20", 20.0), ("AM 25", 25.0)],
    "nfm": [("NFM 5", 5.0), ("NFM 6.25", 6.25), ("NFM 8", 8.0), ("NFM 10", 10.0), ("NFM 12.5", 12.5), ("NFM 15", 15.0),
            ("NFM 16", 16.0), ("NFM 20", 20.0), ("NFM 25", 25.0), ("NFM 30", 30.0), ("NFM 40", 40.0),
            ("NFM 60", 60.0), ("NFM 80", 80.0)],
    "ssb": [("SSB 1.8", 1.8), ("SSB 2.1", 2.1), ("SSB 2.4", 2.4), ("SSB 2.7", 2.7), ("SSB 3.0", 3.0), ("SSB 3.6", 3.6),
            ("SSB 4.5", 4.5)],
}
BW_RANGE = {"fm": (60.0, 250.0), "am": (2.0, 40.0), "nfm": (4.0, 100.0), "ssb": (1.0, 6.0)}
BW_DEFAULT = {"fm": 200.0, "am": 20.0, "nfm": 25.0, "ssb": 2.7}
GAIN_VALUES = ["0", "5", "10", "15", "20", "25", "30", "35", "40", "45", "49.6"]     # dB; „auto” = butonul Gain


def bw_key(mode):
    """USB și LSB folosesc aceeași lățime de filtru."""
    return "ssb" if mode in ("usb", "lsb") else mode


CH_TAPS = 201                     # filtrul de canal (la MPX_RATE): tranziție ~4 kHz


class FmDemod:
    """Demodulator FM în bandă largă: IQ (SDR_RATE) -> MPX (MPX_RATE) -> audio mono (AUDIO_RATE).
    Filtrele se proiectează la primul reset(), ca importul să funcționeze și fără numpy."""

    def __init__(self):
        self._b1 = self._b2 = self._bde = None
        self.bw_hz = BW_DEFAULT["fm"] * 1e3
        self._bw_dirty = False
        self._deemph_a = math.exp(-1 / (DEEMPH * MPX_RATE))

    def reset(self):
        if self._b1 is None:
            self._b1 = _firwin_lp(65, self.bw_hz / 2.0, SDR_RATE)
            self._b2 = _firwin_lp(101, 15e3, MPX_RATE)
            # de-emfaza = filtru IIR de ordin 1; aproximat cu un FIR scurt (a^k), deci doar numpy, fără buclă Python
            a = self._deemph_a
            self._bde = (1.0 - a) * a ** np.arange(96)
        self._z1 = np.zeros(len(self._b1) - 1, dtype=complex)
        self._z2 = np.zeros(len(self._b2) - 1)
        self._zde = np.zeros(len(self._bde) - 1)
        self._prev = np.complex128(0)

    def set_bw(self, bw_hz):
        """Se aplică la următorul bloc, de către firul de demodulare (un singur scriitor pe filtre)."""
        self.bw_hz = float(bw_hz)
        self._bw_dirty = True

    def discriminate(self, x):
        """Bloc IQ -> semnal MPX demodulat (folosit și de decodorul RDS)."""
        if self._bw_dirty:
            self._bw_dirty = False
            self._b1 = _firwin_lp(65, self.bw_hz / 2.0, SDR_RATE)
        y, self._z1 = _fir_stream(self._b1, x, self._z1)
        y = y[::DEC1]
        z = np.concatenate(([self._prev], y))
        self._prev = y[-1]
        return np.angle(z[1:] * np.conj(z[:-1])) * (MPX_RATE / (2 * np.pi * 75e3))

    def audio(self, mpx):
        """MPX -> audio mono float32 de formă (N, 1), cu de-emfază și filtrare de 15 kHz."""
        d, self._zde = _fir_stream(self._bde, mpx, self._zde)
        d, self._z2 = _fir_stream(self._b2, d, self._z2)
        return (d[::DEC2] * 0.8).clip(-1, 1).astype(np.float32).reshape(-1, 1)


class SsbDemod:
    """USB / LSB: anti-alias -> decimare la 48 kHz -> filtru complex de bandă laterală (trece [0, bw] deasupra sau
    dedesubtul purtătoarei) -> partea reală = sunetul -> AGC lent. Purtătoarea (dial-ul) = frecvența acordată.
    Filtrul de bandă laterală lucrează la 48 kHz: acolo 201 de coeficienți dau o tranziție de ~0,8 kHz (la 240 kHz ar fi
    ~3,9 kHz, mai lată decât banda SSB, deci banda laterală opusă nu s-ar mai respinge)."""

    def __init__(self):
        self._b_rf = self._b_pre = self._taps = None
        self.bw_hz = BW_DEFAULT["ssb"] * 1e3
        self._bw_dirty = False
        self._upper = True
        self.reset()

    def set_bw(self, bw_hz):
        self.bw_hz = float(bw_hz)
        self._bw_dirty = True

    def _design(self, upper):
        n = np.arange(CH_TAPS) - (CH_TAPS - 1) / 2.0
        lp = _firwin_lp(CH_TAPS, self.bw_hz / 2.0, AUDIO_RATE)
        shift = np.exp(1j * np.pi * self.bw_hz * n / AUDIO_RATE * (1 if upper else -1))   # mută banda [-bw/2, bw/2] la [0, ±bw]
        return lp * shift

    def reset(self):
        if self._b_rf is None:
            self._b_rf = _firwin_lp(65, 40e3, SDR_RATE)
            self._b_pre = _firwin_lp(81, 8e3, MPX_RATE)         # anti-alias înainte de decimarea la 48 kHz
        self._z_rf = np.zeros(len(self._b_rf) - 1, dtype=complex)
        self._z_pre = np.zeros(len(self._b_pre) - 1, dtype=complex)
        self._z_ch = np.zeros(CH_TAPS - 1, dtype=complex)
        self._taps = None
        self._agc = 0.0

    def audio(self, x, upper=True, squelch_open=True):
        y, self._z_rf = _fir_stream(self._b_rf, x, self._z_rf)
        y = y[::DEC1]
        y, self._z_pre = _fir_stream(self._b_pre, y, self._z_pre)
        y = y[::DEC2]                                           # 48 kHz complex
        if self._taps is None or self._bw_dirty or upper != self._upper:
            self._taps, self._upper, self._bw_dirty = self._design(upper), upper, False
        y, self._z_ch = _fir_stream_cx(self._taps, y, self._z_ch)
        out = y.real
        if len(out) == 0:
            return out.astype(np.float32).reshape(-1, 1)
        self._agc = max(float(np.max(np.abs(out))), self._agc * 0.97)        # atac rapid, revenire lentă
        gain = min(300.0, 0.35 / max(self._agc, 1e-3))
        if not squelch_open:
            out = np.zeros_like(out)
        return np.clip(out * gain, -1.0, 1.0).astype(np.float32).reshape(-1, 1)


class AmDemod:
    """Demodulator AM pentru banda de aviație: IQ (SDR_RATE) -> filtru ~10 kHz -> anvelopă -> voce ~3 kHz."""

    def __init__(self):
        self._b_rf = None
        self._b_af = None
        self.raw = np.zeros(0)
        self.bw_hz = BW_DEFAULT["am"] * 1e3
        self._bw_dirty = False

    def set_bw(self, bw_hz):
        self.bw_hz = float(bw_hz)
        self._bw_dirty = True

    def reset(self):
        if self._b_rf is None:
            self._b_rf = _firwin_lp(65, 40e3, SDR_RATE)         # doar anti-alias înainte de decimare
            self._b_af = _firwin_lp(81, 3.2e3, MPX_RATE)
        self._b_ch = _firwin_lp(CH_TAPS, self.bw_hz / 2.0, MPX_RATE)    # filtrul de canal, cu lățime reglabilă
        self._bw_dirty = False
        self._z_ch = np.zeros(CH_TAPS - 1, dtype=complex)
        self._z_rf = np.zeros(len(self._b_rf) - 1, dtype=complex)
        self._z_af = np.zeros(len(self._b_af) - 1)
        self._dc = 0.0

    def audio(self, x, squelch_open=True):
        y, self._z_rf = _fir_stream(self._b_rf, x, self._z_rf)
        y = y[::DEC1]
        if self._bw_dirty:
            self._bw_dirty = False
            self._b_ch = _firwin_lp(CH_TAPS, self.bw_hz / 2.0, MPX_RATE)
        y, self._z_ch = _fir_stream(self._b_ch, y, self._z_ch)
        env = np.abs(y)
        self._dc = 0.995 * self._dc + 0.005 * float(np.mean(env))
        ac = env - self._dc
        af, self._z_af = _fir_stream(self._b_af, ac, self._z_af)
        out = af[::DEC2]
        if not squelch_open:
            out = np.zeros_like(out)
        self.raw = out                      # înainte de AGC: păstrează dinamica vorbirii
        peak = float(np.max(np.abs(out))) if len(out) else 0.0
        gain = min(4.0, 0.45 / max(peak, 0.05)) if squelch_open else 0.0
        return (out * gain).clip(-1, 1).astype(np.float32).reshape(-1, 1)


class NfmDemod:
    """Demodulator FM îngust (NFM) pentru radioamatori: IQ -> filtru ~12.5 kHz -> discriminator -> voce ~3.5 kHz."""

    def __init__(self):
        self._b_rf = None
        self._b_af = None
        self.bw_hz = BW_DEFAULT["nfm"] * 1e3
        self._bw_dirty = False

    def _rf_cut(self):
        return max(40e3, 0.9 * self.bw_hz / 2.0 + 20e3)

    def set_bw(self, bw_hz):
        self.bw_hz = float(bw_hz)
        self._bw_dirty = True

    def reset(self):
        if self._b_rf is None:
            self._b_rf = _firwin_lp(65, self._rf_cut(), SDR_RATE)         # doar anti-alias înainte de decimare
            self._b_af = _firwin_lp(81, 3.6e3, MPX_RATE)
        self._b_ch = _firwin_lp(CH_TAPS, self.bw_hz / 2.0, MPX_RATE)    # filtrul de canal, cu lățime reglabilă
        self._bw_dirty = False
        self._z_ch = np.zeros(CH_TAPS - 1, dtype=complex)
        self._z_rf = np.zeros(len(self._b_rf) - 1, dtype=complex)
        self._z_af = np.zeros(len(self._b_af) - 1)
        self._prev = np.complex128(0)

    def audio(self, x, squelch_open=True):
        y, self._z_rf = _fir_stream(self._b_rf, x, self._z_rf)
        y = y[::DEC1]
        if self._bw_dirty:
            self._bw_dirty = False
            self._b_ch = _firwin_lp(CH_TAPS, self.bw_hz / 2.0, MPX_RATE)
            self._b_rf = _firwin_lp(65, self._rf_cut(), SDR_RATE)      # banda largă (NFM 60/80) cere și antialias mai larg
        y, self._z_ch = _fir_stream(self._b_ch, y, self._z_ch)
        z = np.concatenate(([self._prev], y))
        self._prev = y[-1]
        disc = np.angle(z[1:] * np.conj(z[:-1])) * (MPX_RATE / (2 * np.pi * 5e3))
        af, self._z_af = _fir_stream(self._b_af, disc, self._z_af)
        out = af[::DEC2]
        if not squelch_open:
            out = np.zeros_like(out)
        return (out * 0.7).clip(-1, 1).astype(np.float32).reshape(-1, 1)


# ============================================================================
#  2b. DECODOARE DE DATE (AX.25 / APRS, ACARS, DTMF) ȘI CLASIFICAREA TRANSMISIILOR
# ============================================================================
ACARS_FREQS = (131.525, 131.550, 131.725, 131.825)   # MHz: canale ACARS VHF (Europa + global)
APRS_FREQS = (144.800, 145.825)                       # MHz: APRS Europa și APRS ISS
BANK_SPAN_MHZ = 0.78                                  # canalele mai depărtate nu încap în banda SDR


def _make_crc_table():
    tab = []
    for i in range(256):
        c = i
        for _ in range(8):
            c = (c >> 1) ^ 0x8408 if c & 1 else c >> 1
        tab.append(c)
    return tab


_CRC16 = _make_crc_table()


def _crc16(data, init):
    """CRC-16 CCITT reflectat (poly 0x8408), la fel pentru AX.25 (init 0xFFFF) și ACARS (init 0)."""
    crc = init
    for b in data:
        crc = (crc >> 8) ^ _CRC16[(crc ^ b) & 0xFF]
    return crc


def noise_prior_db(mode, hb=None):
    """Nivelul teoretic (dB peste podeaua de zgomot) al unui canal fără semnal, după lățimea lui (hb = jumătate, Hz)."""
    if hb is None:
        hb = 10e3 if mode == "am" else 12.5e3
    return 10.0 * math.log10(2 * hb / (SDR_RATE / 4096)) + 1.0


def _bandpass_taps(numtaps, lo, hi, fs):
    n = np.arange(numtaps) - (numtaps - 1) / 2
    h = (2 * hi / fs * np.sinc(2 * hi / fs * n) - 2 * lo / fs * np.sinc(2 * lo / fs * n)) * np.hamming(numtaps)
    return h


def _decim_fir(b, x, hist, m):
    """FIR cu decimare: calculează doar fiecare a m-a ieșire (de m ori mai ieftin decât convolve)."""
    xp = np.concatenate((hist, x))
    n_out = len(x) // m
    L = len(b)
    acc = np.zeros(n_out, dtype=complex)
    for j in range(L):
        start = L - 1 - j
        acc += b[j] * xp[start:start + m * n_out:m]
    return acc, xp[len(xp) - (L - 1):]


def _clean_text(s, limit=220):
    s = re.sub(r"[\r\n]+", " / ", s)
    s = "".join(ch if ch.isprintable() else "·" for ch in s)
    return s.strip()[:limit]


# --- AX.25 / APRS ----------------------------------------------------------
class Ax25Hdlc:
    """Cadre HDLC din biți NRZI-decodați: flag-uri, umplere cu zerouri, verificare FCS (CRC-16)."""

    def __init__(self):
        self.reset()

    def reset(self):
        self._ones = 0
        self._in = False
        self._cur = []
        self.stats = {"sync": 0, "ok": 0, "bad": 0}

    def _finish(self, bits):
        if len(bits) % 8 or len(bits) < 8 * 17:
            return None
        self.stats["sync"] += 1
        data = bytearray()
        for i in range(0, len(bits), 8):
            v = 0
            for j in range(8):
                v |= bits[i + j] << j
            data.append(v)
        if _crc16(data, 0xFFFF) != 0xF0B8:
            self.stats["bad"] += 1
            return None
        self.stats["ok"] += 1
        return bytes(data[:-2])

    def feed(self, bit):
        if bit:
            self._ones += 1
            if self._ones >= 7:
                self._in = False
                self._cur = []
            elif self._in:
                self._cur.append(1)
            return None
        ones, self._ones = self._ones, 0
        res = None
        if ones == 6:                                   # flag 01111110
            if self._in and len(self._cur) >= 7:
                res = self._finish(self._cur[:-7])      # fără flag-ul: 0 + șase de 1
            self._in = True
            self._cur = []
        elif ones == 5:
            pass                                        # zero de umplere
        elif ones >= 7:
            self._in = False
            self._cur = []
        elif self._in:
            self._cur.append(0)
            if len(self._cur) > 8 * 340:
                self._in = False
                self._cur = []
        return res


class Afsk1200Decoder:
    """Bell 202 AFSK 1200 baud (mark 1200 / space 2200 Hz) la 48 kHz -> cadre AX.25 cu FCS valid.
    Corelatoare pe un bit pentru cele două tonuri, normalizate separat, plus PLL de ceas de bit."""

    FS = float(AUDIO_RATE)
    SPS = AUDIO_RATE // 1200            # 40 eșantioane / bit

    BIAS = (0.5, 0.75, 1.0, 1.35, 1.75)  # praguri extinse: sensibilitate mare pe semnale slabe/decalate

    def __init__(self):
        self._bp = _bandpass_taps(129, 900.0, 2600.0, self.FS)
        self._box = np.ones(self.SPS) / self.SPS
        self.reset()

    @property
    def stats(self):
        out = {"sync": 0, "ok": 0, "bad": 0}
        for s in self._sl:
            for k in out:
                out[k] += s["hdlc"].stats[k]
        return out

    def reset(self):
        self._zbp = np.zeros(len(self._bp) - 1)
        self._zm = np.zeros(self.SPS - 1, dtype=complex)
        self._zs = np.zeros(self.SPS - 1, dtype=complex)
        self._n = 0
        self._pm = 1e-6
        self._ps = 1e-6
        self._sl = [{"k": k, "phase": 0.0, "last": False, "tone": 1, "hdlc": Ax25Hdlc()} for k in self.BIAS]

    def feed_audio(self, a):
        y, self._zbp = _fir_stream(self._bp, np.asarray(a, dtype=np.float64), self._zbp)
        n = len(y)
        if n == 0:
            return []
        t = (self._n + np.arange(n)) / self.FS
        self._n = (self._n + n) % AUDIO_RATE
        m, self._zm = _fir_stream(self._box, y * np.exp(-2j * np.pi * 1200.0 * t), self._zm)
        s, self._zs = _fir_stream(self._box, y * np.exp(-2j * np.pi * 2200.0 * t), self._zs)
        am, as_ = np.abs(m), np.abs(s)
        self._pm = max(float(am.max()), self._pm * 0.97, 1e-9)
        self._ps = max(float(as_.max()), self._ps * 0.97, 1e-9)
        mk, sp = am / self._pm, as_ / self._ps
        half, full = self.SPS / 2.0, float(self.SPS)
        frames = []
        for s in self._sl:
            phase, last, tone, hdlc = s["phase"], s["last"], s["tone"], s["hdlc"]
            for v in (mk - s["k"] * sp).tolist():
                sgn = v > 0.0
                if sgn != last:                 # tranziție de ton: ar trebui să cadă la început de bit
                    err = phase if phase < half else phase - full
                    phase = (phase - 0.4 * err) % full
                    last = sgn
                pp = phase
                phase += 1.0
                if phase >= full:
                    phase -= full
                elif pp < half <= phase:        # mijlocul bitului (la o jumătate de bit după tranziție)
                    t_now = 1 if sgn else 0
                    fr = hdlc.feed(1 if t_now == tone else 0)       # NRZI: fără schimbare = 1
                    tone = t_now
                    if fr is not None:
                        frames.append(fr)
            s["phase"], s["last"], s["tone"] = phase, last, tone
        return frames


def _ax25_addr(a):
    chars = [c >> 1 for c in a[:6]]
    if not all(0x20 <= c < 0x7F for c in chars):
        return None
    call = "".join(chr(c) for c in chars).strip()
    if not call or not call.isalnum():
        return None
    ssid = (a[6] >> 1) & 0x0F
    return call + (f"-{ssid}" if ssid else ""), bool(a[6] & 0x80), bool(a[6] & 1)


def parse_ax25(frame):
    """Cadru AX.25 (fără FCS) -> (sursă, destinație, [digipeateri], control, pid, info) sau None."""
    i, addrs = 0, []
    while True:
        a = frame[i:i + 7]
        if len(a) < 7:
            return None
        r = _ax25_addr(a)
        if r is None:
            return None
        addrs.append(r)
        i += 7
        if r[2]:
            break
        if len(addrs) > 10:
            return None
    if len(addrs) < 2 or len(frame) < i + 1:
        return None
    ctrl = frame[i]
    pid = frame[i + 1] if len(frame) > i + 1 else None
    digis = [d[0] + ("*" if d[1] else "") for d in addrs[2:]]
    return addrs[1][0], addrs[0][0], digis, ctrl, pid, bytes(frame[i + 2:])


def _b91(s):
    v = 0
    for ch in s:
        v = v * 91 + (ord(ch) - 33)
    return v


def _fmt_latlon(lat, lon):
    return (f"{abs(lat):.4f}°{'N' if lat >= 0 else 'S'}, "
            f"{abs(lon):.4f}°{'E' if lon >= 0 else 'W'}")


def _aprs_position(body):
    """(lat, lon, comentariu) dintr-o poziție APRS necomprimată sau comprimată."""
    try:
        if len(body) >= 19 and (body[0].isdigit() or body[0] == " "):
            lat_s, lon_s = body[0:8].replace(" ", "0"), body[9:18].replace(" ", "0")
            lat = int(lat_s[:2]) + float(lat_s[2:7]) / 60.0
            lon = int(lon_s[:3]) + float(lon_s[3:8]) / 60.0
            if lat_s[7] in "sS":
                lat = -lat
            if lon_s[8] in "wW":
                lon = -lon
            if lat_s[7] not in "NSns" or lon_s[8] not in "EWew":
                return None
            return lat, lon, body[19:]
        if len(body) >= 13:
            lat = 90.0 - _b91(body[1:5]) / 380926.0
            lon = -180.0 + _b91(body[5:9]) / 190463.0
            if -90 <= lat <= 90 and -180 <= lon <= 180:
                return lat, lon, body[13:]
    except (ValueError, IndexError):
        pass
    return None


def _aprs_mice(dest, s):
    """Poziție Mic-E: latitudinea e ascunsă în adresa destinație, longitudinea în câmpul info."""
    if len(s) < 9 or len(dest) < 6:
        return None
    digs = []
    for ch in dest[:6]:
        if "0" <= ch <= "9":
            digs.append(ord(ch) - 48)
        elif "A" <= ch <= "J":
            digs.append(ord(ch) - 65)
        elif "P" <= ch <= "Y":
            digs.append(ord(ch) - 80)
        elif ch in "KLZ":
            digs.append(0)
        else:
            return None
    lat = digs[0] * 10 + digs[1] + (digs[2] * 10 + digs[3] + (digs[4] * 10 + digs[5]) / 100.0) / 60.0
    if dest[3] < "P":
        lat = -lat
    b = [ord(c) for c in s[:9]]
    lond = b[1] - 28 + (100 if dest[4] >= "P" else 0)
    if 180 <= lond <= 189:
        lond -= 80
    elif 190 <= lond <= 199:
        lond -= 190
    lonm = b[2] - 28
    if lonm >= 60:
        lonm -= 60
    lon = lond + (lonm + (b[3] - 28) / 100.0) / 60.0
    if dest[5] >= "P":
        lon = -lon
    sp = (b[4] - 28) * 10 + (b[5] - 28) // 10
    crs = ((b[5] - 28) % 10) * 100 + (b[6] - 28)
    if sp >= 800:
        sp -= 800
    if crs >= 400:
        crs -= 400
    if not (0 <= lat <= 90 or -90 <= lat < 0) or lond > 180:
        return None
    return lat, lon, sp * 1.852, crs, s[9:]


def aprs_summary(dest, info):
    """Rezumat localizat al unui pachet APRS; None dacă tipul nu e înțeles."""
    if not info:
        return None
    s = info.decode("latin-1")
    t = s[0]
    if t in "!=/@":
        body = s[1:]
        if t in "/@":
            body = body[7:]
        pos = _aprs_position(body)
        if pos:
            com = _clean_text(pos[2])
            return _L("aprs_pos", _fmt_latlon(pos[0], pos[1]), (" — " + com) if com else "")
    elif t == ":" and len(s) >= 11 and s[10] == ":":
        return _L("aprs_msg", s[1:10].strip(), _clean_text(s[11:].split("{")[0]))
    elif t == ">":
        return _L("aprs_status", _clean_text(s[1:]))
    elif t in "`'":
        r = _aprs_mice(dest, s)
        if r:
            com = _clean_text(r[4])
            return _L("aprs_mice", _fmt_latlon(r[0], r[1]), f"{r[2]:.0f}", f"{r[3]:.0f}",
                      (" — " + com) if com else "")
    return None


def afsk_frame_item(freq_mhz, frame):
    p = parse_ax25(frame)
    if p is None:
        return None
    src, dest, digis, ctrl, pid, info = p
    head = f"{src}>{dest}" + ("," + ",".join(digis) if digis else "")
    txt = _clean_text(info.decode("latin-1"))
    if ctrl & 0xEF == 0x03 and pid == 0xF0:
        body = aprs_summary(dest, info) or _L("aprs_other", txt)
        tag = "APRS"
    else:
        body = _L("ax25_frame", txt)
        tag = "AX.25"
    return {"time": time.strftime("%H:%M:%S"), "freq": f"{freq_mhz:.4f}".rstrip("0").rstrip(".") + " MHz",
            "tag": tag, "band": "ham", "text": f"{head}: {body}"}


# --- ACARS -----------------------------------------------------------------
class AcarsMskDemod:
    """Audio AM 48 kHz (anvelopa) -> biți de date ACARS. MSK 2400 Bd cu tonuri de 1200/2400 Hz:
    ton de 2400 Hz = bit neschimbat față de precedentul, ton de 1200 Hz = bit inversat."""

    FS = float(AUDIO_RATE)
    SPS = 20

    def __init__(self):
        self._lp = _firwin_lp(101, 1500.0, self.FS)
        self._b5 = np.ones(5) / 5
        self._b10 = np.ones(10) / 10
        self.reset()

    def reset(self):
        self._z = np.zeros(100, dtype=complex)
        self._prev = np.complex128(0)
        self._z5 = np.zeros(4)
        self._z10 = np.zeros(9)
        self._n = 0
        self._phase = 0.0
        self._last_s = False
        self._d = 1

    def process(self, a):
        n = len(a)
        if n == 0:
            return []
        t = (self._n + np.arange(n)) / self.FS
        self._n = (self._n + n) % AUDIO_RATE
        # spre bandă de bază în jurul a 1800 Hz: tonurile devin ±600 Hz (±π/2 pe bit)
        z, self._z = _fir_stream(self._lp, np.asarray(a, dtype=np.float64) * np.exp(-2j * np.pi * 1800.0 * t), self._z)
        zz = np.concatenate(([self._prev], z))
        self._prev = z[-1]
        u = np.angle(zz[1:] * np.conj(zz[:-1]))
        us, self._z5 = _fir_stream(self._b5, u, self._z5)
        um, self._z10 = _fir_stream(self._b10, u, self._z10)
        phase, last, d = self._phase, self._last_s, self._d
        bits = []
        half, full = self.SPS / 2.0, float(self.SPS)
        for sg, mv in zip((us > 0).tolist(), um.tolist()):
            if sg != last:
                err = phase if phase < half else phase - full
                phase = (phase - 0.4 * err) % full
                last = sg
            pp = phase
            phase += 1.0
            if phase >= full:
                phase -= full
            elif pp < 12.0 <= phase:        # în interiorul simbolului, după întârzierea filtrelor
                if mv <= 0.0:
                    d ^= 1
                bits.append(d)
        self._phase, self._last_s, self._d = phase, last, d
        return bits


class AcarsFramer:
    """Biți ACARS -> mesaje: sincronizare (+ * SYN SYN, ambele polarități), paritate impară pe caracter,
    BCS = CRC-16 Kermit peste Mode..ETX/ETB."""

    SYNC = (0x2B, 0x2A, 0x16, 0x16)
    ETX, ETB = 0x83, 0x97                      # cu bitul de paritate

    def __init__(self):
        pat = 0
        for byte in self.SYNC:
            for k in range(8):
                pat = (pat << 1) | ((byte >> k) & 1)
        self._pat = pat
        self.reset()

    def reset(self):
        self._reg = 0
        self._state = 0
        self._acc = 0
        self._nb = 0
        self._inv = False
        self._buf = []
        self._crc = []
        self._perr = 0
        self.stats = {"sync": 0, "ok": 0, "bad": 0}

    def _start(self, inv):
        self.stats["sync"] += 1
        self._state = 1
        self._inv = inv
        self._acc = 0
        self._nb = 0
        self._buf = []
        self._crc = []
        self._perr = 0

    def feed(self, bits):
        out = []
        for b in bits:
            self._reg = ((self._reg << 1) | b) & 0xFFFFFFFF
            if self._state == 0:
                x = self._reg ^ self._pat
                if bin(x).count("1") <= 3:
                    self._start(False)
                elif bin(x ^ 0xFFFFFFFF).count("1") <= 3:
                    self._start(True)
                continue
            self._acc |= b << self._nb
            self._nb += 1
            if self._nb == 8:
                byte = self._acc ^ (0xFF if self._inv else 0)
                self._acc = 0
                self._nb = 0
                r = self._byte(byte)
                if r:
                    out.append(r)
        return out

    def _byte(self, byte):
        st = self._state
        if st == 1:
            self._state = 2 if byte == 0x01 else 0          # SOH
            return None
        if st == 2:
            self._buf.append(byte)
            if bin(byte).count("1") % 2 == 0:               # paritate impară așteptată
                self._perr += 1
            if self._perr > 4 or len(self._buf) > 240:
                self._state = 0
            elif byte in (self.ETX, self.ETB):
                self._state = 3
            return None
        self._crc.append(byte)                              # st == 3: BCS (octetul mic primul)
        if len(self._crc) < 2:
            return None
        self._state = 0
        return self._finish()

    def _fix(self, buf):
        """Corectează 1–2 caractere cu paritate greșită, încercând bit cu bit până se potrivește CRC-ul."""
        bad = [i for i, b in enumerate(buf) if bin(b).count("1") % 2 == 0]
        if not 1 <= len(bad) <= 2:
            return None
        cand = list(buf)
        for b1 in range(8):
            cand[bad[0]] = buf[bad[0]] ^ (1 << b1)
            if len(bad) == 1:
                if _crc16(cand + self._crc, 0) == 0:
                    return cand
                continue
            for b2 in range(8):
                cand[bad[1]] = buf[bad[1]] ^ (1 << b2)
                if _crc16(cand + self._crc, 0) == 0:
                    return cand
        return None

    def _finish(self):
        buf = self._buf
        ok = _crc16(buf + self._crc, 0) == 0
        if not ok and self._perr and len(buf) >= 13:
            fixed = self._fix(buf)
            if fixed is not None:
                buf, ok = fixed, True
        if len(buf) < 13 or (not ok and self._perr):
            self.stats["bad"] += 1
            return None
        self.stats["ok" if ok else "bad"] += 1
        ch = [b & 0x7F for b in buf]
        text = "".join(chr(c) for c in ch[13:-1]) if len(ch) > 13 else ""
        ack = {0x06: "ACK", 0x15: "NAK"}.get(ch[8], chr(ch[8]) if 32 <= ch[8] < 127 else "?")
        return {
            "mode": chr(ch[0]),
            "reg": "".join(chr(c) if 32 <= c < 127 else "?" for c in ch[1:8]).lstrip(".").strip(),
            "ack": ack,
            "label": "".join(chr(c) if 32 < c < 127 else "·" for c in ch[9:11]),
            "blk": chr(ch[11]) if 32 <= ch[11] < 127 else "?",
            "text": _clean_text(text),
            "crc_ok": ok,
        }


def acars_item(freq_mhz, m):
    body = _L("acars_msg", m["reg"] or "?", m["label"], m["blk"], m["text"] or _L("acars_notext"))
    if not m["crc_ok"]:
        body = _L("acars_crc_bad") + body
    return {"time": time.strftime("%H:%M:%S"), "freq": f"{freq_mhz:.4f}".rstrip("0").rstrip(".") + " MHz",
            "tag": "ACARS", "band": "air", "text": body}


# --- canal de decodare + banc de canale -------------------------------------
class _DecChannel:
    """Un canal radio izolat din blocul IQ (mixare, filtrare, decimare) + decodorul lui."""

    def __init__(self, freq_mhz, center_hz, kind):
        self.freq = freq_mhz
        self.kind = kind
        self._off = freq_mhz * 1e6 - center_hz
        self._rot = np.exp(-2j * np.pi * self._off * np.arange(CHUNK) / SDR_RATE)
        self._acc = 1 + 0j
        self._step = np.exp(-2j * np.pi * self._off * CHUNK / SDR_RATE)
        self._b1 = _firwin_lp(65, 90e3, SDR_RATE)
        self._b2 = _firwin_lp(101, 12e3, MPX_RATE)
        self._b3 = _firwin_lp(121, 3.4e3, MPX_RATE)
        self._z1 = np.zeros(64, dtype=complex)
        self._z2 = np.zeros(100, dtype=complex)
        self._z3 = np.zeros(120)
        self._prev = np.complex128(0)
        self._seen = {}
        if kind == "acars":
            self._bp = _bandpass_taps(129, 700.0, 3000.0, AUDIO_RATE)
            self._zbp = np.zeros(128)
            self.demod = AcarsMskDemod()
            self.framer = AcarsFramer()
        else:
            self.demod = Afsk1200Decoder()

    def _dedupe(self, key):
        now = time.time()
        for k in [k for k, t in self._seen.items() if now - t > 10.0]:
            del self._seen[k]
        if key in self._seen:
            return True
        self._seen[key] = now
        return False

    def _retune(self, n):
        k = np.arange(n)
        self._rot = np.exp(-2j * np.pi * self._off * k / SDR_RATE)
        self._step = np.exp(-2j * np.pi * self._off * n / SDR_RATE)

    @property
    def stats(self):
        return (self.framer if self.kind == "acars" else self.demod).stats

    def process(self, x):
        n = len(x) - len(x) % DEC1
        if n <= 0:
            return []
        if n != len(self._rot):
            self._retune(n)
        x = x[:n]
        xm = x * self._rot
        xm *= self._acc
        self._acc *= self._step
        self._acc /= abs(self._acc)
        y, self._z1 = _decim_fir(self._b1, xm, self._z1, DEC1)
        y, self._z2 = _fir_stream(self._b2, y, self._z2)
        items = []
        if self.kind == "acars":
            a, self._z3 = _fir_stream(self._b3, np.abs(y), self._z3)
            a, self._zbp = _fir_stream(self._bp, a[::DEC2], self._zbp)
            for m in self.framer.feed(self.demod.process(a)):
                if not self._dedupe((m["reg"], m["label"], m["blk"], m["text"])):
                    items.append(acars_item(self.freq, m))
        else:
            z = np.concatenate(([self._prev], y))
            self._prev = y[-1]
            disc = np.angle(z[1:] * np.conj(z[:-1]))
            a, self._z3 = _fir_stream(self._b3, disc, self._z3)
            for fr in self.demod.feed_audio(a[::DEC2]):
                if not self._dedupe(fr):
                    it = afsk_frame_item(self.freq, fr)
                    if it:
                        items.append(it)
        return items


class DecoderBank:
    """Decodează în paralel, din același flux IQ, toate canalele cunoscute din jurul frecvenței acordate
    (ACARS pe aviație, APRS pe radioamatori), independent de ce se aude."""

    def __init__(self):
        self._key = None
        self.channels = []

    def reset(self):
        self._key = None
        self.channels = []

    def _build(self, center_mhz, mode):
        if mode == "am":
            fl = [f for f in ACARS_FREQS if abs(f - center_mhz) <= BANK_SPAN_MHZ]
            if 129.0 <= center_mhz <= 132.5 and not any(abs(f - center_mhz) < 0.003 for f in ACARS_FREQS):
                fl.append(center_mhz)
            kind = "acars"
        elif mode == "nfm":
            fl = [center_mhz] + [f for f in APRS_FREQS if 0.003 < abs(f - center_mhz) <= BANK_SPAN_MHZ]
            kind = "afsk"
        else:
            fl, kind = [], None
        self.channels = [_DecChannel(f, center_mhz * 1e6, kind) for f in fl]

    def status(self):
        """([frecvențe], sincronizări, mesaje valide, CRC greșit) pentru canalele active."""
        st = [ch.stats for ch in self.channels]
        return ([ch.freq for ch in self.channels], sum(s["sync"] for s in st),
                sum(s["ok"] for s in st), sum(s["bad"] for s in st))

    def process(self, x, center_mhz, mode):
        key = (round(center_mhz, 4), mode)
        if key != self._key:
            self._key = key
            self._build(center_mhz, mode)
        out = []
        for ch in self.channels:
            out.extend(ch.process(x))
        return out


# --- DTMF -------------------------------------------------------------------
class DtmfDecoder:
    """Tonuri DTMF (ex. apel selectiv, comenzi de repetor) din audio 48 kHz, cu FFT pe ferestre de 40 ms."""

    N, HOP = 1920, 480
    LOW = (697, 770, 852, 941)
    HIGH = (1209, 1336, 1477, 1633)
    KEYS = ("123A", "456B", "789C", "*0#D")

    def __init__(self):
        self._w = np.hanning(self.N)
        self._kl = [int(round(f * self.N / AUDIO_RATE)) for f in self.LOW]
        self._kh = [int(round(f * self.N / AUDIO_RATE)) for f in self.HIGH]
        self._b0 = int(300 * self.N / AUDIO_RATE)
        self._b1 = int(3400 * self.N / AUDIO_RATE) + 1
        self.reset()

    def reset(self):
        self._buf = np.zeros(0)
        self._cand = None
        self._cnt = 0
        self._gap = 99
        self._gap_before = 99
        self._last_digit = None
        self._digits = ""
        self._last_t = 0.0

    def _detect(self, seg):
        if float(np.mean(seg * seg)) < 1e-5:
            return None
        P = np.abs(np.fft.rfft(seg * self._w)) ** 2
        tot = float(P[self._b0:self._b1].sum()) + 1e-12
        el = [float(P[k - 1:k + 2].sum()) for k in self._kl]
        eh = [float(P[k - 1:k + 2].sum()) for k in self._kh]
        il, ih = int(np.argmax(el)), int(np.argmax(eh))
        sl, sh = sorted(el), sorted(eh)
        if sl[-1] < 4 * sl[-2] or sh[-1] < 4 * sh[-2]:
            return None
        twist = el[il] / max(eh[ih], 1e-12)
        if not 0.15 < twist < 6.7:
            return None
        if el[il] + eh[ih] < 0.6 * tot:
            return None
        return self.KEYS[il][ih]

    def feed(self, x, freq_mhz, now=None):
        now = time.time() if now is None else now
        items = []
        self._buf = np.concatenate((self._buf, np.asarray(x, dtype=np.float64)))
        while len(self._buf) >= self.N:
            seg = self._buf[:self.N]
            self._buf = self._buf[self.HOP:]
            d = self._detect(seg)
            if d is None:
                self._cand, self._cnt = None, 0
                self._gap += 1
                continue
            if d != self._cand:
                self._cand, self._cnt = d, 1
                self._gap_before = self._gap
            else:
                self._cnt += 1
            self._gap = 0
            if self._cnt == 3 and (d != self._last_digit or self._gap_before >= 4):
                self._digits += d
                self._last_digit = d
                self._last_t = now
        if self._digits and (now - self._last_t > 2.0 or len(self._digits) >= 48):
            items.append({"time": time.strftime("%H:%M:%S"),
                          "freq": f"{freq_mhz:.4f}".rstrip("0").rstrip(".") + " MHz",
                          "tag": "DTMF", "band": "ham", "text": _L("dtmf_seq", self._digits)})
            self._digits = ""
            self._last_digit = None
        return items


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
        rule = f'SUBSYSTEM=="usb", ATTRS{{idVendor}}=="{vid}", ATTRS{{idProduct}}=="{pid}", MODE="0666"'
        return _L("err_perm", rule)

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
        node, deadline = None, time.time() + 5.0
        while node is None and time.time() < deadline:
            node = next((n for n in sorted(self._dvb_nodes(devname))
                         if n.endswith("/frontend0") and os.path.exists(n)), None)
            if node is None:
                time.sleep(0.2)
        if node is None:
            return
        def hold():
            try:
                fd = os.open(node, os.O_RDWR)
            except OSError:
                return                          # ocupat sau fără drepturi: nu e grav, TV-ul merge ca înainte
            try:
                time.sleep(WAKE_HOLD_SECS)
            finally:
                os.close(fd)
        # open() pe un frontend blocat poate rămâne agățat în kernel: îl facem într-un fir, cu timp limită
        t = threading.Thread(target=hold, daemon=True)
        t.start()
        t.join(WAKE_HOLD_SECS + 3.0)

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
                    raise RuntimeError(_L("err_detach", ifname, e))
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
                self.last_error = _L("err_reattach", ifname, e)

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
        self.tuner_type = 5             # se citește din antetul rtl_tcp la conectare
        self.hf_direct = False          # setat de Engine: HF prin „direct sampling” doar la RTL-SDR Blog V3
        self.log_text = ""              # ce a scris rtl_tcp la pornire (nume dispozitiv, tuner)
        self._ds = 0
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

    def _read_log(self):
        """Textul scris de rtl_tcp pe stderr. pread nu mută poziția fișierului, care e partajată cu procesul copil."""
        try:
            return os.pread(self._errf.fileno(), 65536, 0).decode(errors="replace")
        except Exception:
            return ""

    def _rtl_error(self):
        try:
            self._errf.seek(0)
            lines = [l.strip() for l in self._errf.read().decode(errors="replace").splitlines() if l.strip()]
        except Exception:
            lines = []
        low = " ".join(lines).lower()
        if "no supported devices" in low:
            return _L("err_no_device")
        if "permission" in low or "usb_open error -3" in low:
            return _L("err_dev_perm")
        if "failed to open" in low:
            return _L("err_dev_open", " | ".join(lines[-2:]))
        return " | ".join(lines[-2:]) or _L("err_rtl_nomsg")

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
                    raise RuntimeError(_L("err_rtl_timeout", self._rtl_error()))
                time.sleep(0.1)
        self._sock.settimeout(2.0)
        hdr = self._recv_exact(12)                 # "RTL0" + tip tuner + nr. trepte gain
        if bytes(hdr[:4]) != b"RTL0":
            raise RuntimeError(_L("err_rtl_badhdr"))
        self.tuner_type = struct.unpack(">I", bytes(hdr[4:8]))[0]
        self.log_text = self._read_log()

    def _recv_exact(self, n):
        buf = bytearray(n)
        view = memoryview(buf)
        got = 0
        while got < n:
            try:
                k = self._sock.recv_into(view[got:], n - got)
            except socket.timeout:
                if self._stop:
                    raise ConnectionError(_L("err_stopped_short"))
                continue
            if k == 0:
                raise ConnectionError(_L("err_rtl_stopped", self._rtl_error()))
            got += k
        return buf

    def _cmd(self, code, param):
        if self._sock is None:
            raise ConnectionError(_L("err_stopped_short"))
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
        if self.hf_direct:                          # sub 24 MHz: ramura Q în mod direct, altfel tunerul normal
            want = 2 if self._freq < HF_DIRECT_BELOW_HZ else 0
            if want != self._ds:
                self._ds = want
                self._cmd(0x09, want)
        self._cmd(0x01, self._freq)

    @property
    def ppm(self):
        return self._ppm

    @ppm.setter
    def ppm(self, v):
        self._ppm = int(v)
        self._cmd(0x05, self._ppm)                 # corecția cristalului; librtlsdr retunează singur după ea

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
                try:
                    self._proc.wait(2)          # un proces blocat în kernel nu trebuie să ne blocheze și pe noi
                except subprocess.TimeoutExpired:
                    pass
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


def list_pipewire_sinks():
    """[(nume_intern, descriere)] ale ieșirilor audio PipeWire, din `pw-dump` (vine cu PipeWire);
    dacă nu merge, din `pactl`. Listă goală dacă niciuna nu răspunde."""
    sinks = []
    pw_dump = shutil.which("pw-dump")
    if pw_dump:
        try:
            data = json.loads(subprocess.run([pw_dump], capture_output=True, text=True, timeout=4).stdout or "[]")
            for obj in data if isinstance(data, list) else []:
                if obj.get("type") != "PipeWire:Interface:Node":
                    continue
                props = (obj.get("info") or {}).get("props") or {}
                name = (props.get("node.name") or "").strip()
                if props.get("media.class") == "Audio/Sink" and name and name not in [n for n, _d in sinks]:
                    sinks.append((name, props.get("node.description") or props.get("node.nick") or name))
        except Exception:
            pass
    if not sinks and shutil.which("pactl"):
        try:
            out = subprocess.run(["pactl", "list", "sinks"], capture_output=True, text=True, timeout=4,
                                 env=dict(os.environ, LC_ALL="C")).stdout
            name = None
            for line in out.splitlines():
                t = line.strip()
                if t.startswith("Name:"):
                    name = t[5:].strip()
                elif t.startswith("Description:") and name:
                    sinks.append((name, t[12:].strip() or name))
                    name = None
        except Exception:
            pass
    return sinks


def pcm_stereo(a, vol):
    """Audio float32 (N, 1) -> octeți PCM S16_LE stereo (același semnal pe ambele canale)."""
    pcm = (a[:, 0] * (vol * 32767)).clip(-32768, 32767).astype("<i2")
    return np.repeat(pcm, 2).tobytes()


class AplayOutput:
    """Redă PCM S16_LE stereo prin aplay + PipeWire. Când e ales un sink anume, îl indică prin
    PIPEWIRE_NODE și PULSE_SINK (aplay -D pipewire)."""

    def __init__(self, device=None, sink=None):
        cmd = [shutil.which("aplay"), "-q", "-t", "raw", "-f", "S16_LE", "-r", str(AUDIO_RATE),
               "-c", "2", "--buffer-time=200000"]
        env = os.environ.copy()
        if sink:
            env["PIPEWIRE_NODE"] = sink
            env["PULSE_SINK"] = sink
            cmd += ["-D", "pipewire"]
        elif device:
            cmd += ["-D", device]
        self._errf = tempfile.TemporaryFile()
        self._proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.DEVNULL,
                                      stderr=self._errf, env=env)
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
            raise RuntimeError(_L("err_no_ffmpeg"))
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
            msg = self._last_error() or _L("err_ffmpeg_stopped")
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
            self._err = self._err or _L("err_ffmpeg_timeout")
        err = self._err
        if err is None and self._proc.returncode != 0:
            err = self._last_error() or _L("err_ffmpeg_code", self._proc.returncode)
        if err is None and (not os.path.exists(self.path) or os.path.getsize(self.path) == 0):
            err = _L("err_rec_empty")
        self._errf.close()
        return self.path, err


# ============================================================================
#  7. ENGINE (fire de execuție: citire -> demodulare -> audio, plus scanare)
# ============================================================================
#  6b. CALIBRARE PPM (eroarea cristalului dongle-ului)
# ============================================================================
# Ideea: o stație GSM emite periodic un burst FCCH = ton pur la exact 1625000/24 Hz peste purtătoare, cu ceas
# foarte precis. Cât de departe de acea frecvență vedem tonul = eroarea cristalului (aceeași în ppm pe orice frecvență).
FCCH_OFFSET_HZ = 1625000.0 / 24.0
GSM_BANDS = {"gsm900": (925.2, 959.8), "gsm850": (869.2, 893.8)}      # purtătoare la 200 kHz (MHz)
CAL_MAX_PPM = 150.0


def ppm_from_offset(p0, offset_hz, freq_hz):
    """Corecția ppm nouă. offset_hz = frecvența observată - frecvența reală (la corecția p0 deja aplicată).
    Dacă semnalul apare prea sus, tunerul crede un cristal prea mare: ppm trebuie coborât."""
    return p0 - offset_hz / freq_hz * 1e6


def gsm_channel_powers(iq, fs=None, n=2048, half=3):
    """Pentru cele 2*half+1 canale de 200 kHz din fereastră (centrate pe centrul ferestrei): raportul semnal/zgomot în dB."""
    fs = fs or SDR_RATE
    m = len(iq) // n
    if m == 0:
        return [0.0] * (2 * half + 1)
    P = (np.abs(np.fft.fft(iq[:m * n].reshape(m, n) * np.hanning(n), axis=1)) ** 2).mean(axis=0)
    P = np.fft.fftshift(P)
    df = fs / n
    width = int(round(160e3 / df))
    floor = float(np.percentile(10 * np.log10(P[int(n * 0.1):int(n * 0.9)] + 1e-20), 20)) + 10 * math.log10(width)
    out = []
    for j in range(-half, half + 1):
        c = n // 2 + j * 200e3 / df
        lo = int(round(c - 80e3 / df))
        out.append(10 * math.log10(P[lo:lo + width].sum() + 1e-20) - floor)
    return out


def gsm_fcch_tones(iq, fs=None):
    """Caută burst-urile FCCH (ton pur, ~0,55 ms) și întoarce frecvența fiecărui ton, în Hz față de centrul ferestrei."""
    fs = fs or SDR_RATE
    n, hop = 1024, 256
    L = len(iq)
    if L < 8 * n:
        return []
    df = fs / n
    win = np.hanning(n).astype(np.float32)
    band_bins = np.arange(int(-40e3 / df), int(175e3 / df) + 1)          # unde poate cădea tonul (eroare până la ±100 kHz)
    broad_idx = np.arange(int(-300e3 / df), int(300e3 / df) + 1) % n
    band_idx = band_bins % n
    starts = np.arange(0, L - n, hop)
    ratio = np.zeros(len(starts), np.float32)
    peak_hz = np.zeros(len(starts), np.float32)
    ar = np.arange(n)
    for c0 in range(0, len(starts), 1024):
        st = starts[c0:c0 + 1024]
        F = np.fft.fft(iq[st[:, None] + ar[None, :]] * win, axis=1)
        P = F.real ** 2 + F.imag ** 2
        Pb = P[:, band_idx]
        pk = Pb.argmax(axis=1)
        cols = (band_bins[pk][:, None] + np.arange(-2, 3)[None, :]) % n   # tonul ocupă ~5 bin-i (fereastra Hann)
        tone = P[np.arange(len(st))[:, None], cols].sum(axis=1)
        ratio[c0:c0 + len(st)] = tone / (P[:, broad_idx].sum(axis=1) + 1e-20)
        peak_hz[c0:c0 + len(st)] = band_bins[pk] * df
    hit = np.flatnonzero(ratio >= 0.35)                    # tonul concentrează >35% din putere; datele GMSK au sub ~10%
    if len(hit) == 0:
        return []
    events, cur = [], [hit[0]]
    for i in hit[1:]:
        if i - cur[-1] <= 3:
            cur.append(i)
        else:
            events.append(cur)
            cur = [i]
    events.append(cur)
    tones = []
    for ev in events:
        if len(ev) < 2:
            continue
        w = ratio[ev].astype(np.float64)
        centre = int(round(float(np.sum((starts[ev] + n / 2) * w) / w.sum())))
        a, b = centre - 350, centre + 350
        if a < 0 or b > L:
            continue
        fc = float(np.median(peak_hz[ev]))
        t = np.arange(b - a)
        y = np.convolve(iq[a:b] * np.exp(-2j * np.pi * fc * t / fs), np.ones(64) / 64, "valid")   # îngustează la ~±9 kHz
        ph = np.unwrap(np.angle(y))
        k = np.arange(len(ph))
        slope, icpt = np.polyfit(k, ph, 1)
        if np.sqrt(np.mean((ph - (slope * k + icpt)) ** 2)) > 0.5:      # tonul nu e curat (interferență)
            continue
        delta = slope * fs / (2 * np.pi)
        if abs(delta) > 3e3:
            continue
        tones.append(fc + delta)
    return tones


def gsm_fcch_estimate(iq, fs=None):
    """Frecvența tonului FCCH, robustă: {freq, std, n} sau None dacă nu sunt suficiente burst-uri."""
    tones = np.asarray(gsm_fcch_tones(iq, fs), np.float64)
    if len(tones) < 6:
        return None
    med = float(np.median(tones))
    kept = tones[np.abs(tones - med) < 1000.0]
    if len(kept) < 6:
        return None
    return {"freq": float(np.median(kept)), "std": float(np.std(kept)), "n": int(len(kept))}


def carrier_offset(iq, search_hz, fs=None, n=16384):
    """Poziția (Hz față de centru) a celei mai puternice purtătoare înguste din ±search_hz, sau None."""
    fs = fs or SDR_RATE
    m = len(iq) // n
    if m == 0:
        return None
    P = (np.abs(np.fft.fft(iq[:m * n].reshape(m, n) * np.hanning(n), axis=1)) ** 2).mean(axis=0)
    P = np.fft.fftshift(P)
    df = fs / n
    c = n // 2
    r = int(search_hz / df)
    seg = P[c - r:c + r + 1]
    k = int(np.argmax(seg))
    if k < 2 or k > len(seg) - 3:
        return None
    wide = P[int(n * 0.1):int(n * 0.9)]
    if 10 * math.log10(seg[k] / (np.median(wide) + 1e-20)) < 15.0:        # nu se desprinde din zgomot
        return None
    if seg[k - 2:k + 3].sum() / (seg.sum() + 1e-20) < 0.15:               # prea lată: nu e o purtătoare îngustă
        return None
    la, lb, lc = (math.log(seg[k + d] + 1e-30) for d in (-1, 0, 1))
    denom = la - 2 * lb + lc
    shift = 0.5 * (la - lc) / denom if denom != 0 else 0.0               # interpolare parabolică pe logaritm
    return (k - r + shift) * df


def run_ppm_calibration(eng, source, ref_mhz, p0, cancel, report):
    """Rulează calibrarea pe firul de control. `eng.capture_iq` dă eșantioane brute. Întoarce un dicționar cu rezultatul
    sau ridică RuntimeError cu un mesaj localizat."""
    def stop():
        return cancel is not None and cancel.is_set()

    if source == "manual":
        f = float(ref_mhz)
        report(_L("cal_meas_manual", f), 0.2)
        iq = eng.capture_iq(f * 1e6, 20, cancel)
        if iq is None:
            raise RuntimeError(_L("cal_cancelled") if stop() else _L("cal_err_capture"))
        off = carrier_offset(iq, min(700e3, CAL_MAX_PPM * f), None)
        if off is None:
            raise RuntimeError(_L("cal_err_nocarrier", f))
        ppm = ppm_from_offset(p0, off, f * 1e6)
        return {"ppm": ppm, "p0": p0, "channels": [{"mhz": f, "ppm": ppm, "n": 1, "std": 0.0}]}

    lo, hi = GSM_BANDS[source]
    centres = list(np.arange(lo + 0.6, hi - 0.6 + 1e-9, 1.4))
    if centres[-1] + 0.6 < hi - 1e-6:
        centres.append(hi - 0.6)
    cand = {}
    for i, c in enumerate(centres):
        if stop():
            raise RuntimeError(_L("cal_cancelled"))
        report(_L("cal_scan", i + 1, len(centres)), 0.4 * i / len(centres))
        iq = eng.capture_iq(c * 1e6, 2, cancel)
        if iq is None:
            raise RuntimeError(_L("cal_cancelled") if stop() else _L("cal_err_capture"))
        for j, snr in zip(range(-3, 4), gsm_channel_powers(iq)):
            mhz = round(c + 0.2 * j, 1)
            if lo - 1e-6 <= mhz <= hi + 1e-6 and snr > cand.get(mhz, -99.0):
                cand[mhz] = snr
    ranked = [m for m, s in sorted(cand.items(), key=lambda kv: -kv[1]) if s >= 8.0][:8]
    results = []
    for i, mhz in enumerate(ranked):
        if stop():
            raise RuntimeError(_L("cal_cancelled"))
        report(_L("cal_meas", mhz, i + 1, len(ranked)), 0.4 + 0.6 * i / max(1, len(ranked)))
        iq = eng.capture_iq(mhz * 1e6, 33, cancel)
        if iq is None:
            raise RuntimeError(_L("cal_cancelled") if stop() else _L("cal_err_capture"))
        est = gsm_fcch_estimate(iq)
        if est is None:
            continue
        ppm = ppm_from_offset(p0, est["freq"] - FCCH_OFFSET_HZ, mhz * 1e6 + FCCH_OFFSET_HZ)
        if abs(ppm - p0) <= CAL_MAX_PPM:
            results.append({"mhz": mhz, "ppm": ppm, "n": est["n"], "std": est["std"]})
        if len(results) >= 3:
            break
    if not results:
        raise RuntimeError(_L("cal_err_nogsm"))
    return {"ppm": float(np.median([r["ppm"] for r in results])), "p0": p0, "channels": results}



# ============================================================================
class Engine:
    def __init__(self):
        self.sdr = None
        self.freq = 98.3
        self.demod_mode = "fm"          # "fm" | "am" | "nfm"
        self.squelch_db = 12.0
        self.squelch_auto = False
        self.auto_sql_db = None
        self._auto_n = 0
        self._auto_vals = []
        self._auto_base = 0.0
        self._auto_prior = 0.0
        self.audio_sink = None          # None = ieșirea implicită; altfel numele sink-ului PipeWire
        self.decode_packets = False
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
        self.am_demod = AmDemod()
        self.nfm_demod = NfmDemod()
        self.ssb_demod = SsbDemod()
        self._tuner_type = 5
        self.hf_override = "auto"         # "auto" | "direct" | "native" | "off" (din configurare)
        self.hf_mode = None             # cum recepționează dongle-ul HF (detectat la deschidere)
        self.device_label = ""
        self.bw_khz = dict(BW_DEFAULT)  # lățimea benzii de recepție pe moduri (kHz)
        self.bank = DecoderBank()
        self.dtmf = DtmfDecoder()
        self.wf_enabled = False         # cascadă: calculată doar cât e bifată
        self.wf_fft = WF_RES[WF_DEFAULT_RES]
        self.wf_rate = WF_SPEEDS[WF_DEFAULT_SPEED]
        self.wf_q = queue.Queue(maxsize=240)    # (frecvență centrală MHz, lățime MHz, rând dB)
        self._wf_acc = None
        self._wf_cnt = 0
        self._wf_due = 0.0
        self._wf_win = {}
        self.ppm = 0                    # corecția cristalului (ppm), aplicată la deschidere și la fiecare schimbare
        self._cap_blocks = []           # captură brută pentru calibrare (mode == "capture")
        self._cap_need = 0
        self._cap_done = threading.Event()
        self._bank_q = queue.Queue(maxsize=6)
        self._bank_flush = False
        self._last_decode_t = 0.0
        self.decoded_msgs = queue.Queue()
        self.raw_q = queue.Queue(maxsize=30)
        self.audio_q = queue.Queue(maxsize=10)
        self.skip = 0
        self._squelch_state = False
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

    def effective_squelch_db(self):
        """Pragul folosit efectiv: cel automat (dacă e activ și măsurat) sau cel de pe slider."""
        if self.squelch_auto and self.demod_mode in LISTEN_MODES and self.auto_sql_db is not None:
            return self.auto_sql_db
        return self.squelch_db

    @property
    def squelch_open(self):
        thr = self.effective_squelch_db()
        if self._squelch_state:
            self._squelch_state = self.level_db >= (thr - 2.0)
        else:
            self._squelch_state = self.level_db >= thr
        return self._squelch_state

    # --- squelch automat ----------------------------------------------------
    def set_squelch_auto(self, flag):
        self.squelch_auto = bool(flag)
        self._auto_reset()

    def _half_bw_hz(self, mode):
        return self.bw_khz.get(bw_key(mode), 25.0) * 500.0

    def _ch_offset_hz(self):
        """Unde stă canalul față de frecvența acordată: SSB are banda deasupra (USB) sau dedesubt (LSB)."""
        if self.demod_mode == "usb":
            return self.bw_khz["ssb"] * 500.0
        if self.demod_mode == "lsb":
            return -self.bw_khz["ssb"] * 500.0
        return 0.0

    @property
    def tuner_type(self):
        s = self.sdr
        if s is not None:
            self._tuner_type = s.tuner_type
        return self._tuner_type

    def set_bandwidth(self, mode, khz):
        """Lățimea benzii de recepție (kHz, totală) pentru un mod. Sigur de apelat din orice fir: filtrele se
        reproiectează de către firul de demodulare, la următorul bloc."""
        lo, hi = BW_RANGE[mode]
        self.bw_khz[mode] = max(lo, min(hi, float(khz)))
        {"fm": self.demod, "am": self.am_demod, "nfm": self.nfm_demod, "ssb": self.ssb_demod}[mode].set_bw(self.bw_khz[mode] * 1e3)
        if mode == bw_key(self.demod_mode) and mode != "fm":
            self._auto_reset()                  # pragul automat de squelch depinde de lățimea canalului

    def _auto_reset(self):
        """Repornește măsurarea zgomotului. Pornește de la valoarea teoretică a nivelului fără semnal
        (lățimea canalului în bin-uri FFT), apoi o înlocuiește cu ce se măsoară pe frecvența curentă."""
        self._auto_prior = noise_prior_db(self.demod_mode, self._half_bw_hz(self.demod_mode))
        self._auto_n = 0
        self._auto_vals = []
        self._auto_base = self._auto_prior + 4.0
        self.auto_sql_db = max(1.0, min(50.0, self._auto_base + AUTO_SQL_MARGIN))

    def _auto_squelch_update(self):
        """Urmărește zgomotul de fond: coboară repede cu el, urcă încet și doar cât squelch-ul e închis,
        ca o emisiune lungă (ex. ATIS) să nu ridice pragul peste ea."""
        lv = self.level_db
        n = self._auto_n
        self._auto_n = n + 1
        if n < AUTO_SQL_SETTLE:
            return
        if n < AUTO_SQL_SETTLE + AUTO_SQL_WARM:
            self._auto_vals.append(lv)
            if n == AUTO_SQL_SETTLE + AUTO_SQL_WARM - 1:
                vals = sorted(self._auto_vals)
                self._auto_base = min(vals[len(vals) // 2], self._auto_prior + 6.0)
        else:
            b = self._auto_base
            if lv < b:
                b += 0.3 * (lv - b)
            elif not self._squelch_state:
                b += 0.02 * (lv - b)
            self._auto_base = b
        self.auto_sql_db = max(1.0, min(50.0, self._auto_base + AUTO_SQL_MARGIN))

    # --- pornire / oprire ---------------------------------------------------
    def open(self, gain="auto", force=False):
        if self.sdr is not None:
            return
        if not HAS_NUMPY:
            raise RuntimeError(_L("err_no_numpy"))
        if not shutil.which("rtl_tcp"):
            raise RuntimeError(_L("err_no_rtl_tcp"))

        self.audio_device = resolve_pipewire_device()
        self.guard.detach(force=force)
        try:
            sdr = RtlTcpSdr()
            self.hf_mode = detect_hf_mode(sdr.tuner_type, sdr.log_text, self.hf_override)
            self.device_label = parse_device_label(sdr.log_text)
            sdr.hf_direct = self.hf_mode == "direct"
            try:
                sdr.sample_rate = SDR_RATE
                if self.ppm:
                    sdr.ppm = self.ppm
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
            for f in (self._reader, self._demod, self._audio, self._bank_worker)
        ]
        for t in self._threads:
            t.start()

    def close(self):
        try:
            self.stop_recording()
        except Exception:
            pass
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
                self.error = _L("err_gain", e)

    def set_ppm(self, ppm):
        self.ppm = int(ppm)
        if self.sdr is not None:
            try:
                self.sdr.ppm = self.ppm
            except Exception as e:
                self.error = _L("err_ppm", e)
                return
            self._drain()                        # librtlsdr retunează după schimbare: ignorăm blocurile de tranziție
            self.skip = 3

    def tune(self, mhz, audio=None, demod_mode=None):
        if abs(mhz - self.freq) > 1e-6:
            self.stop_recording()                # post nou: se salvează înregistrarea curentă
        self.freq = mhz
        if demod_mode is not None:
            self.demod_mode = demod_mode
        if audio is not None:
            self.audio_enabled = audio
        self.mode = "listen"
        if self.sdr is None:
            return
        try:
            self.sdr.center_freq = mhz * 1e6
        except Exception as e:
            self.error = _L("err_tune", e)
            return
        self._drain()
        self.skip = 4
        self.reset_ack.clear()
        self.need_reset = True
        self.reset_ack.wait(0.6)

    def _drain(self):
        for q in (self.raw_q, self.audio_q, self._bank_q, self.wf_q):
            try:
                while True:
                    q.get_nowait()
            except queue.Empty:
                pass

    def _reset_states(self):
        self._squelch_state = False
        self._wf_acc = None
        self.demod.reset()
        self.am_demod.reset()
        self.nfm_demod.reset()
        self.ssb_demod.reset()
        self.dtmf.reset()
        self.rds.reset()
        self._auto_reset()

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
                self.error = _L("err_sdr", e)

    def _demod(self, sdr, ev):
        while not ev.is_set():
            try:
                x = self.raw_q.get(timeout=0.1)
            except queue.Empty:
                x = None
            if self.need_reset:
                try:
                    self._reset_states()
                except Exception as e:
                    self.error = _L("err_proc", e)
                finally:                        # altfel firul moare sau tune() așteaptă degeaba
                    self.need_reset = False
                    self.reset_ack.set()
            if x is None:
                continue
            if self.skip > 0:
                self.skip -= 1
                continue
            try:
                if self.mode == "capture":      # calibrare: doar adunăm eșantioane brute, fără demodulare
                    self._cap_blocks.append(x.astype(np.complex64))
                    if len(self._cap_blocks) >= self._cap_need:
                        self._cap_done.set()
                    continue
                pw = _mean_power(x)
                if self.mode != "scan" and self.demod_mode in LISTEN_MODES:
                    P = _psd(x)
                    if len(P) > 0:
                        hb = self._half_bw_hz(self.demod_mode)
                        ch_db = channel_db(P, self._ch_offset_hz(), half_bw=hb)
                        floor_db = 10.0 * math.log10(_percentile_10(P) + 1e-20)
                        sig_db = max(0.0, min(50.0, ch_db - floor_db))
                    else:
                        sig_db = 0.0
                else:
                    sig_db = 10.0 * math.log10(pw + 1e-12)
                self.level_db = 0.6 * self.level_db + 0.4 * sig_db
                if self.squelch_auto and self.mode != "scan" and self.demod_mode in LISTEN_MODES:
                    self._auto_squelch_update()
                if self.mode == "scan":
                    self._scan_acc.append(_psd(x))
                    if len(self._scan_acc) >= 2:
                        self._scan_done.set()
                else:
                    self._feed_bank(x)
                    self._listen_block(x)
                    if self.wf_enabled and (self.demod_mode == "fm" or self.demod_mode in LISTEN_MODES):
                        self._feed_waterfall(x)
            except Exception as e:
                self.error = _L("err_proc", e)

    def bank_status(self):
        return self.bank.status()

    def reset_decoders(self):
        self._bank_flush = True
        self.dtmf.reset()

    def _feed_bank(self, x):
        if self.decode_packets and self.demod_mode in ("am", "nfm"):
            try:
                self._bank_q.put_nowait((x, self.freq, self.demod_mode))
            except queue.Full:
                pass

    def _wf_power(self, x, n):
        """Spectrul de putere mediat pe segmente de n puncte (None dacă blocul e prea scurt)."""
        m = len(x) // n
        if m == 0:
            return None
        x = x - x.mean()
        win = self._wf_win.get(n)
        if win is None:
            win = self._wf_win[n] = np.hanning(n)
        return (np.abs(np.fft.fft(x[:m * n].reshape(m, n) * win, axis=1)) ** 2).mean(axis=0)

    def _wf_emit(self, P):
        n = len(P)
        P = np.fft.fftshift(P)
        edge = int(n * WF_EDGE)
        row = (10.0 * np.log10(P[edge:n - edge] + 1e-20)).astype(np.float32)
        df = SDR_RATE / n / 1e6                                 # lățimea unui bin (MHz)
        left = (edge - n / 2.0 - 0.5) * df                      # marginea stângă a primului bin, față de frecvența acordată
        try:
            self.wf_q.put_nowait((self.freq, len(row) * df, row, left))
        except queue.Full:
            pass

    def _feed_waterfall(self, x):
        """Emite rânduri de spectru: sub 15/s mediază blocurile primite, peste 15/s împarte fiecare bloc."""
        n = self.wf_fft
        parts = int(round(self.wf_rate / WF_BLOCK_RATE))
        if parts > 1:
            self._wf_acc = None
            step = len(x) // parts
            for k in range(parts):
                P = self._wf_power(x[k * step:(k + 1) * step], n)
                if P is not None:
                    self._wf_emit(P)
            return
        P = self._wf_power(x, n)
        if P is None:
            return
        if self._wf_acc is None or len(self._wf_acc) != n:
            self._wf_acc, self._wf_cnt = P, 1
        else:
            self._wf_acc += P
            self._wf_cnt += 1
        now = time.time()
        if now < self._wf_due:
            return
        period = 1.0 / max(0.5, self.wf_rate)
        self._wf_due += period
        if self._wf_due < now - period:             # după o pauză: nu emite rafale de rânduri
            self._wf_due = now
        P, self._wf_acc, self._wf_cnt = self._wf_acc / self._wf_cnt, None, 0
        self._wf_emit(P)

    def _bank_worker(self, sdr, ev):
        """Decodare în fundal (ACARS, APRS...) pe canalele din jurul frecvenței acordate."""
        while not ev.is_set():
            try:
                x, freq, mode = self._bank_q.get(timeout=0.2)
            except queue.Empty:
                continue
            if self._bank_flush:
                self._bank_flush = False
                self.bank.reset()
            try:
                for item in self.bank.process(x, freq, mode):
                    self._last_decode_t = time.time()
                    self.decoded_msgs.put(item)
            except Exception:
                self.bank.reset()

    def _analyze_audio(self, samples):
        """DTMF pe audio-ul ascultat (fără afișarea mesajelor nedecodate)."""
        try:
            mono = (self.am_demod.raw if self.demod_mode == "am" else samples[:, 0])
            items = []
            if self.demod_mode == "nfm":
                items += self.dtmf.feed(mono, self.freq)
            for it in items:
                self._last_decode_t = time.time()
                self.decoded_msgs.put(it)
        except Exception:
            pass

    def _listen_block(self, x):
        if not self.audio_enabled:
            if self.demod_mode == "fm" and self.rds_enabled and HAS_RDS_DEPS:
                self.rds.feed(self.demod.discriminate(x))
            return
        try:
            if self.demod_mode == "am":
                samples = self.am_demod.audio(x, squelch_open=self.squelch_open)
                if not self.squelch_open:
                    samples = np.zeros_like(samples)
            elif self.demod_mode == "nfm":
                samples = self.nfm_demod.audio(x, squelch_open=self.squelch_open)
                if not self.squelch_open:
                    samples = np.zeros_like(samples)
            elif self.demod_mode in ("usb", "lsb"):
                samples = self.ssb_demod.audio(x, upper=(self.demod_mode == "usb"), squelch_open=self.squelch_open)
            else:
                d = self.demod.discriminate(x)
                if self.rds_enabled and HAS_RDS_DEPS:
                    self.rds.feed(d)
                samples = self.demod.audio(d)
            if self.decode_packets and self.demod_mode in ("am", "nfm"):
                self._analyze_audio(samples)
            self.audio_q.put_nowait(samples)
        except queue.Full:
            pass

    def _audio(self, sdr, ev):
        if not shutil.which("aplay"):
            self.error = _L("err_no_aplay")
            return
        while not ev.is_set():
            out = None
            sink = self.audio_sink
            try:
                out = AplayOutput(self.audio_device or resolve_pipewire_device(), sink)
                while not ev.is_set():
                    if not out.alive:
                        raise RuntimeError(_L("err_aplay_stopped"))
                    if self.audio_sink != sink:         # s-a ales altă ieșire: redeschide redarea
                        break
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
                    self.error = _L("err_audio", out.last_error(str(e)) if out else e)
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
            raise RuntimeError(_L("err_nothing_playing"))
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

    # --- scanare FM ---------------------------------------------------------
    def capture_iq(self, center_hz, blocks, cancel=None):
        """Retunează și întoarce `blocks` blocuri IQ brute (complex64) sau None (anulat / fără date).
        Lasă motorul în modul "capture": cine apelează trebuie să revină la "listen"."""
        if not self.running:
            return None
        self._cap_blocks = []
        self._cap_need = blocks
        self._cap_done.clear()
        self.mode = "capture"
        self.sdr.center_freq = center_hz
        self._drain()
        self.skip = 2
        deadline = time.time() + 3.0 + blocks / 15.0 * 2
        while not self._cap_done.is_set():
            if (cancel is not None and cancel.is_set()) or time.time() > deadline:
                return None
            self._cap_done.wait(0.05)
        return np.concatenate(self._cap_blocks[:blocks])

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

    # --- scanare continuă pentru Aviație / Radioamatori ---------------------
    def scan_window_step(self, start_mhz, end_mhz, step_mhz, half_bw_hz, thr_db, cancel, pace_sleep=0.03):
        """Măsoară o fereastră de ~1.5 MHz și întoarce lista de frecvențe (MHz) peste prag."""
        if not self.running or cancel.is_set():
            return []
        span_mhz = 1.5
        centre_mhz = min(end_mhz - 0.1, start_mhz + span_mhz * 0.5)
        centre_hz = centre_mhz * 1e6
        P = self.measure_window(centre_hz, cancel=cancel)
        if cancel.is_set() or P is None or len(P) == 0:
            return []
        lo_f = max(start_mhz, centre_mhz - span_mhz * 0.5)
        hi_f = min(end_mhz, centre_mhz + span_mhz * 0.5)
        n_steps = max(1, int(math.floor((hi_f - lo_f + 1e-9) / step_mhz)))
        chans = []
        for i in range(n_steps + 1):
            f = round(lo_f + i * step_mhz, 4)
            if f > end_mhz + 1e-6:
                break
            chans.append((f, channel_db(P, f * 1e6 - centre_hz, half_bw=half_bw_hz)))
        if not chans:
            return []
        floor = _percentile_10([c[1] for c in chans])
        freqs = [c[0] for c in chans]
        excess = [c[1] - floor for c in chans]
        if pace_sleep > 0 and not cancel.is_set():
            cancel.wait(pace_sleep)
        return detect_peaks(freqs, excess, thr_db)


# ============================================================================
#  8. TEXTE INTERFAȚĂ (I18N)
# ============================================================================
I18N = {
    "ro": {
        "tuning": "Acordare & Control",
        "tuning_air_ham": "Acordare Fină & Marcaje",
        "audio_sdr": "Audio & SDR",
        "warning": "",
        "freq": "Frecvență:",
        "prev": "Precedent",
        "go": "Go!",
        "next": "Următor",
        "prev_mark": "Marcaj ant.",
        "next_mark": "Marcaj urm.",
        "clear_marks": "Curăță marcaje",
        "band_lbl": "Bandă:",
        "squelch_lbl": "Squelch",
        "view_msgs": "Mesaje",
        "wf_wait": "Fără date (scanare sau oprit)",
        "tip_view_switch": "Ce se afișează în zona de jos:\nstânga = mesaje decodate (ACARS, APRS, DTMF),\ndreapta = cascadă (spectrul radio).\nClic pe întrerupător sau pe text.",
        "waterfall": "Cascadă",
        "wf_title": "Spectru RF",
        "wf_res": "Rezoluție:",
        "wf_speed": "Viteză:",
        "wf_sens": "Sensibilitate:",
        "tip_wf_sens": "Sensibilitatea culorilor:\n• Mai mare (+): apar mai multe culori, se văd și semnalele slabe.\n• Mai mică (−): fundalul rămâne gri, se văd doar semnalele puternice.\nSe aplică imediat și pe imaginea deja desenată.",
        "err_ppm": "Corecția ppm: {0}",
        "ppm_lbl": "Corecție ppm",
        "ppm_none": "fără corecție",
        "ppm_effect": "deplasare ≈ {0:+.2f} kHz la {1:.3f} MHz",
        "tip_ppm": "Valoarea corecției cristalului dongle-ului, în părți per milion (ppm).\nDongle-urile ieftine au 20–100 ppm eroare (la 433 MHz: 9–43 kHz!);\ncele cu TCXO (RTL-SDR Blog V3/V4) sunt aproape de 0.\nApasă butonul „Corecție ppm” (din stânga câmpului) ca s-o afli automat.\nSe aplică imediat (valori întregi, −200…+200).\nEfectul apare sub rândul de informații.",
        "tip_cal": "Corecție ppm — clic: pornește asistentul de calibrare.\nMăsoară automat eroarea cristalului cu ajutorul stațiilor GSM\nsau al unei purtătoare cunoscute și îți propune valoarea corectă.\nValoarea ajunge în câmpul din dreapta, după „Aplică”.",
        "unsupported_long": "Nesuportat de dongle-ul tău ({0}: {1} MHz)",
        "unsupported_short": "Nesuportat de dongle",
        "unsupported_hf": "HF (sub 24 MHz) cere RTL-SDR Blog V3 (direct sampling) sau V4",
        "hf_direct_note": "HF (sub 24 MHz): direct sampling activ (RTL-SDR Blog V3)",
        "tip_out_lock": "Ieșire audio — clic: blochează lista de dispozitive\n(devine inactivă, gri), ca să nu schimbi dispozitivul\naudio din greșeală. Clic din nou pentru a o debloca.",
        "bw_lbl": "Filtru",
        "bw_custom": "Personal",
        "tip_bw_preset": "Lățimea filtrului de recepție (banda demodulată).\nPresetări pentru modul curent: WFM (radio FM), AM, NFM, SSB.\n„Personal” = scrii tu valoarea, în kHz, în câmpul din dreapta.\nActiv doar când filtrul nu e blocat pe valoarea recomandată.",
        "tip_bw_val": "Lățimea totală a benzii de recepție, în kHz.\nMai îngust = mai puține interferențe de la canalele vecine,\ndar sunet mai înfundat dacă semnalul e deplasat în frecvență.\nO poți regla și trăgând chenarul portocaliu din cascadă.\nActiv doar când filtrul nu e blocat.",
        "cal_title": "Calibrare frecvență (ppm)",
        "cal_intro": "Măsoară eroarea cristalului dongle-ului folosind stații GSM (semnalul FCCH are ceas foarte precis) sau o purtătoare cunoscută. Antena trebuie să fie conectată; durează 30–60 s, iar radioul e folosit de asistent cât timp rulează.",
        "cal_src": "Sursă:",
        "cal_src_gsm900": "GSM 900 (925–960 MHz)",
        "cal_src_gsm850": "GSM 850 (869–894 MHz)",
        "cal_src_manual": "Purtătoare cunoscută (manual)",
        "cal_ref": "Frecvență exactă (MHz):",
        "cal_start": "Pornește",
        "cal_stop": "Oprește",
        "cal_apply": "Aplică",
        "cal_close": "Închide",
        "cal_scan": "Caut canale GSM… {0}/{1}",
        "cal_meas": "Măsor canalul {0:.1f} MHz ({1}/{2})…",
        "cal_meas_manual": "Măsor purtătoarea de la {0:.4f} MHz…",
        "cal_result": "Corecție recomandată: {0:+d} ppm (acum: {1:+d} ppm).",
        "cal_detail": "• {0:.1f} MHz: {1:+.1f} ppm ({2} burst-uri, σ = {3:.0f} Hz)",
        "cal_one_channel": "Un singur canal a fost util, deci rezultatul e mai puțin sigur. După „Aplică”, rulează din nou pentru verificare.",
        "cal_applied": "Aplicat. Pentru verificare, rulează din nou: recomandarea trebuie să rămână la fel (±1 ppm), iar diferența față de corecția actuală să fie aproape de 0.",
        "cal_residual": "Diferență față de corecția actuală: {0:+.1f} ppm (după „Aplică” ar trebui să fie aproape de 0).",
        "cal_err_capture": "Nu am primit semnal de la dongle.",
        "cal_err_nogsm": "Nu am găsit canale GSM cu semnal FCCH. Încearcă cealaltă bandă GSM, o antenă mai bună sau metoda manuală.",
        "cal_err_nocarrier": "Nu am găsit o purtătoare îngustă la {0:.4f} MHz. Verifică frecvența și că semnalul e o purtătoare stabilă, nemodulată.",
        "cal_err_radio": "Radioul nu a putut porni.",
        "cal_err_ref": "Introdu frecvența de referință în MHz (între 24 și 1700).",
        "cal_cancelled": "Oprit.",
        "wf_zoom": "Zoom:",
        "wf_peak": "Vârfuri",
        "tip_wf_zoom": "Mărește zona din jurul frecvenței acordate.\nPoți folosi și rotița mouse-ului pe cascadă.\nLa zoom mare alege o rezoluție mai fină.",
        "tip_wf_peak": "Păstrează pe linia de spectru maximul atins de fiecare\nfrecvență (linie portocalie), ca să vezi transmisiile scurte.\n„Curăță” le șterge.",
        "tip_waterfall": "Cascadă (waterfall): spectrul radio din jurul frecvenței acordate,\nderulat în timp, în locul mesajelor recepționate.\nClic pe cascadă = acordare pe acea frecvență.",
        "tip_wf_res": "Rezoluția spectrului (lățimea unui bin FFT):\n• Mai mică (ex. 0.47 kHz): detalii fine, mai mult zgomot.\n• Mai mare (ex. 3.75 kHz): imagine mai netedă.",
        "tip_wf_speed": "Viteza de derulare (rânduri pe secundă):\n• Mai lent: rândurile sunt mediate, imagine mai curată.\n• Mai rapid: urmărești transmisiile scurte.",
        "hold_on": "HOLD marcaje: ACTIV",
        "hold_off": "HOLD marcaje: scanare",
        "sql_open": "SQL: DESCHIS",
        "sql_closed": "SQL: ÎNCHIS",
        "fine_step_khz": "Pas fin: {0} kHz",
        "start": "Start",
        "stop": "Stop",
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
        "volume": "Volum",
        "audio_out_btn": "Ieșire",
        "audio_default": "Implicită (sistem)",
        "gain": "Gain",
        "scan": "Caută",
        "cancel": "Anulează",
        "threshold": "Prag (dB):",
        "delete": "Șterge",
        "add": "Adaugă canal",
        "clear": "Golește",
        "edit": "Redenumește",
        "language": "Limbă:",
        "tv_release": "Eliberează pentru TV",
        "air_ham_btn": "Mod radioamatori / SDR",
        "air_ham_back": "Înapoi la Radio FM",
        "air_title": "Aviație (AM • 118.0–137.0 MHz)",
        "scan_toggle": "Scanează",
        "msgs_title": "Mesaje recepționate",
        "msgs_clear": "Curăță",
        "msgs_empty_hint": "Când apare un pachet sau mesaj decodat pe frecvență, cardul lui va apărea aici.",
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
        "air_scan_on": "Scanare continuă Aviație (118–137 MHz)...",
        "ham_scan_on": "Scanare continuă Radioamatori...",
        "band_scan_stopped": "Scanare oprită — marcajele sunt păstrate (HOLD).",
        "air_listening": "Aviație AM — marcajele sunt în HOLD.",
        "ham_listening": "Radioamatori NFM — marcajele sunt în HOLD.",
        "marks_cleared": "Marcajele de pe grafice au fost șterse.",
        "no_marks_yet": "Nu există marcaje detectate pe graficul activ.",
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
        "err_detach": "Nu pot detașa driverul DVB ({0}): {1}",
        "err_reattach": "Nu pot reatașa driverul TV ({0}): {1}",
        "err_perm": "Nu am drepturi pe dongle-ul USB. Creează /etc/udev/rules.d/99-rtlsdr.rules cu:  {0}  apoi: sudo udevadm control --reload && sudo udevadm trigger",
        "err_rtl_nomsg": "rtl_tcp s-a oprit fără mesaj",
        "err_rtl_timeout": "rtl_tcp nu a pornit la timp: {0}",
        "err_rtl_badhdr": "Răspuns neașteptat de la rtl_tcp",
        "err_rtl_stopped": "rtl_tcp s-a oprit: {0}",
        "err_stopped_short": "oprit",
        "err_no_device": "Nu am găsit niciun dispozitiv RTL-SDR. Conectează dongle-ul USB și apasă Start.",
        "err_dev_perm": "Nu am drepturi pe dispozitivul RTL-SDR (instalează regulile udev rtl-sdr.rules).",
        "err_dev_open": "Nu pot deschide dispozitivul RTL-SDR (poate fi folosit de alt program sau driver): {0}",
        "err_no_ffmpeg": "Lipsește ffmpeg (sudo apt install ffmpeg).",
        "err_ffmpeg_stopped": "ffmpeg s-a oprit",
        "err_ffmpeg_timeout": "ffmpeg nu s-a oprit la timp",
        "err_ffmpeg_code": "ffmpeg a ieșit cu codul {0}",
        "err_rec_empty": "fișierul înregistrat e gol",
        "err_no_numpy": "Lipsește numpy (sudo apt install python3-numpy).",
        "err_no_rtl_tcp": "Lipsește rtl_tcp (sudo apt install rtl-sdr).",
        "err_no_aplay": "Audio: lipsește aplay (sudo apt install alsa-utils).",
        "err_aplay_stopped": "aplay s-a oprit",
        "err_nothing_playing": "Nu se redă nimic.",
        "err_gain": "Gain: {0}",
        "err_tune": "Acordare: {0}",
        "err_sdr": "SDR: {0}",
        "err_proc": "Procesare: {0}",
        "err_audio": "Audio: {0}",
        "tip_lang": "Schimbă limba interfeței\n(Română, English, Italiano).",
        "tip_prev": "Sare la postul memorat anterior\ndin lista de canale.",
        "tip_next": "Sare la următorul post memorat\ndin lista de canale.",
        "tip_prev_mark": "Sare la marcajul de activitate anterior\nde pe graficul curent (păstrând HOLD).",
        "tip_next_mark": "Sare la următorul marcaj de activitate\nde pe graficul curent (păstrând HOLD).",
        "tip_clear_marks": "Șterge manual toate marcajele\nde activitate de pe ambele grafice.",
        "tip_squelch": "Prag de tăiere a fâșâitului (0–50 dB peste zgomot):\n• Mai jos (ex. 0–5 dB): lasă să treacă\n  și semnalele foarte slabe.\n• Mediu (ex. 10–15 dB): taie zgomotul\n  și deschide sunetul la semnal clar.\n• Mai sus (ex. 25+ dB): lasă să treacă\n  doar semnalele puternice.\nMouse deasupra + rotița mouse-ului = mută slider-ul.",
        "acars_msg": "Aeronavă {0} • etichetă {1} • bloc {2}: {3}",
        "acars_notext": "(fără text)",
        "acars_crc_bad": "⚠ CRC neverificat • ",
        "aprs_pos": "Poziție {0}{1}",
        "aprs_msg": "Mesaj pentru {0}: {1}",
        "aprs_status": "Status: {0}",
        "aprs_mice": "Poziție {0}, {1} km/h, {2}°{3}",
        "aprs_other": "Date APRS: {0}",
        "ax25_frame": "Cadru AX.25: {0}",
        "dtmf_seq": "Tonuri DTMF: {0}",
        "dig_coded": "Semnal activ {0} s care nu poate fi decodat: digital sau codat/criptat ({1})",
        "hint_vdl2": "posibil VDL Mode 2, date aeronautice digitale",
        "hint_digital": "posibil DMR, D-STAR, C4FM, TETRA, VDL sau alt mod digital",
        "tag_digital": "DIGITAL / CODAT",
        "tip_decode_pkt": "Decodare date, în fundal, fără să afecteze ce asculți:\n• ACARS (aviație, AM): 131.525, 131.725, 131.825 MHz\n  (Europa) și 131.550 MHz (global). Dacă acordezi lângă\n  ele (±0.7 MHz), le primești pe toate deodată.\n• APRS / packet AFSK 1200 Bd (radioamatori, NFM):\n  144.800 MHz (Europa), 145.825 MHz (ISS, când e activă).\n• DTMF (tonuri de apel, comenzi de repetor): oricare\n  frecvență NFM.\nSemnalele digitale sau criptate (VDL2 pe 136.975 MHz,\nDMR, D-STAR, C4FM, TETRA) nu pot fi decodate; apar în\nlistă ca „digital / codat”.",
        "tip_threshold_band": "Prag de detecție peste zgomot (dB) pentru scanarea\nacestei benzi:\n• 4–8 dB: prinde și semnale slabe, dar apar\n  mai multe marcaje false.\n• 10–12 dB: echilibrat (recomandat).\n• 15+ dB: doar semnalele puternice.",
        "bank_active": "Ascult în fundal pe: {0} MHz • sincronizări: {1} • mesaje: {2} • CRC greșit: {3}",
        "bank_none": "Nicio frecvență cunoscută în banda curentă. Acordează lângă 131.525–131.825 MHz (ACARS), pe 144.800 / 145.825 MHz (APRS) sau pe orice frecvență NFM pentru DTMF.",
        "tip_band_sel": "Alege banda de lucru: aviație, radioamatori (HF / VHF / UHF),\nunde scurte, AM comercial, Radio FM, marină, CB, PMR446...\nSub 24 MHz (HF) e nevoie de un dongle cu direct sampling\n(ex. RTL-SDR Blog V3) sau V4. Părțile pe care dongle-ul tău\nnu le poate recepționa sunt hașurate pe grafic.",
        "tip_freq_entry": "Introdu frecvența în MHz (ex: 98.3 sau 118.275)\nși apasă Enter sau butonul Mergi.",
        "tip_go": "Acordează radioul direct pe frecvența\nscrisă în căsuță.",
        "tip_nudge_down": "Scade frecvența cu un pas fin, ales după bandă:\nRadio FM 0,1 MHz · AM 1 kHz (aviație, MW, SW, CB)\nSSB 0,1 kHz · FM îngust 2,5 kHz (VHF/UHF, marină, PMR).\nPasul curent e scris sub frecvență.",
        "tip_nudge_up": "Crește frecvența cu un pas fin, ales după bandă:\nRadio FM 0,1 MHz · AM 1 kHz (aviație, MW, SW, CB)\nSSB 0,1 kHz · FM îngust 2,5 kHz (VHF/UHF, marină, PMR).\nPasul curent e scris sub frecvență.",
        "tip_start": "Pornește recepția SDR și detașează\nautomat driverul DVB pentru TV.",
        "tip_stop": "Oprește recepția SDR și redă\ndongle-ul driverului TV.",
        "tip_add": "Adaugă manual un canal nou\nîn lista de posturi.",
        "tip_gain": "Gain — clic: pornește / oprește gain-ul automat.\nApăsat (albastru) = automat; lista din dreapta e atunci inactivă.\nNeapăsat = alegi tu gain-ul manual, în dB.",
        "tip_gain_val": "Gain manual, în dB. Activ doar când butonul Gain nu e apăsat (adică nu e pe automat).",
        "tip_bw_lock": "Filtru — clic: blochează filtrul pe valoarea recomandată\npentru banda curentă (apăsat, albastru); lista și valoarea devin inactive.\nNeapăsat: alegi tu lățimea, iar alegerea se ține minte pe fiecare bandă.",
        "tip_mute": "Volum — clic: oprește sau pornește sunetul (mute).\nButonul rămâne apăsat cât sunetul e oprit.",
        "tip_volume": "Reglează volumul de redare\nprin PipeWire.\nMouse deasupra + rotița mouse-ului = mută slider-ul.",
        "tip_audio_out": "Alege dispozitivul audio PipeWire pe care\nse redă sunetul (DAC, placă audio etc.).\nSe folosește doar PipeWire.\nPoți bloca lista cu butonul „Ieșire”.",
        "tip_squelch_auto": "Squelch automat. Apasă-l ca să rămână apăsat:\nprogramul măsoară singur zgomotul de fond\nși deschide sunetul doar la semnal real,\ndeci nu mai trebuie să muți glisorul.\nApasă din nou pentru reglaj manual.",
        "tip_tv_release": "Oprește radioul și reatașează\ndriverul DVB ca să poți folosi TV.",
        "tip_air_ham": "Comută între Radio FM (posturi comerciale)\nși modul radioamatori / SDR: aviație, radioamatori,\nunde scurte, AM comercial, marină, CB etc.,\ncu grafic de bandă, scanare, cascadă și decodare mesaje.",
        "tip_scan_toggle": "Apasă pentru a scana continuu banda\n(rămâne apăsat). Apasă din nou\npentru a opri sau dă clic pe grafic.",
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
            "• Prag mai mic (5–8 dB): prinde și\n  posturi slabe, dar crește riscul de\n  fals pozitive și durează mai mult\n  filtrarea manuală.\n"
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
        "tuning_air_ham": "Fine Tuning & Markers",
        "audio_sdr": "Audio & SDR",
        "warning": "",
        "freq": "Frequency:",
        "prev": "Previous",
        "go": "Go!",
        "next": "Next",
        "prev_mark": "Prev mark",
        "next_mark": "Next mark",
        "clear_marks": "Clear marks",
        "band_lbl": "Band:",
        "squelch_lbl": "Squelch",
        "view_msgs": "Messages",
        "wf_wait": "No data (scanning or stopped)",
        "tip_view_switch": "What the bottom area shows:\nleft = decoded messages (ACARS, APRS, DTMF),\nright = waterfall (radio spectrum).\nClick the switch or a label.",
        "waterfall": "Waterfall",
        "wf_title": "RF spectrum",
        "wf_res": "Resolution:",
        "wf_speed": "Speed:",
        "wf_sens": "Sensitivity:",
        "tip_wf_sens": "Colour sensitivity:\n• Higher (+): more colour, weak signals show up.\n• Lower (−): the background stays grey, only strong signals show.\nApplies immediately, also to what is already drawn.",
        "err_ppm": "PPM correction: {0}",
        "ppm_lbl": "PPM corr.",
        "ppm_none": "no correction",
        "ppm_effect": "shift ≈ {0:+.2f} kHz at {1:.3f} MHz",
        "tip_ppm": "Dongle crystal correction value, in parts per million (ppm).\nCheap dongles are off by 20–100 ppm (at 433 MHz: 9–43 kHz!);\nTCXO ones (RTL-SDR Blog V3/V4) are close to 0.\nClick the “PPM corr.” button (left of the field) to find it automatically.\nApplied immediately (whole numbers, −200…+200).\nThe effect is shown below the info line.",
        "tip_cal": "PPM corr. — click: opens the calibration assistant.\nIt automatically measures the crystal error using GSM base stations\nor a known carrier and suggests the right value.\nThe value goes into the field on the right, after “Apply”.",
        "unsupported_long": "Not supported by your dongle ({0}: {1} MHz)",
        "unsupported_short": "Not supported by dongle",
        "unsupported_hf": "HF (below 24 MHz) needs an RTL-SDR Blog V3 (direct sampling) or V4",
        "hf_direct_note": "HF (below 24 MHz): direct sampling active (RTL-SDR Blog V3)",
        "tip_out_lock": "Audio output — click: locks the device list\n(it turns inactive, grey) so the audio device\ncan’t be changed by accident. Click again to unlock.",
        "bw_lbl": "Filter",
        "bw_custom": "Custom",
        "tip_bw_preset": "Receive filter width (the demodulated band).\nPresets for the current mode: WFM (FM radio), AM, NFM, SSB.\n“Custom” = type your own value, in kHz, in the field on the right.\nActive only when the filter is not locked to the recommended value.",
        "tip_bw_val": "Total receive bandwidth, in kHz.\nNarrower = less interference from neighbouring channels,\nbut muffled sound if the signal is off-frequency.\nYou can also set it by dragging the orange box in the waterfall.\nActive only when the filter is not locked.",
        "cal_title": "Frequency calibration (ppm)",
        "cal_intro": "Measures the dongle crystal error using GSM base stations (the FCCH signal has a very precise clock) or a known carrier. The antenna must be connected; it takes 30–60 s and the radio is used by the assistant while it runs.",
        "cal_src": "Source:",
        "cal_src_gsm900": "GSM 900 (925–960 MHz)",
        "cal_src_gsm850": "GSM 850 (869–894 MHz)",
        "cal_src_manual": "Known carrier (manual)",
        "cal_ref": "Exact frequency (MHz):",
        "cal_start": "Start",
        "cal_stop": "Stop",
        "cal_apply": "Apply",
        "cal_close": "Close",
        "cal_scan": "Looking for GSM channels… {0}/{1}",
        "cal_meas": "Measuring channel {0:.1f} MHz ({1}/{2})…",
        "cal_meas_manual": "Measuring the carrier at {0:.4f} MHz…",
        "cal_result": "Recommended correction: {0:+d} ppm (now: {1:+d} ppm).",
        "cal_detail": "• {0:.1f} MHz: {1:+.1f} ppm ({2} bursts, σ = {3:.0f} Hz)",
        "cal_one_channel": "Only one channel was usable, so the result is less certain. After “Apply”, run again to verify.",
        "cal_applied": "Applied. To verify, run again: the recommendation should stay the same (±1 ppm) and the difference from the current correction should be close to 0.",
        "cal_residual": "Difference from the current correction: {0:+.1f} ppm (after “Apply” it should be close to 0).",
        "cal_err_capture": "No signal received from the dongle.",
        "cal_err_nogsm": "No GSM channels with an FCCH signal found. Try the other GSM band, a better antenna, or the manual method.",
        "cal_err_nocarrier": "No narrow carrier found at {0:.4f} MHz. Check the frequency and that the signal is a stable, unmodulated carrier.",
        "cal_err_radio": "The radio could not start.",
        "cal_err_ref": "Enter the reference frequency in MHz (between 24 and 1700).",
        "cal_cancelled": "Stopped.",
        "wf_zoom": "Zoom:",
        "wf_peak": "Peaks",
        "tip_wf_zoom": "Magnifies the area around the tuned frequency.\nYou can also use the mouse wheel on the waterfall.\nAt high zoom pick a finer resolution.",
        "tip_wf_peak": "Keeps the maximum reached at each frequency on the spectrum\nline (orange), so short transmissions stay visible.\n“Clear” resets it.",
        "tip_waterfall": "Waterfall: the radio spectrum around the tuned frequency,\nscrolling over time, instead of the received messages.\nClick on the waterfall = tune to that frequency.",
        "tip_wf_res": "Spectrum resolution (FFT bin width):\n• Smaller (e.g. 0.47 kHz): fine detail, more noise.\n• Larger (e.g. 3.75 kHz): smoother picture.",
        "tip_wf_speed": "Scroll speed (rows per second):\n• Slower: rows are averaged, cleaner picture.\n• Faster: follow short transmissions.",
        "hold_on": "Marker HOLD: ON",
        "hold_off": "Marker HOLD: scanning",
        "sql_open": "SQL: OPEN",
        "sql_closed": "SQL: CLOSED",
        "fine_step_khz": "Fine step: {0} kHz",
        "start": "Start",
        "stop": "Stop",
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
        "volume": "Volume",
        "audio_out_btn": "Output",
        "audio_default": "Default (system)",
        "gain": "Gain",
        "scan": "Scan",
        "cancel": "Cancel",
        "threshold": "Threshold (dB):",
        "delete": "Delete",
        "add": "Add channel",
        "clear": "Clear",
        "edit": "Rename",
        "language": "Language:",
        "tv_release": "Release for TV",
        "air_ham_btn": "Amateur / SDR mode",
        "air_ham_back": "Back to FM Radio",
        "air_title": "Aviation (AM • 118.0–137.0 MHz)",
        "scan_toggle": "Scan",
        "msgs_title": "Received Messages",
        "msgs_clear": "Clear",
        "msgs_empty_hint": "When a packet or decoded message arrives on frequency, its card will show here.",
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
        "air_scan_on": "Continuous Aviation scan (118–137 MHz)...",
        "ham_scan_on": "Continuous Ham radio scan...",
        "band_scan_stopped": "Scan stopped — markers kept on HOLD.",
        "air_listening": "Aviation AM — markers on HOLD.",
        "ham_listening": "Ham NFM — markers on HOLD.",
        "marks_cleared": "Chart markers cleared.",
        "no_marks_yet": "No detected markers on the active chart.",
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
        "err_detach": "Cannot detach the DVB driver ({0}): {1}",
        "err_reattach": "Cannot reattach the TV driver ({0}): {1}",
        "err_perm": "No permission on the USB dongle. Create /etc/udev/rules.d/99-rtlsdr.rules with:  {0}  then run: sudo udevadm control --reload && sudo udevadm trigger",
        "err_rtl_nomsg": "rtl_tcp stopped without a message",
        "err_rtl_timeout": "rtl_tcp did not start in time: {0}",
        "err_rtl_badhdr": "Unexpected response from rtl_tcp",
        "err_rtl_stopped": "rtl_tcp stopped: {0}",
        "err_stopped_short": "stopped",
        "err_no_device": "No RTL-SDR device found. Plug in the USB dongle and press Start.",
        "err_dev_perm": "No permission on the RTL-SDR device (install the udev rules file rtl-sdr.rules).",
        "err_dev_open": "Cannot open the RTL-SDR device (it may be in use by another program or driver): {0}",
        "err_no_ffmpeg": "ffmpeg is missing (sudo apt install ffmpeg).",
        "err_ffmpeg_stopped": "ffmpeg stopped",
        "err_ffmpeg_timeout": "ffmpeg did not stop in time",
        "err_ffmpeg_code": "ffmpeg exited with code {0}",
        "err_rec_empty": "the recorded file is empty",
        "err_no_numpy": "numpy is missing (sudo apt install python3-numpy).",
        "err_no_rtl_tcp": "rtl_tcp is missing (sudo apt install rtl-sdr).",
        "err_no_aplay": "Audio: aplay is missing (sudo apt install alsa-utils).",
        "err_aplay_stopped": "aplay stopped",
        "err_nothing_playing": "Nothing is playing.",
        "err_gain": "Gain: {0}",
        "err_tune": "Tuning: {0}",
        "err_sdr": "SDR: {0}",
        "err_proc": "Processing: {0}",
        "err_audio": "Audio: {0}",
        "tip_lang": "Change the interface language\n(Română, English, Italiano).",
        "tip_prev": "Jump to the previous saved station\nin the channel list.",
        "tip_next": "Jump to the next saved station\nin the channel list.",
        "tip_prev_mark": "Jump to the previous activity marker\non the active chart (keeps HOLD).",
        "tip_next_mark": "Jump to the next activity marker\non the active chart (keeps HOLD).",
        "tip_clear_marks": "Manually clear all activity markers\nfrom both charts.",
        "tip_squelch": "Noise squelch threshold (0–50 dB above noise):\n• Lower (e.g. 0–5 dB): lets very weak\n  signals through.\n• Medium (e.g. 10–15 dB): mutes static\n  and opens on clear signals.\n• Higher (e.g. 25+ dB): lets through\n  only strong signals.\nHover + mouse wheel = moves the slider.",
        "acars_msg": "Aircraft {0} • label {1} • block {2}: {3}",
        "acars_notext": "(no text)",
        "acars_crc_bad": "⚠ CRC not verified • ",
        "aprs_pos": "Position {0}{1}",
        "aprs_msg": "Message to {0}: {1}",
        "aprs_status": "Status: {0}",
        "aprs_mice": "Position {0}, {1} km/h, {2}°{3}",
        "aprs_other": "APRS data: {0}",
        "ax25_frame": "AX.25 frame: {0}",
        "dtmf_seq": "DTMF tones: {0}",
        "dig_coded": "Active signal of {0} s that cannot be decoded: digital or coded/encrypted ({1})",
        "hint_vdl2": "possibly VDL Mode 2, digital aeronautical data",
        "hint_digital": "possibly DMR, D-STAR, C4FM, TETRA, VDL or another digital mode",
        "tag_digital": "DIGITAL / CODED",
        "tip_decode_pkt": "Data decoding, in the background, without affecting what you hear:\n• ACARS (aviation, AM): 131.525, 131.725, 131.825 MHz\n  (Europe) and 131.550 MHz (global). If you tune near\n  them (±0.7 MHz) you receive all of them at once.\n• APRS / AFSK 1200 Bd packet (ham radio, NFM):\n  144.800 MHz (Europe), 145.825 MHz (ISS, when active).\n• DTMF (selective-call tones, repeater commands): any\n  NFM frequency.\nDigital or encrypted signals (VDL2 on 136.975 MHz,\nDMR, D-STAR, C4FM, TETRA) cannot be decoded; they show\nup in the list as “digital / coded”.",
        "tip_threshold_band": "Detection threshold above noise (dB) for scanning\nthis band:\n• 4–8 dB: also catches weak signals, but gives\n  more false markers.\n• 10–12 dB: balanced (recommended).\n• 15+ dB: strong signals only.",
        "bank_active": "Monitoring in the background: {0} MHz • syncs: {1} • messages: {2} • bad CRC: {3}",
        "bank_none": "No known frequency in the current band. Tune near 131.525–131.825 MHz (ACARS), 144.800 / 145.825 MHz (APRS) or any NFM frequency for DTMF.",
        "tip_band_sel": "Pick the band: aviation, amateur (HF / VHF / UHF),\nshortwave, AM broadcast, FM radio, marine, CB, PMR446...\nBelow 24 MHz (HF) you need a dongle with direct sampling\n(e.g. RTL-SDR Blog V3) or a V4. Parts your dongle\ncannot receive are hatched on the chart.",
        "tip_freq_entry": "Enter frequency in MHz (e.g. 98.3 or 118.275)\nand press Enter or Tune.",
        "tip_go": "Tune the radio directly to the\nfrequency entered in the box.",
        "tip_nudge_down": "Decreases the frequency by a fine step chosen per band:\nFM radio 0.1 MHz · AM 1 kHz (aviation, MW, SW, CB)\nSSB 0.1 kHz · narrow FM 2.5 kHz (VHF/UHF, marine, PMR).\nThe current step is shown under the frequency.",
        "tip_nudge_up": "Increases the frequency by a fine step chosen per band:\nFM radio 0.1 MHz · AM 1 kHz (aviation, MW, SW, CB)\nSSB 0.1 kHz · narrow FM 2.5 kHz (VHF/UHF, marine, PMR).\nThe current step is shown under the frequency.",
        "tip_start": "Start SDR reception and automatically\ndetach the DVB TV driver.",
        "tip_stop": "Stop SDR reception and return\nthe dongle to the TV driver.",
        "tip_add": "Manually add a new channel\nto the station list.",
        "tip_gain": "Gain — click: turns automatic gain on / off.\nPressed (blue) = automatic; the list on the right is then inactive.\nNot pressed = you pick the manual gain, in dB.",
        "tip_gain_val": "Manual gain, in dB. Active only when the Gain button is not pressed (i.e. not on automatic).",
        "tip_bw_lock": "Filter — click: locks the filter to the value recommended\nfor the current band (pressed, blue); the list and value become inactive.\nNot pressed: you choose the width, and your choice is remembered per band.",
        "tip_mute": "Volume — click: mutes or unmutes the audio.\nThe button stays pressed while muted.",
        "tip_volume": "Adjust playback volume\nthrough PipeWire.\nHover + mouse wheel = moves the slider.",
        "tip_audio_out": "Pick the PipeWire audio device the sound\nis played on (DAC, sound card, etc.).\nPipeWire only.\nYou can lock the list with the “Output” button.",
        "tip_squelch_auto": "Automatic squelch. Press it so it stays pressed:\nthe program measures the background noise itself\nand opens the audio only on a real signal,\nso you no longer need to move the slider.\nPress again for manual control.",
        "tip_tv_release": "Stop the radio and reattach\nthe DVB driver for TV apps.",
        "tip_air_ham": "Switches between FM Radio (broadcast stations)\nand the amateur / SDR mode: aviation, amateur bands,\nshortwave, AM broadcast, marine, CB, etc.,\nwith band chart, scanning, waterfall and message decoding.",
        "tip_scan_toggle": "Press to scan continuously (stays\npressed). Press again to stop\nor click the chart to tune.",
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
        "tuning_air_ham": "Sintonia Fine & Marcatori",
        "audio_sdr": "Audio & SDR",
        "warning": "",
        "freq": "Frequenza:",
        "prev": "Precedente",
        "go": "Go!",
        "next": "Successivo",
        "prev_mark": "Marc. prec.",
        "next_mark": "Marc. succ.",
        "clear_marks": "Pulisci marc.",
        "band_lbl": "Banda:",
        "squelch_lbl": "Squelch",
        "view_msgs": "Messaggi",
        "wf_wait": "Nessun dato (scansione o fermo)",
        "tip_view_switch": "Cosa mostra l\'area in basso:\nsinistra = messaggi decodificati (ACARS, APRS, DTMF),\ndestra = cascata (spettro radio).\nClic sull\'interruttore o sul testo.",
        "waterfall": "Cascata",
        "wf_title": "Spettro RF",
        "wf_res": "Risoluzione:",
        "wf_speed": "Velocità:",
        "wf_sens": "Sensibilità:",
        "tip_wf_sens": "Sensibilità dei colori:\n• Più alta (+): più colore, si vedono anche i segnali deboli.\n• Più bassa (−): lo sfondo resta grigio, solo i segnali forti.\nSi applica subito, anche all\'immagine già disegnata.",
        "err_ppm": "Correzione ppm: {0}",
        "ppm_lbl": "Corr. ppm",
        "ppm_none": "nessuna correzione",
        "ppm_effect": "spostamento ≈ {0:+.2f} kHz a {1:.3f} MHz",
        "tip_ppm": "Valore della correzione del cristallo del dongle, in parti per milione (ppm).\nI dongle economici sbagliano di 20–100 ppm (a 433 MHz: 9–43 kHz!);\nquelli con TCXO (RTL-SDR Blog V3/V4) sono vicini a 0.\nPremi il pulsante “Corr. ppm” (a sinistra del campo) per trovarla automaticamente.\nSi applica subito (numeri interi, −200…+200).\nL'effetto appare sotto la riga delle informazioni.",
        "tip_cal": "Corr. ppm — clic: apre l'assistente di calibrazione.\nMisura automaticamente l'errore del cristallo usando le stazioni GSM\no una portante nota e propone il valore corretto.\nIl valore finisce nel campo a destra, dopo “Applica”.",
        "unsupported_long": "Non supportato dal tuo dongle ({0}: {1} MHz)",
        "unsupported_short": "Non supportato dal dongle",
        "unsupported_hf": "HF (sotto 24 MHz) richiede un RTL-SDR Blog V3 (direct sampling) o V4",
        "hf_direct_note": "HF (sotto 24 MHz): direct sampling attivo (RTL-SDR Blog V3)",
        "tip_out_lock": "Uscita audio — clic: blocca l\'elenco dei dispositivi\n(diventa inattivo, grigio) così il dispositivo audio\nnon cambia per errore. Clic di nuovo per sbloccarlo.",
        "bw_lbl": "Filtro",
        "bw_custom": "Person.",
        "tip_bw_preset": "Larghezza del filtro di ricezione (la banda demodulata).\nPreset per la modalità corrente: WFM (radio FM), AM, NFM, SSB.\n“Person.” = scrivi tu il valore, in kHz, nel campo a destra.\nAttivo solo quando il filtro non è bloccato sul valore consigliato.",
        "tip_bw_val": "Larghezza totale della banda di ricezione, in kHz.\nPiù stretta = meno interferenze dai canali vicini,\nma suono più ovattato se il segnale è fuori frequenza.\nPuoi regolarla anche trascinando il riquadro arancione nella cascata.\nAttivo solo quando il filtro non è bloccato.",
        "cal_title": "Calibrazione frequenza (ppm)",
        "cal_intro": "Misura l'errore del cristallo del dongle usando stazioni GSM (il segnale FCCH ha un clock molto preciso) o una portante nota. L'antenna deve essere collegata; richiede 30–60 s e la radio è usata dall'assistente mentre è in esecuzione.",
        "cal_src": "Sorgente:",
        "cal_src_gsm900": "GSM 900 (925–960 MHz)",
        "cal_src_gsm850": "GSM 850 (869–894 MHz)",
        "cal_src_manual": "Portante nota (manuale)",
        "cal_ref": "Frequenza esatta (MHz):",
        "cal_start": "Avvia",
        "cal_stop": "Ferma",
        "cal_apply": "Applica",
        "cal_close": "Chiudi",
        "cal_scan": "Cerco canali GSM… {0}/{1}",
        "cal_meas": "Misuro il canale {0:.1f} MHz ({1}/{2})…",
        "cal_meas_manual": "Misuro la portante a {0:.4f} MHz…",
        "cal_result": "Correzione consigliata: {0:+d} ppm (ora: {1:+d} ppm).",
        "cal_detail": "• {0:.1f} MHz: {1:+.1f} ppm ({2} burst, σ = {3:.0f} Hz)",
        "cal_one_channel": "È stato utile un solo canale, quindi il risultato è meno sicuro. Dopo “Applica”, ripeti per verificare.",
        "cal_applied": "Applicato. Per verificare, ripeti: il consiglio deve restare uguale (±1 ppm) e la differenza dalla correzione attuale deve essere vicina a 0.",
        "cal_residual": "Differenza dalla correzione attuale: {0:+.1f} ppm (dopo “Applica” dovrebbe essere vicina a 0).",
        "cal_err_capture": "Nessun segnale ricevuto dal dongle.",
        "cal_err_nogsm": "Nessun canale GSM con segnale FCCH trovato. Prova l'altra banda GSM, un'antenna migliore o il metodo manuale.",
        "cal_err_nocarrier": "Nessuna portante stretta trovata a {0:.4f} MHz. Controlla la frequenza e che il segnale sia una portante stabile, non modulata.",
        "cal_err_radio": "La radio non è riuscita ad avviarsi.",
        "cal_err_ref": "Inserisci la frequenza di riferimento in MHz (tra 24 e 1700).",
        "cal_cancelled": "Fermato.",
        "wf_zoom": "Zoom:",
        "wf_peak": "Picchi",
        "tip_wf_zoom": "Ingrandisce l'area attorno alla frequenza sintonizzata.\nPuoi usare anche la rotella del mouse sulla cascata.\nCon zoom alto scegli una risoluzione più fine.",
        "tip_wf_peak": "Mantiene sulla linea dello spettro il massimo raggiunto da ogni\nfrequenza (linea arancione), così le trasmissioni brevi restano visibili.\n“Pulisci” li azzera.",
        "tip_waterfall": "Cascata (waterfall): lo spettro radio attorno alla frequenza sintonizzata,\nin scorrimento nel tempo, al posto dei messaggi ricevuti.\nClic sulla cascata = sintonizza su quella frequenza.",
        "tip_wf_res": "Risoluzione dello spettro (larghezza del bin FFT):\n• Più piccola (es. 0.47 kHz): più dettaglio, più rumore.\n• Più grande (es. 3.75 kHz): immagine più liscia.",
        "tip_wf_speed": "Velocità di scorrimento (righe al secondo):\n• Più lenta: righe mediate, immagine più pulita.\n• Più veloce: segui le trasmissioni brevi.",
        "hold_on": "HOLD marcatori: ATTIVO",
        "hold_off": "HOLD marcatori: scansione",
        "sql_open": "SQL: APERTO",
        "sql_closed": "SQL: CHIUSO",
        "fine_step_khz": "Passo fine: {0} kHz",
        "start": "Avvia",
        "stop": "Ferma",
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
        "volume": "Volume",
        "audio_out_btn": "Uscita",
        "audio_default": "Predefinita (sistema)",
        "gain": "Gain",
        "scan": "Cerca",
        "cancel": "Annulla",
        "threshold": "Soglia (dB):",
        "delete": "Elimina",
        "add": "Aggiungi canale",
        "clear": "Svuota",
        "edit": "Rinominare",
        "language": "Lingua:",
        "tv_release": "Libera per TV",
        "air_ham_btn": "Modalità radioamatore / SDR",
        "air_ham_back": "Torna alla Radio FM",
        "air_title": "Aviazione (AM • 118.0–137.0 MHz)",
        "scan_toggle": "Scansiona",
        "msgs_title": "Messaggi ricevuti",
        "msgs_clear": "Pulisci",
        "msgs_empty_hint": "Quando arriva un pacchetto o un messaggio decodificato, la sua scheda apparirà qui.",
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
        "air_scan_on": "Scansione continua Aviazione (118–137 MHz)...",
        "ham_scan_on": "Scansione continua Radioamatori...",
        "band_scan_stopped": "Scansione fermata — marcatori mantenuti (HOLD).",
        "air_listening": "Aviazione AM — marcatori in HOLD.",
        "ham_listening": "Radioamatori NFM — marcatori in HOLD.",
        "marks_cleared": "Marcatori cancellati dai grafici.",
        "no_marks_yet": "Nessun marcatore rilevato sul grafico attivo.",
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
        "err_detach": "Impossibile scollegare il driver DVB ({0}): {1}",
        "err_reattach": "Impossibile ricollegare il driver TV ({0}): {1}",
        "err_perm": "Nessun permesso sulla chiavetta USB. Crea /etc/udev/rules.d/99-rtlsdr.rules con:  {0}  poi esegui: sudo udevadm control --reload && sudo udevadm trigger",
        "err_rtl_nomsg": "rtl_tcp si è fermato senza messaggio",
        "err_rtl_timeout": "rtl_tcp non si è avviato in tempo: {0}",
        "err_rtl_badhdr": "Risposta inattesa da rtl_tcp",
        "err_rtl_stopped": "rtl_tcp si è fermato: {0}",
        "err_stopped_short": "fermato",
        "err_no_device": "Nessun dispositivo RTL-SDR trovato. Collega la chiavetta USB e premi Start.",
        "err_dev_perm": "Nessun permesso sul dispositivo RTL-SDR (installa il file di regole udev rtl-sdr.rules).",
        "err_dev_open": "Impossibile aprire il dispositivo RTL-SDR (potrebbe essere usato da un altro programma o driver): {0}",
        "err_no_ffmpeg": "Manca ffmpeg (sudo apt install ffmpeg).",
        "err_ffmpeg_stopped": "ffmpeg si è fermato",
        "err_ffmpeg_timeout": "ffmpeg non si è fermato in tempo",
        "err_ffmpeg_code": "ffmpeg è terminato con codice {0}",
        "err_rec_empty": "il file registrato è vuoto",
        "err_no_numpy": "Manca numpy (sudo apt install python3-numpy).",
        "err_no_rtl_tcp": "Manca rtl_tcp (sudo apt install rtl-sdr).",
        "err_no_aplay": "Audio: manca aplay (sudo apt install alsa-utils).",
        "err_aplay_stopped": "aplay si è fermato",
        "err_nothing_playing": "Non si sta riproducendo nulla.",
        "err_gain": "Gain: {0}",
        "err_tune": "Sintonia: {0}",
        "err_sdr": "SDR: {0}",
        "err_proc": "Elaborazione: {0}",
        "err_audio": "Audio: {0}",
        "tip_lang": "Cambia la lingua dell'interfaccia\n(Română, English, Italiano).",
        "tip_prev": "Passa alla stazione salvata precedente\nnella lista canali.",
        "tip_next": "Passa alla stazione salvata successiva\nnella lista canali.",
        "tip_prev_mark": "Salta al marcatore precedente\nsul grafico attivo (mantiene HOLD).",
        "tip_next_mark": "Salta al marcatore successivo\nsul grafico attivo (mantiene HOLD).",
        "tip_clear_marks": "Cancella manualmente tutti i marcatori\nda entrambi i grafici.",
        "tip_squelch": "Soglia squelch rumore (0–50 dB sul rumore):\n• Più bassa (es. 0–5 dB): fa passare\n  anche segnali molto deboli.\n• Media (es. 10–15 dB): taglia il fruscio\n  e apre solo con segnali chiari.\n• Più alta (es. 25+ dB): fa passare\n  solo segnali forti.\nMouse sopra + rotella = sposta lo slider.",
        "acars_msg": "Aereo {0} • etichetta {1} • blocco {2}: {3}",
        "acars_notext": "(senza testo)",
        "acars_crc_bad": "⚠ CRC non verificato • ",
        "aprs_pos": "Posizione {0}{1}",
        "aprs_msg": "Messaggio per {0}: {1}",
        "aprs_status": "Stato: {0}",
        "aprs_mice": "Posizione {0}, {1} km/h, {2}°{3}",
        "aprs_other": "Dati APRS: {0}",
        "ax25_frame": "Frame AX.25: {0}",
        "dtmf_seq": "Toni DTMF: {0}",
        "dig_coded": "Segnale attivo di {0} s non decodificabile: digitale o codificato/cifrato ({1})",
        "hint_vdl2": "possibile VDL Mode 2, dati aeronautici digitali",
        "hint_digital": "possibile DMR, D-STAR, C4FM, TETRA, VDL o altro modo digitale",
        "tag_digital": "DIGITALE / CODIFICATO",
        "tip_decode_pkt": "Decodifica dati, in background, senza influire su ciò che ascolti:\n• ACARS (aviazione, AM): 131.525, 131.725, 131.825 MHz\n  (Europa) e 131.550 MHz (globale). Se sintonizzi vicino\n  (±0.7 MHz) li ricevi tutti insieme.\n• APRS / packet AFSK 1200 Bd (radioamatori, NFM):\n  144.800 MHz (Europa), 145.825 MHz (ISS, quando attiva).\n• DTMF (toni di chiamata, comandi ripetitore): qualsiasi\n  frequenza NFM.\nI segnali digitali o cifrati (VDL2 su 136.975 MHz,\nDMR, D-STAR, C4FM, TETRA) non si possono decodificare;\ncompaiono in elenco come “digitale / codificato”.",
        "tip_threshold_band": "Soglia di rilevamento sul rumore (dB) per la scansione\ndi questa banda:\n• 4–8 dB: rileva anche segnali deboli, ma più\n  marcatori falsi.\n• 10–12 dB: equilibrata (consigliata).\n• 15+ dB: solo segnali forti.",
        "bank_active": "Monitoraggio in background su: {0} MHz • sincronizzazioni: {1} • messaggi: {2} • CRC errato: {3}",
        "bank_none": "Nessuna frequenza nota nella banda corrente. Sintonizza vicino a 131.525–131.825 MHz (ACARS), 144.800 / 145.825 MHz (APRS) o su qualsiasi frequenza NFM per DTMF.",
        "tip_band_sel": "Scegli la banda: aviazione, radioamatori (HF / VHF / UHF),\nonde corte, AM commerciale, Radio FM, marina, CB, PMR446...\nSotto 24 MHz (HF) serve un dongle con direct sampling\n(es. RTL-SDR Blog V3) o un V4. Le parti che il dongle\nnon riceve sono tratteggiate sul grafico.",
        "tip_freq_entry": "Inserisci la frequenza in MHz (es. 98.3 o 118.275)\ne premi Invio o Vai.",
        "tip_go": "Sintonizza la radio direttamente sulla\nfrequenza inserita.",
        "tip_nudge_down": "Riduce la frequenza di un passo fine, scelto per banda:\nRadio FM 0,1 MHz · AM 1 kHz (aviazione, MW, SW, CB)\nSSB 0,1 kHz · FM stretta 2,5 kHz (VHF/UHF, marina, PMR).\nIl passo corrente è scritto sotto la frequenza.",
        "tip_nudge_up": "Aumenta la frequenza di un passo fine, scelto per banda:\nRadio FM 0,1 MHz · AM 1 kHz (aviazione, MW, SW, CB)\nSSB 0,1 kHz · FM stretta 2,5 kHz (VHF/UHF, marina, PMR).\nIl passo corrente è scritto sotto la frequenza.",
        "tip_start": "Avvia la ricezione SDR e scollega\nautomaticamente il driver DVB TV.",
        "tip_stop": "Ferma la ricezione SDR e ricollega\nil dongle al driver TV.",
        "tip_add": "Aggiungi manualmente un nuovo canale\nalla lista.",
        "tip_gain": "Gain — clic: attiva / disattiva il gain automatico.\nPremuto (blu) = automatico; l\'elenco a destra è allora inattivo.\nNon premuto = scegli tu il gain manuale, in dB.",
        "tip_gain_val": "Gain manuale, in dB. Attivo solo quando il pulsante Gain non è premuto (cioè non è su automatico).",
        "tip_bw_lock": "Filtro — clic: blocca il filtro sul valore consigliato\nper la banda corrente (premuto, blu); elenco e valore diventano inattivi.\nNon premuto: scegli tu la larghezza, e la scelta viene ricordata per banda.",
        "tip_mute": "Volume — clic: disattiva o riattiva l\'audio (muto).\nIl pulsante resta premuto mentre l\'audio è disattivato.",
        "tip_volume": "Regola il volume di riproduzione\ntramite PipeWire.\nMouse sopra + rotella = sposta lo slider.",
        "tip_audio_out": "Scegli il dispositivo audio PipeWire su cui\nviene riprodotto il suono (DAC, scheda audio ecc.).\nSolo PipeWire.\nPuoi bloccare l\'elenco con il pulsante “Uscita”.",
        "tip_squelch_auto": "Squelch automatico. Premilo perché resti premuto:\nil programma misura da solo il rumore di fondo\ne apre l'audio solo con un segnale reale,\nquindi non serve più muovere il cursore.\nPremi di nuovo per il controllo manuale.",
        "tip_tv_release": "Ferma la radio e ricollega\nil driver DVB per le app TV.",
        "tip_air_ham": "Passa tra Radio FM (stazioni commerciali)\ne la modalità radioamatore / SDR: aviazione, radioamatori,\nonde corte, AM commerciale, marina, CB ecc.,\ncon grafico di banda, scansione, cascata e decodifica messaggi.",
        "tip_scan_toggle": "Premi per scansionare in continuo\n(resta premuto). Premi di nuovo\nper fermare o clicca sul grafico.",
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
            "• Più bassa (5–8 dB): rileva anche\n  stazioni deboli, ma aumenta i falsi\n  positivi e la pulizia manuale.\n"
            "• Più alta (15+ dB): più rapida e\n  precisa su segnali forti, ma può\n  perdere stazioni deboli."
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
    "air_ham": "🗼",
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


class BandActivityChart(tk.Canvas):
    """Grafic scalabil de bandă cu marcaje persistente, HOLD la ascultare și intensitate la recurență."""

    def __init__(self, parent, start_mhz, end_mhz, step_mhz, on_tune_cb, **kwargs):
        super().__init__(parent, highlightthickness=1, highlightbackground="#c8c8c8", **kwargs)
        self.start_mhz = start_mhz
        self.end_mhz = end_mhz
        self.step_mhz = step_mhz
        self.on_tune_cb = on_tune_cb
        self.active_freq = None
        self.hold = True                # True când se ascultă / scanarea e oprită (marcajele nu expiră)
        # freq_rounded -> {"hits": int, "last_t": float}
        self.markers = {}
        self._sig = None
        self.unsupported = []           # părți din bandă pe care dongle-ul nu le recepționează: [(MHz, MHz), ...]
        self.unsupported_long = ""
        self.unsupported_short = ""
        self.note = ""                  # notă discretă în colțul graficului (ex. HF cere direct sampling)
        self.bind("<Configure>", lambda _e: self.redraw())
        self.bind("<Button-1>", self._on_click)

    def set_unsupported(self, parts, long_txt, short_txt, note=""):
        self.unsupported = list(parts)
        self.unsupported_long, self.unsupported_short, self.note = long_txt, short_txt, note
        self.redraw()

    def redraw_if_changed(self):
        """Apelat periodic: redesenează doar dacă s-a schimbat ceva vizibil (marcaje, frecvență, estompare)."""
        sig = (self.active_freq, self.hold, self.start_mhz, self.end_mhz, self.winfo_width(), self.winfo_height(),
               tuple((f, v["hits"]) for f, v in self.markers.items()), None if self.hold else int(time.time() * 2))
        if sig != self._sig:
            self._sig = sig
            self.redraw()

    def set_band(self, start_mhz, end_mhz, step_mhz):
        self.start_mhz = start_mhz
        self.end_mhz = end_mhz
        self.step_mhz = step_mhz
        self.markers.clear()
        self.redraw()

    def set_hold(self, hold_enabled):
        was_hold = self.hold
        self.hold = bool(hold_enabled)
        if was_hold and not self.hold:
            now = time.time()
            for item in self.markers.values():
                item["last_t"] = now
        self.redraw()

    def clear_markers(self):
        self.markers.clear()
        self.redraw()

    def sorted_marker_freqs(self):
        return sorted(self.markers.keys())

    def record_hits(self, freqs):
        now = time.time()
        for f in freqs:
            k = round(float(f), 4)
            if k < self.start_mhz - 1e-6 or k > self.end_mhz + 1e-6:
                continue
            item = self.markers.get(k)
            if item is None:
                self.markers[k] = {"hits": 1, "last_t": now}
            else:
                item["hits"] = min(MARKER_MAX_HITS, item["hits"] + 1)
                item["last_t"] = now

    def prune_expired(self, now=None):
        if self.hold:
            return False
        now = now if now is not None else time.time()
        expired = [k for k, v in self.markers.items() if (now - v["last_t"]) > MARKER_TTL_SECS]
        for k in expired:
            del self.markers[k]
        return bool(expired)

    def _freq_to_x(self, f, left, right):
        span = max(1e-6, self.end_mhz - self.start_mhz)
        clamped = max(self.start_mhz, min(self.end_mhz, f))
        return left + ((clamped - self.start_mhz) / span) * (right - left)

    def _on_click(self, event):
        w = self.winfo_width()
        left, right = 18, w - 18
        if right <= left:
            return
        ratio = max(0.0, min(1.0, (event.x - left) / (right - left)))
        raw_f = self.start_mhz + ratio * (self.end_mhz - self.start_mhz)
        snapped = round(round(raw_f / self.step_mhz) * self.step_mhz, 4)
        snapped = max(self.start_mhz, min(self.end_mhz, snapped))
        self.active_freq = snapped
        self.hold = True
        if callable(self.on_tune_cb):
            self.on_tune_cb(snapped)
        self.redraw()

    @staticmethod
    def _blend_hex(hex_fg, hex_bg, alpha):
        alpha = max(0.0, min(1.0, alpha))
        r1, g1, b1 = int(hex_fg[1:3], 16), int(hex_fg[3:5], 16), int(hex_fg[5:7], 16)
        r2, g2, b2 = int(hex_bg[1:3], 16), int(hex_bg[3:5], 16), int(hex_bg[5:7], 16)
        r = int(round(r1 * alpha + r2 * (1.0 - alpha)))
        g = int(round(g1 * alpha + g2 * (1.0 - alpha)))
        b = int(round(b1 * alpha + b2 * (1.0 - alpha)))
        return f"#{r:02x}{g:02x}{b:02x}"

    def redraw(self):
        self.delete("all")
        w = max(20, self.winfo_width())
        h = max(40, self.winfo_height())
        # Fundalul graficului urmează tema ferestrei (ttk), nu un panou alb fix.
        bg = ttk.Style(self).lookup("TFrame", "background") or self.master.cget("bg")
        try:
            self.configure(bg=bg)
        except tk.TclError:
            bg = self.master.cget("bg")
            self.configure(bg=bg)
        try:
            rgb = tuple(int(bg[i:i + 2], 16) for i in (1, 3, 5))
            dark = sum(rgb) / 3 < 128
        except (ValueError, TypeError):
            dark = False
        band_bg = bg
        axis_color = "#aab4c0" if dark else "#6c757d"
        tick_color = "#c5ccd5" if dark else "#495057"
        text_color = "#e1e6ec" if dark else "#343a40"
        left, right = 18, w - 18
        axis_y = int(h * 0.56)
        top_y = max(18, axis_y - int(h * 0.34))
        bot_y = min(h - 20, axis_y + int(h * 0.24))

        # Bandă de activitate în fundal
        self.create_rectangle(left, top_y, right, bot_y, fill=band_bg, outline="")
        self.create_line(left, axis_y, right, axis_y, fill=axis_color, width=1)

        span = max(1e-6, self.end_mhz - self.start_mhz)
        px_per_mhz = (right - left) / span

        # Zone pe care dongle-ul nu le poate recepționa: hașurate roșu, cu explicație
        for a, b in self.unsupported:
            x0, x1 = self._freq_to_x(a, left, right), self._freq_to_x(b, left, right)
            if x1 - x0 < 1:
                continue
            self.create_rectangle(x0, top_y, x1, bot_y, fill="#c92a2a", outline="#c92a2a", stipple="gray25")
            wpx = x1 - x0
            txt = self.unsupported_long if wpx >= 330 else (self.unsupported_short if wpx >= 90 else "")
            if txt:
                self.create_text((x0 + x1) / 2, top_y + 12, text=txt, fill=text_color, width=max(40, int(wpx) - 10),
                                 font=("TkDefaultFont", 8, "bold"))

        # Gradații: pasul se alege după lățimea în pixeli, aliniat la multipli rotunzi
        steps = (0.001, 0.002, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5, 1.0, 2.0, 5.0, 10.0, 20.0, 50.0, 100.0)
        major_step = next((s for s in steps if s * px_per_mhz >= 55), steps[-1])
        decimals = max(0, -int(math.floor(math.log10(major_step) + 1e-9)))
        k = math.ceil((self.start_mhz - 1e-9) / major_step)
        while True:
            f = k * major_step
            if f > self.end_mhz + 1e-6:
                break
            x = self._freq_to_x(f, left, right)
            self.create_line(x, axis_y - 7, x, axis_y + 7, fill=tick_color, width=1)
            self.create_text(x, min(h - 4, axis_y + 10), text=f"{f:.{decimals}f}", anchor="n",
                             fill=text_color, font=("TkDefaultFont", 8))
            k += 1
        if self.note:
            self.create_text(left, 3, text=self.note, anchor="nw", fill=text_color, font=("TkDefaultFont", 8))

        # Marcaje de activitate: înghețate (HOLD) la ascultare, estompate treptat la scanare
        now = time.time()
        for f, info in self.markers.items():
            if self.hold:
                freshness = 0.90
            else:
                age = max(0.0, now - info["last_t"])
                if age >= MARKER_TTL_SECS:
                    continue
                freshness = 1.0 - (age / MARKER_TTL_SECS)
            rec_ratio = min(1.0, info["hits"] / float(MARKER_MAX_HITS))
            strength = min(1.0, 0.35 * freshness + 0.65 * rec_ratio)
            width_px = 2 + int(round(strength * 4))
            color = self._blend_hex("#0d6efd", band_bg, max(0.28, strength))
            mx = self._freq_to_x(f, left, right)
            mark_h = (bot_y - top_y) * (0.48 + 0.48 * strength)
            y0 = axis_y - mark_h * 0.5
            y1 = axis_y + mark_h * 0.5
            self.create_line(mx, y0, mx, y1, fill=color, width=width_px)

        # Indicatorul frecvenței acordate curent
        if self.active_freq is not None and (self.start_mhz - 1e-6) <= self.active_freq <= (self.end_mhz + 1e-6):
            cx = self._freq_to_x(self.active_freq, left, right)
            self.create_line(cx, top_y - 2, cx, bot_y + 4, fill="#c92a2a", width=2)
            lx = min(max(cx, left + 36), right - 36)
            self.create_text(lx, top_y - 4, text=f"{self.active_freq:.4f}".rstrip("0").rstrip(".") + " MHz",
                             anchor="s", fill="#c92a2a", font=("TkDefaultFont", 8, "bold"))


def _mix_rgb(a, b, t):
    return tuple(int(round(a[i] + (b[i] - a[i]) * t)) for i in range(3))


def _hex_rgb(c):
    return "#%02x%02x%02x" % tuple(max(0, min(255, v)) for v in c)


class ToggleSwitch(tk.Canvas):
    """Întrerupător orizontal cu două poziții (stânga / dreapta), în stilul slider-ului din temă:
    șanț gri adâncit + buton dreptunghiular cu muchii; mereu e una dintre poziții selectată."""

    W, H = 48, 20

    def __init__(self, parent, command=None):
        super().__init__(parent, width=self.W, height=self.H, highlightthickness=0, cursor="hand2")
        self.command = command
        self.right = False
        self.bind("<Button-1>", lambda _e: self.set(not self.right, notify=True))
        self.bind("<<ThemeChanged>>", lambda _e: self.redraw())
        self.redraw()

    def set(self, right, notify=False):
        right = bool(right)
        changed = right != self.right
        self.right = right
        self.redraw()
        if notify and changed and callable(self.command):
            self.command()

    def _color(self, name, default):
        try:
            return tuple(v >> 8 for v in self.winfo_rgb(name))
        except tk.TclError:
            return default

    def redraw(self):
        style = ttk.Style(self)
        bg = self._color(style.lookup("TFrame", "background") or "#d9d9d9", (217, 217, 217))
        trough = self._color(style.lookup("TScale", "troughcolor") or "", None)
        if trough is None or trough == bg:
            trough = _mix_rgb(bg, (0, 0, 0), 0.14)
        black, white = (0, 0, 0), (255, 255, 255)
        edge = _mix_rgb(bg, black, 0.55)
        knob = _mix_rgb(bg, white, 0.30)
        self.configure(bg=_hex_rgb(bg))
        self.delete("all")
        w, h = self.W, self.H
        self.create_rectangle(0, 0, w - 1, h - 1, fill=_hex_rgb(trough), outline=_hex_rgb(edge))
        shade = _hex_rgb(_mix_rgb(trough, black, 0.25))
        self.create_line(1, 1, w - 2, 1, fill=shade)                    # șanț adâncit: umbră sus / stânga
        self.create_line(1, 1, 1, h - 2, fill=shade)
        kw = w // 2 - 2
        x0 = w - 2 - kw if self.right else 2
        x1, y0, y1 = x0 + kw, 2, h - 3
        self.create_rectangle(x0, y0, x1, y1, fill=_hex_rgb(knob), outline=_hex_rgb(edge))
        self.create_line(x0 + 1, y0 + 1, x1 - 1, y0 + 1, fill=_hex_rgb(_mix_rgb(knob, white, 0.7)))   # muchie luminată
        self.create_line(x0 + 1, y0 + 1, x0 + 1, y1 - 1, fill=_hex_rgb(_mix_rgb(knob, white, 0.7)))
        self.create_line(x0 + 1, y1 - 1, x1 - 1, y1 - 1, fill=_hex_rgb(_mix_rgb(knob, black, 0.2)))   # muchie în umbră
        self.create_line(x1 - 1, y0 + 1, x1 - 1, y1 - 1, fill=_hex_rgb(_mix_rgb(knob, black, 0.2)))


def wf_palette(bg):
    """Tabel de culori 256x3: fundal (gri-ul temei) -> albastru -> cyan -> galben -> roșu."""
    pts = [(0.0, bg), (0.30, (59, 91, 219)), (0.52, (34, 184, 207)),
           (0.72, (252, 196, 25)), (0.90, (224, 49, 49)), (1.0, (255, 214, 214))]
    xs = np.linspace(0.0, 1.0, 256)
    pos = [p[0] for p in pts]
    return np.stack([np.interp(xs, pos, [p[1][c] for p in pts]) for c in range(3)], axis=1).astype(np.uint8)


def wf_normalize(row_db, floor, sens_db=0.0):
    """dB -> indici 0..255. Fundalul (floor) cade la începutul paletei (gri cu nuanță slabă);
    sens_db > 0 coboară pragul: apar mai multe culori; sens_db < 0 îl urcă: rămâne doar gri + semnale puternice."""
    return ((row_db - (floor - 4.0 - sens_db)) * (255.0 / WF_RANGE_DB)).clip(0, 255).astype(np.uint8)


def wf_columns(a, width, u0=None, u1=None):
    """Aduce ultima axă la `width` coloane pentru zona [u0, u1) exprimată în CELULE (marginea stângă a primei celule = 0).
    Pixelul x acoperă celulele [u0 + x*s, u0 + (x+1)*s), s = (u1-u0)/width. Mai multe celule decât pixeli: maximul
    grupului (vârfurile nu dispar); mai puține: interpolare între centrele celulelor. Maparea e aceeași cu cea a clicului."""
    bins = a.shape[-1]
    if u0 is None:
        u0, u1 = 0.0, float(bins)
    s = (u1 - u0) / width
    if s >= 1.0:
        edges = np.clip(np.round(u0 + np.arange(width + 1) * s).astype(np.intp), 0, bins)
        starts = np.minimum(edges[:-1], bins - 1)
        idx = starts if edges[-1] >= bins else np.concatenate((starts, [edges[-1]]))
        out = np.maximum.reduceat(a, idx, axis=-1)
        return out[..., :width]
    uc = np.clip(u0 + (np.arange(width) + 0.5) * s - 0.5, 0.0, bins - 1.0)     # centrul pixelului, în „centre de celulă”
    i0 = np.floor(uc).astype(np.intp)
    i1 = np.minimum(i0 + 1, bins - 1)
    t = (uc - i0).astype(np.float32)
    return a[..., i0] * (1.0 - t) + a[..., i1] * t


def wf_image_rgb(rows, floors, width, height, lut, sens_db=0.0, view=None):
    """Rânduri în dB (cele mai vechi primele) + nivelul fundalului fiecăruia -> imagine (height, width, 3),
    cel mai nou rând sus. `view=(u0, u1)` = zona afișată, în celule (zoom)."""
    bins = len(rows[-1]) if rows else 1
    grid = np.full((height, bins), -1e9, np.float32)        # fără date -> sub prag -> fundal
    fl = np.zeros((height, 1), np.float32)
    n = min(len(rows), height)
    if n:
        grid[:n] = np.stack(rows[-n:][::-1])
        fl[:n, 0] = floors[-n:][::-1]
    u0, u1 = view if view else (None, None)
    return lut[wf_normalize(wf_columns(grid, width, u0, u1), fl, sens_db)]


def wf_curve(row_db, floor, sens_db, width, height, view=None):
    """Linia de spectru: vector [x0, y0, x1, y1, ...] (y = 0 sus). Aceeași scară ca a culorilor (floor, sensibilitate)."""
    u0, u1 = view if view else (None, None)
    r = wf_columns(np.asarray(row_db, np.float32), width, u0, u1)
    lo = floor - 4.0 - sens_db
    y = (height - 1) - np.clip((r - lo) / WF_RANGE_DB, 0.0, 1.0) * (height - 1)
    pts = np.empty(2 * width, np.float32)
    pts[0::2] = np.arange(width)
    pts[1::2] = y
    return pts


class WaterfallView(tk.Canvas):
    """Spectru RF + cascadă. De sus în jos: frecvența acordată, linia de spectru (cu memorarea vârfurilor),
    axa de frecvențe, cascada. Doar tkinter + numpy: imaginea se construiește ca PPM în memorie.
    Centrul = frecvența acordată (linia roșie); chenarul portocaliu = banda demodulată (se trage de margini);
    clic = acordare; rotița mouse-ului = zoom."""

    LABEL_H = 14
    TICK_H = 26

    def __init__(self, parent, on_click_cb, on_zoom_cb=None, on_bw_cb=None, **kwargs):
        super().__init__(parent, highlightthickness=1, highlightbackground="#c8c8c8", **kwargs)
        self.on_click_cb = on_click_cb
        self.on_zoom_cb = on_zoom_cb
        self.on_bw_cb = on_bw_cb                     # apelat cu lățimea totală (kHz) cât tragi marginea chenarului
        self.bw_limits = (2.0, 40.0)
        self.bw_khz = 0.0                            # lățimea totală a benzii demodulate; 0 = fără chenar
        self.bw_locked = False                       # filtrul blocat pe recomandat: marginile chenarului nu se mai trag
        self.bw_side = 0                             # 0 = simetric (AM/NFM/WFM); +1 = USB; -1 = LSB
        self.peak_snap = True                        # clicul se atrage pe vârful de semnal din apropiere (Shift = clic exact)
        self._drag = False
        self._cursor = ""
        self._rows = deque(maxlen=WF_MAX_ROWS)       # rânduri în dB (float32)
        self._floors = deque(maxlen=WF_MAX_ROWS)     # nivelul fundalului la momentul fiecărui rând
        self.sens_db = 0.0
        self.zoom = 1
        self.peak_hold = False
        self.centre = None                           # frecvența acordată (MHz)
        self.span = None                             # lățimea totală a rândului (MHz)
        self.left_rel = 0.0                          # marginea stângă a primului bin, față de frecvența acordată (MHz)
        self._bins = 0
        self._floor = None
        self._spec = None                            # spectrul curent (mediat ușor), pentru linie
        self._peak = None                            # maximul pe fiecare bin, de la ultima ștergere
        self._geom = None                            # (lățime, f_lo, span) pentru clic
        self._dirty = True
        self._bg = None
        self._lut = None
        self._dark = False
        self._img = None
        self._img_id = None
        self.wait_text = ""                          # afișat cât timp nu există niciun rând de date
        self.bind("<Configure>", lambda _e: self._invalidate())
        self.bind("<Button-1>", self._on_click)
        self.bind("<MouseWheel>", self._on_wheel)
        self.bind("<Button-4>", self._on_wheel)
        self.bind("<Button-5>", self._on_wheel)
        self.bind("<Motion>", self._on_motion)
        self.bind("<B1-Motion>", self._on_drag)
        self.bind("<ButtonRelease-1>", self._on_release)

    def _invalidate(self):
        self._dirty = True

    def clear(self):
        self._rows.clear()
        self._floors.clear()
        self.centre = self.span = self._floor = self._spec = self._peak = None
        self._dirty = True

    def set_peak_hold(self, on):
        self.peak_hold = bool(on)
        self._peak = None
        self._dirty = True

    def add_rows(self, items):
        for centre, span, row, left_rel in items:
            if self.centre is None or abs(centre - self.centre) > 1e-6 or len(row) != self._bins:
                self._rows.clear()                  # altă frecvență centrală sau altă rezoluție: istoricul nu se mai potrivește
                self._floors.clear()
                self._floor = self._spec = self._peak = None
                self.centre, self.span, self._bins = centre, span, len(row)
            self.left_rel = left_rel
            med = float(np.median(row))
            self._floor = med if self._floor is None else 0.9 * self._floor + 0.1 * med
            self._rows.append(row)
            self._floors.append(self._floor)
            self._spec = row.copy()
            if self.peak_hold:
                self._peak = row.copy() if self._peak is None else np.maximum(self._peak, row)
            self._dirty = True

    def _view(self):
        """(u0, u1, f_lo, span): zona afișată. Centrată pe frecvența acordată; u0/u1 sunt în CELULE (bin-i),
        deci pixelul x ↔ frecvența f_lo + (x + 0.5) / lățime · span, exact ca la clic."""
        df = self.span / self._bins
        span = max(self.span / max(1, self.zoom), 8 * df)
        f_lo = self.centre - span / 2.0
        u0 = (f_lo - (self.centre + self.left_rel)) / df
        return u0, u0 + span / df, f_lo, span

    # ------------------------------------------------------------------ mouse
    def _box_px(self):
        """(x_stânga, x_dreapta) ale chenarului de bandă, în pixeli, sau None."""
        if self._geom is None or self.bw_khz <= 0:
            return None
        pw, _f_lo, span = self._geom
        cx = 1 + pw / 2.0
        w = self.bw_khz * 1e-3 * (pw / span)
        if self.bw_side == 0:
            return cx - w / 2.0, cx + w / 2.0
        return (cx, cx + w) if self.bw_side > 0 else (cx - w, cx)

    def _edge(self, x):
        """Mouse-ul e pe marginea chenarului care se trage? (la SSB doar marginea îndepărtată de purtătoare)"""
        box = self._box_px()
        if box is None or self.on_bw_cb is None or self.bw_locked or box[1] - box[0] < 8:
            return False
        if self.bw_side == 0:
            return min(abs(x - box[0]), abs(x - box[1])) <= 4
        return abs(x - (box[1] if self.bw_side > 0 else box[0])) <= 4

    def _on_motion(self, event):
        want = "sb_h_double_arrow" if self._edge(event.x) else ""
        if want != self._cursor:
            self._cursor = want
            self.configure(cursor=want)

    def _on_click(self, event):
        if self._geom is None:
            return
        if self._edge(event.x):                     # începe tragerea lățimii benzii, nu acordează
            self._drag = True
            return
        pw, f_lo, span = self._geom
        f = f_lo + (event.x - 1 + 0.5) / pw * span                   # centrul pixelului, nu marginea lui
        if self.peak_snap and not (event.state & 0x0001):            # Shift apăsat = acordare exactă, fără atragere
            peak = self._peak_near(f)
            if peak is not None:
                f = peak
        self.on_click_cb(f)

    def _peak_near(self, f):
        """Frecvența vârfului de semnal din apropierea lui `f` (MHz), cu interpolare sub-bin, sau None dacă nu există
        un vârf clar (cel puțin 6 dB peste fundal). Spectrul e mediat în putere pe ultimele rânduri, ca zgomotul să
        nu mute vârful. Fereastra de căutare ține de lățimea benzii demodulate."""
        if not self._rows or self.centre is None or self._bins < 8:
            return None
        recent = list(self._rows)[-10:]
        spec = 10.0 * np.log10(np.mean([10.0 ** (r / 10.0) for r in recent], axis=0) + 1e-20)
        df = self.span / self._bins
        left = self.centre + self.left_rel                           # marginea stângă a primei celule
        u = (f - left) / df - 0.5                                    # celula (fracționară) de sub cursor
        half = max(self.bw_khz * 0.75e-3, 3 * df) / df
        lo, hi = max(0, int(math.floor(u - half))), min(self._bins - 1, int(math.ceil(u + half)))
        if hi - lo < 2:
            return None
        k = lo + int(np.argmax(spec[lo:hi + 1]))
        if k <= lo or k >= hi or spec[k] - float(np.median(spec)) < 6.0:
            return None                                              # maximul trebuie să fie interior (un vârf, nu poalele unuia)
        delta = 0.0
        if 0 < k < self._bins - 1:
            a, b, c = float(spec[k - 1]), float(spec[k]), float(spec[k + 1])
            den = a - 2.0 * b + c
            if den != 0.0:
                delta = max(-0.5, min(0.5, 0.5 * (a - c) / den))
        return left + (k + 0.5 + delta) * df

    def _on_drag(self, event):
        if not self._drag or self._geom is None:
            return
        pw, _f_lo, span = self._geom
        dx_khz = abs(event.x - (1 + pw / 2.0)) / (pw / span) * 1000.0
        lo, hi = self.bw_limits
        full = max(lo, min(hi, dx_khz * (2.0 if self.bw_side == 0 else 1.0)))
        self.bw_khz = full
        self._dirty = True
        self.on_bw_cb(full)

    def _on_release(self, _event):
        self._drag = False

    def _on_wheel(self, event):
        up = getattr(event, "num", 0) == 4 or getattr(event, "delta", 0) > 0
        if self.on_zoom_cb:
            self.on_zoom_cb(1 if up else -1)

    # ------------------------------------------------------------------ desen
    def _theme(self):
        bg = ttk.Style(self).lookup("TFrame", "background") or "#d9d9d9"
        if bg != self._bg:
            try:
                rgb = tuple(v >> 8 for v in self.winfo_rgb(bg))
            except tk.TclError:
                bg, rgb = "#d9d9d9", (217, 217, 217)
            self._bg, self._dark = bg, sum(rgb) / 3 < 128
            self._lut = wf_palette(rgb)
            ink = (255, 255, 255) if self._dark else (0, 0, 0)
            self._text = _hex_rgb(_mix_rgb(rgb, ink, 0.85))
            self._tick = _hex_rgb(_mix_rgb(rgb, ink, 0.65))
            self._grid = _hex_rgb(_mix_rgb(rgb, ink, 0.14))
            self._curve = "#74c0fc" if self._dark else "#1c7ed6"
            self._peakc = "#ffd43b" if self._dark else "#e8590c"
            self.configure(bg=bg)
            self._dirty = True

    def _make_image(self, rgb):
        h, w = rgb.shape[:2]
        try:
            return tk.PhotoImage(master=self, format="PPM", data=b"P6 %d %d 255\n" % (w, h) + rgb.tobytes())
        except tk.TclError:                         # Tk fără suport PPM din memorie: variantă mai lentă, dar sigură
            img = tk.PhotoImage(master=self, width=w, height=h)
            img.put(" ".join("{" + " ".join("#%02x%02x%02x" % tuple(px) for px in line) + "}" for line in rgb.tolist()))
            return img

    def render(self):
        self._theme()
        w, h = self.winfo_width(), self.winfo_height()
        if not self._dirty or w < 60 or h < self.LABEL_H + self.TICK_H + 40:
            return
        self._dirty = False
        pw = w - 2
        spec_h = 0 if h < 170 else int(min(90, max(44, h * 0.28)))      # zona liniei de spectru
        img_y = self.LABEL_H + spec_h + self.TICK_H
        ph = h - img_y - 2
        if ph < 10:
            return
        have = self.centre is not None and bool(self._rows)
        u0, u1, f_lo, span = self._view() if have else (0.0, 1.0, 0.0, 1.0)
        rgb = wf_image_rgb(list(self._rows), list(self._floors), pw, ph, self._lut, self.sens_db,
                           (u0, u1) if have else None)
        self._img = self._make_image(rgb)
        if self._img_id is None:
            self._img_id = self.create_image(1, img_y, anchor="nw", image=self._img)
        else:
            self.coords(self._img_id, 1, img_y)
            self.itemconfigure(self._img_id, image=self._img)
        self.delete("ov")
        if have:
            self._geom = (pw, f_lo, span)
            self._draw_overlay(pw, h, spec_h, img_y, f_lo, span, (u0, u1))
        else:
            self._geom = None
            self.create_text(w / 2, img_y + ph / 2, text=self.wait_text, fill=getattr(self, "_text", "#343a40"), tags="ov")

    def _draw_overlay(self, pw, h, spec_h, img_y, f_lo, span, view):
        ppm_px = pw / span                                      # pixeli / MHz
        cx = 1 + pw / 2
        top = self.LABEL_H
        box = self._box_px()
        if box is not None:                                     # chenarul benzii demodulate
            x0, x1 = box
            if x1 - x0 < 4:
                x0, x1 = (x0 + x1) / 2 - 2, (x0 + x1) / 2 + 2
            self.create_rectangle(x0, top, x1, h - 2, outline="#f08c00", fill="#f08c00",
                                  stipple="gray12", width=2, tags="ov")
        # --- linia de spectru + vârfuri memorate
        if spec_h and self._spec is not None:
            bot = top + spec_h - 1
            self.create_rectangle(1, top, pw, bot, outline=self._grid, tags="ov")
            floor = self._floors[-1]
            line = wf_curve(self._spec, floor, self.sens_db, pw, spec_h - 2, view)
            line[0::2] += 1
            line[1::2] += top + 1
            poly = np.concatenate([line, np.array([pw, bot, 1, bot], np.float32)])
            self.create_polygon(poly.tolist(), fill=self._curve, outline="", stipple="gray25", tags="ov")
            self.create_line(line.tolist(), fill=self._curve, tags="ov")
            if self.peak_hold and self._peak is not None:
                pk = wf_curve(self._peak, floor, self.sens_db, pw, spec_h - 2, view)
                pk[0::2] += 1
                pk[1::2] += top + 1
                self.create_line(pk.tolist(), fill=self._peakc, tags="ov")
        # --- axa de frecvențe (etichete deasupra gradațiilor, lipită de cascadă)
        step = next((s for s in (0.001, 0.002, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.25, 0.5, 1.0, 2.0, 5.0)
                     if s * ppm_px >= 80), 10.0)
        k = math.ceil(f_lo / step - 1e-9)
        while True:
            x = 1 + (k * step - f_lo) * ppm_px
            if x > pw:
                break
            if spec_h:
                self.create_line(x, top, x, top + spec_h - 1, fill=self._grid, tags="ov")
            self.create_line(x, img_y - 7, x, img_y, fill=self._tick, tags="ov")
            self.create_text(x, img_y - 9, text=f"{k * step:.4f}".rstrip("0").rstrip("."), anchor="s",
                             fill=self._text, font=("TkDefaultFont", 8), tags="ov")
            k += 1
        # --- frecvența acordată (roșu) + lățimea afișată
        self.create_line(cx, top, cx, h - 1, fill="#c92a2a", tags="ov")
        self.create_text(cx, 1, text=f"{self.centre:.4f}".rstrip("0").rstrip(".") + " MHz", anchor="n",
                         fill="#c92a2a", font=("TkDefaultFont", 8, "bold"), tags="ov")
        self.create_text(pw, 1, text=f"{span * 1000:.0f} kHz", anchor="ne", fill=self._text,
                         font=("TkDefaultFont", 8), tags="ov")


class MessageCardsPanel(tk.Canvas):
    """Panou plăcut cu carduri de mesaje recepționate pe fundal cald, fără aspect de log."""

    BG_PANEL = "#f2efe9"
    CARD_BG = "#fcfbf8"
    CARD_BORDER = "#ded9cf"
    ACCENT_AIR = "#1b6ca8"
    ACCENT_HAM = "#2b7a4b"
    TEXT_MAIN = "#23272e"
    TEXT_META = "#5c6470"

    def __init__(self, parent, **kwargs):
        theme_bg = ttk.Style(parent).lookup("TFrame", "background") or parent.cget("bg")
        try:
            rgb = tuple(int(theme_bg[i:i + 2], 16) for i in (1, 3, 5))
            dark = sum(rgb) / 3 < 128
        except (ValueError, TypeError):
            dark = False
        self.BG_PANEL = theme_bg
        self.CARD_BG = theme_bg
        self.CARD_BORDER = "#59616b" if dark else "#c8c8c8"
        self.TEXT_MAIN = "#e1e6ec" if dark else "#343a40"
        self.TEXT_META = "#b8c0ca" if dark else "#5c6470"
        super().__init__(parent, bg=theme_bg, highlightthickness=1,
                         highlightbackground=self.CARD_BORDER, **kwargs)
        self.cards = []     # [{"time": str, "freq": str, "tag": str, "text": str, "hint": bool}]
        self.bind("<Configure>", lambda _e: self.redraw())
        self.bind("<MouseWheel>", self._on_wheel)
        self.bind("<Button-4>", self._on_wheel)
        self.bind("<Button-5>", self._on_wheel)

    def _on_wheel(self, event):
        bbox = self.bbox("all")
        if not bbox or (bbox[3] - bbox[1]) <= max(1, self.winfo_height()):
            return
        if event.num == 4 or getattr(event, "delta", 0) > 0:
            self.yview_scroll(-2, "units")
        elif event.num == 5 or getattr(event, "delta", 0) < 0:
            self.yview_scroll(2, "units")

    def set_hint(self, hint_text):
        self.cards = [{"time": "", "freq": "", "tag": "", "text": hint_text, "hint": True}]
        self.redraw()

    def add_message(self, item):
        if self.cards and self.cards[0].get("hint"):
            self.cards.clear()
        self.cards.append({
            "time": item.get("time", ""),
            "freq": item.get("freq", ""),
            "tag": item.get("tag", ""),
            "band": item.get("band", ""),
            "text": item.get("text", ""),
            "hint": False,
        })
        if len(self.cards) > 300:
            self.cards = self.cards[-300:]
        self.redraw()
        self.yview_moveto(1.0)

    def clear_cards(self, hint_text=""):
        self.cards.clear()
        if hint_text:
            self.set_hint(hint_text)
        else:
            self.redraw()

    @staticmethod
    def _wrap_lines(text, max_chars):
        max_chars = max(18, max_chars)
        lines = []
        for para in (text or "").splitlines() or [""]:
            words = para.split()
            if not words:
                lines.append("")
                continue
            cur = words[0]
            for w in words[1:]:
                if len(cur) + 1 + len(w) <= max_chars:
                    cur += " " + w
                else:
                    lines.append(cur)
                    cur = w
            lines.append(cur)
        return lines

    def redraw(self):
        self.delete("all")
        w = max(120, self.winfo_width())
        h = max(60, self.winfo_height())
        pad_x = 12
        card_w = max(80, w - pad_x * 2)
        y = 10

        if not self.cards:
            self.configure(scrollregion=(0, 0, w, h))
            return

        if self.cards[0].get("hint"):
            hint = self.cards[0]["text"]
            lines = self._wrap_lines(hint, max(24, (w - 40) // 7))
            box_h = max(46, 18 + len(lines) * 16)
            cy = max(14, (h - box_h) // 2)
            self.create_rectangle(pad_x, cy, pad_x + card_w, cy + box_h,
                                    fill=self.CARD_BG, outline=self.CARD_BORDER, width=1)
            for idx, ln in enumerate(lines):
                self.create_text(w // 2, cy + 12 + idx * 16, text=ln, anchor="n",
                                 fill=self.TEXT_META, font=("TkDefaultFont", 9, "italic"))
            self.configure(scrollregion=(0, 0, w, max(h, cy + box_h + 12)))
            return

        for card in self.cards:
            accent = self.ACCENT_AIR if card.get("band") == "air" else self.ACCENT_HAM
            meta_left = "  •  ".join(p for p in (card["freq"], card["tag"]) if p)
            meta_right = card["time"]
            body_lines = self._wrap_lines(card["text"], max(24, (card_w - 28) // 7))
            card_h = 34 + len(body_lines) * 16

            x0, x1 = pad_x, pad_x + card_w
            self.create_rectangle(x0, y, x1, y + card_h,
                                    fill=self.CARD_BG, outline=self.CARD_BORDER, width=1)
            self.create_rectangle(x0, y, x0 + 4, y + card_h, fill=accent, outline="")

            if meta_left:
                self.create_text(x0 + 12, y + 8, text=meta_left, anchor="nw",
                                 fill=accent, font=("TkDefaultFont", 8, "bold"))
            if meta_right:
                self.create_text(x1 - 10, y + 8, text=meta_right, anchor="ne",
                                 fill=self.TEXT_META, font=("TkDefaultFont", 8))

            for i, ln in enumerate(body_lines):
                self.create_text(x0 + 12, y + 25 + i * 16, text=ln, anchor="nw",
                                 fill=self.TEXT_MAIN, font=("TkDefaultFont", 9))

            y += card_h + 8

        self.configure(scrollregion=(0, 0, w, max(h, y + 6)))


class App:
    def __init__(self, root):
        self.root = root
        self.eng = Engine()
        self.stations = {}
        self.selected_freq = None
        self._station_buttons = {}      # freq -> (holder_frame, btn)
        self._last_cols = 0
        self._toolbar_pad = TOOLBAR_MIN_GAP  # spațiu minim între cifrele scalei și butoanele de sub ea
        self._align_pending = False
        self._scale_pad = 0             # spațiu deasupra scalei, ca axa ei să cadă pe separatorul din dreapta
        self._right_pad = 0             # spațiu suplimentar deasupra titlului din dreapta (doar dacă e nevoie la aliniere)
        self._warn_key = None           # avertismentul curent din zona de mesaje (cheie I18N)
        self._warn_args = ()
        self.rec_dir = default_rec_dir()
        self.ui_q = queue.Queue()
        self.scanning = False
        self.scan_cancel = threading.Event()
        self.air_ham_active = False
        self.active_upper_band = "air"  # "air" | "ham"
        self.ham_band = "vhf"           # "vhf" (144-146) | "uhf" (430-440)
        self.air_scan_running = False
        self.ham_scan_running = False
        self._air_scan_cancel = threading.Event()
        self._ham_scan_cancel = threading.Event()
        self._status_key = None
        self._status_args = ()
        self._status_raw = ""
        self.fm_freq = 98.3             # ultimul post FM ascultat
        self.air_freq = None            # ultima frecvență ascultată pe aviație
        self.ham_freqs = {b[0]: None for b in BANDS if b[0] != "air"}     # ultima frecvență ascultată pe fiecare bandă ham
        self._ent_dirty = False         # utilizatorul a scris în căsuța de frecvență (nu o suprascrie)
        self.audio_sink_name = None     # ieșirea audio aleasă (nume sink PipeWire); None = implicită
        # --- control hardware: TOT ce poate bloca (USB, rtl_tcp, scanări) rulează pe UN singur fir, în coadă.
        #     Interfața doar pune comenzi în coadă și citește rezultatele din ui_q, deci nu îngheață niciodată.
        self.jobs = queue.Queue()
        self._pending = 0               # comenzi trimise și încă neterminate (doar pe firul UI)
        self._want_on = False           # intenția utilizatorului: radio pornit?
        self._closing = False
        self._closed_evt = threading.Event()
        self._gain = "auto"             # copii simple ale valorilor din widget-uri, citite de firul de control
        self.band_thr = {"air": 10, "ham": 10}
        self._ui_freq = None            # ultima frecvență cerută din interfață (înainte să ajungă la motor)
        self._ppm = 0                   # corecția ppm curentă (aplicată motorului prin coada de comenzi)
        self._bw = dict(BW_DEFAULT)     # lățimea benzii de recepție pe moduri (kHz) — starea din interfață
        self._save_after = None
        self._split = 0.34              # ce fracțiune din înălțime ocupă graficul de bandă (bara mobilă)
        self._split_applied = False
        self._ppm_after = None
        self._ppm_sig = None
        self._band_bw = {}              # filtrul ales de utilizator pe fiecare bandă (implicit: cel recomandat)
        self._band_markers = {}         # marcajele pe fiecare bandă (graficul generic se refolosește între benzi)
        self._cal_win = None            # fereastra asistentului de calibrare
        self._cal_cancel = threading.Event()
        self._last_running = None
        self._scale_sig = None
        self._hl_sig = None
        self._sink_names = []
        self._sink_labels = []
        self.cfg = self._load_cfg()
        self._build_ui()
        self._apply_cfg()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

        threading.Thread(target=self._ctl_loop, daemon=True, name="radio-control").start()
        self._check_system_status()
        self._poll()
        self._wf_tick()
        self.root.after(300, self._align_toolbar_row)   # aliniere după ce fereastra e afișată

    def _load_cfg(self):
        for path in (CFG_PATH, OLD_CFG_PATH):
            if path == OLD_CFG_PATH and os.path.exists(CFG_PATH):
                break
            try:
                with open(path, "r", encoding="utf-8") as f:
                    return json.load(f)
            except Exception:
                continue
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
            "fm_freq": self.fm_freq,
            "air_freq": self.air_freq,
            **{"ham_freq_" + k: v for k, v in self.ham_freqs.items()},
            "air_ham_active": bool(self.air_ham_active),
            "upper_band": self.active_upper_band,
            "markers_air": [[f, v["hits"]] for f, v in sorted(self.air_chart.markers.items())],
            "markers_bands": self._markers_snapshot(),
            "audio_sink": self.audio_sink_name,
            "out_locked": bool(self.out_lock_var.get()),
            "squelch_auto": bool(self.sql_auto_var.get()),
            "volume": self.vol_var.get(),
            "muted": bool(self.mute_var.get()),
            "rds_enabled": bool(self.rds_var.get()) and HAS_RDS_DEPS,
            "gain": self._effective_gain(),
            "gain_manual": self.gain_var.get(),
            "bw_locked": bool(self.bw_lock_var.get()),
            "thr": self._int_var(self.thr_var, 10),
            "thr_air": self._int_var(self.thr_air_var, 10),
            "thr_ham": self._int_var(self.thr_ham_var, 10),
            "squelch_db": round(float(self.sql_var.get()), 1),
            "decode_packets": bool(self.decode_pkt_var.get()),
            "waterfall": bool(self.wf_var.get()),
            "wf_res": self.wf_res_var.get(),
            "wf_speed": self.wf_speed_var.get(),
            "wf_sens": self.wf_sens_var.get(),
            "wf_zoom": self.wf_zoom_var.get(),
            "wf_peak": bool(self.wf_peak_var.get()),
            "ppm": self._ppm,
            "bw": dict(self._bw),
            "band_bw": dict(self._band_bw),
            "hf_mode": self.eng.hf_override,
            "split": round(self._split, 3),
            "rec_dir": self.rec_dir,
            "rec_fmt": self.rec_fmt_var.get(),
            "language": self.lang.get(),
            "ham_band": self.ham_band,
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
        self.fm_freq = self._cfg_freq(c.get("fm_freq", c.get("freq")), 64.0, 110.0) or 98.3
        self.air_freq = self._cfg_freq(c.get("air_freq"), AIR_BAND_START, AIR_BAND_END)
        self.ham_freqs = {b[0]: self._cfg_freq(c.get("ham_freq_" + b[0]), b[2], b[3]) for b in BANDS if b[0] != "air"}
        self.eng.freq = self.fm_freq
        self.selected_freq = round(self.eng.freq, 2)
        sink = c.get("audio_sink")
        self.audio_sink_name = sink if isinstance(sink, str) and sink else None
        self.out_lock_var.set(1 if c.get("out_locked") else 0)
        self.vol_var.set(c.get("volume", 70))
        self.mute_var.set(1 if c.get("muted") else 0)
        rds_want = 1 if c.get("rds_enabled") else 0
        self.rds_var.set(rds_want if HAS_RDS_DEPS else 0)
        g = str(c.get("gain", "auto"))
        manual = str(c.get("gain_manual", g if g != "auto" else "30"))
        self.gain_var.set(manual if manual in GAIN_VALUES else "30")
        self.gain_auto_var.set(1 if g == "auto" else 0)
        self.bw_lock_var.set(1 if c.get("bw_locked", True) else 0)
        self.thr_var.set(c.get("thr", 10))
        for var, key in ((self.thr_air_var, "thr_air"), (self.thr_ham_var, "thr_ham")):
            try:
                var.set(max(3, min(30, int(c.get(key, c.get("thr", 10))))))
            except (TypeError, ValueError):
                var.set(10)
        sql_val = float(c.get("squelch_db", 12.0))
        self.sql_var.set(max(0.0, min(50.0, sql_val)))
        self._on_squelch_change(save=False)
        self.sql_auto_var.set(1 if c.get("squelch_auto") else 0)
        self._on_squelch_auto_change(save=False)
        if c.get("wf_res") in WF_RES:
            self.wf_res_var.set(c["wf_res"])
        if c.get("wf_speed") in WF_SPEEDS:
            self.wf_speed_var.set(c["wf_speed"])
        if c.get("wf_sens") in WF_SENS:
            self.wf_sens_var.set(c["wf_sens"])
        if c.get("wf_zoom") in WF_ZOOM:
            self.wf_zoom_var.set(c["wf_zoom"])
        self.wf_peak_var.set(1 if c.get("wf_peak") else 0)
        try:
            self._ppm = max(-200, min(200, int(c.get("ppm", 0))))
        except (TypeError, ValueError):
            self._ppm = 0
        self.ppm_var.set(str(self._ppm))
        self.eng.ppm = self._ppm
        saved_bw = c.get("bw") if isinstance(c.get("bw"), dict) else {}
        for m in BW_DEFAULT:
            try:
                v = float(saved_bw.get(m, BW_DEFAULT[m]))
            except (TypeError, ValueError):
                v = BW_DEFAULT[m]
            self._bw[m] = max(BW_RANGE[m][0], min(BW_RANGE[m][1], v))
            self.eng.set_bandwidth(m, self._bw[m])
        saved_band_bw = c.get("band_bw") if isinstance(c.get("band_bw"), dict) else {}
        for bid, v in saved_band_bw.items():
            try:
                key = bw_key(BAND_BY_ID[bid][5])
                self._band_bw[bid] = max(BW_RANGE[key][0], min(BW_RANGE[key][1], float(v)))
            except (KeyError, TypeError, ValueError):
                pass
        if c.get("hf_mode") in ("auto", "direct", "native", "off"):
            self.eng.hf_override = c["hf_mode"]
        try:
            self._split = max(0.15, min(0.7, float(c.get("split", self._split))))
        except (TypeError, ValueError):
            pass
        self.wf_var.set(1 if c.get("waterfall") else 0)
        self._on_waterfall_change(save=False)
        if isinstance(c.get("rec_dir"), str) and c["rec_dir"].strip():
            self.rec_dir = c["rec_dir"]
        if c.get("rec_fmt") in Recorder.FORMATS:
            self.rec_fmt_var.set(c["rec_fmt"])
        if c.get("ham_band") in BAND_BY_ID and c.get("ham_band") != "air":
            self.ham_band = c["ham_band"]
        lang_code = c.get("language", "ro")
        if lang_code not in self.i18n:
            lang_code = "ro"
        self.lang.set(lang_code)
        self.lang_name_var.set(CODE_TO_LANG_NAME.get(lang_code, "Română"))
        self._apply_translations(save=False)
        self._sync_rds_state(save=False)
        self._apply_out_lock()
        self._apply_gain_ui()
        self._apply_bw_lock_state()
        if self.air_ham_active:
            self._apply_band_bw()
        self._on_volume()
        self._on_mute()

        # Modul Aviație / Radioamatori, banda activă, marcajele: se reiau ca la închidere
        if c.get("upper_band") in ("air", "ham"):
            self.active_upper_band = c["upper_band"]
        self._apply_ham_band()
        self._load_markers(c)
        if c.get("air_ham_active"):
            self._set_air_ham_mode(True, retune=False)
        self._refresh_station_buttons(force_layout=True)

    @staticmethod
    def _int_var(var, default):
        try:
            return int(var.get())
        except (tk.TclError, ValueError):
            return default

    def _snapshot_params(self):
        """Copiază în atribute simple valorile din widget-uri de care are nevoie firul de control
        (Tkinter nu are voie apelat din alte fire)."""
        try:
            self._gain = self._effective_gain()
        except tk.TclError:
            pass
        self.band_thr = {"air": max(4, self._int_var(self.thr_air_var, 10)),
                         "ham": max(4, self._int_var(self.thr_ham_var, 10))}

    def _cur_freq(self):
        return self._ui_freq if self._ui_freq is not None else self.eng.freq

    @staticmethod
    def _cfg_freq(v, lo, hi):
        try:
            f = float(v)
        except (TypeError, ValueError):
            return None
        return f if lo <= f <= hi else None

    def _load_markers(self, c):
        now = time.time()

        def parse(items, lo, hi):
            out = {}
            for item in items if isinstance(items, list) else []:
                try:
                    f, hits = round(float(item[0]), 4), int(item[1])
                except (TypeError, ValueError, IndexError, KeyError):
                    continue
                if lo - 1e-6 <= f <= hi + 1e-6:
                    out[f] = {"hits": max(1, min(MARKER_MAX_HITS, hits)), "last_t": now}
            return out

        self.air_chart.markers.update(parse(c.get("markers_air"), self.air_chart.start_mhz, self.air_chart.end_mhz))
        per_band = c.get("markers_bands") if isinstance(c.get("markers_bands"), dict) else {}
        if not per_band and c.get("markers_ham"):                    # format vechi: o singură listă pentru banda ham curentă
            per_band = {self.ham_band: c["markers_ham"]}
        for bid, items in per_band.items():
            if bid in BAND_BY_ID and bid != "air":
                b = BAND_BY_ID[bid]
                self._band_markers[bid] = parse(items, b[2], b[3])
        self.ham_chart.markers.update(self._band_markers.get(self.ham_band, {}))
        self.air_chart.redraw()
        self.ham_chart.redraw()

    def _markers_snapshot(self):
        """Marcajele tuturor benzilor, pentru salvare (banda curentă se ia direct din grafic)."""
        self._band_markers[self.ham_band] = dict(self.ham_chart.markers)
        return {bid: [[f, v["hits"]] for f, v in sorted(m.items())] for bid, m in self._band_markers.items() if m}

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

    def _set_status_key(self, key, *args):
        self._status_key = key
        self._status_args = args
        self._status_raw = ""
        self.status.set(self._tr(key, *args))

    def _set_status_text(self, text):
        self._status_key = None
        self._status_args = ()
        self._status_raw = text
        self.status.set(text)

    def _set_warning(self, key=None, *args):
        self._warn_key = key
        self._warn_args = args
        self.lbl_warning.config(text=self._tr(key, *args) if key else "")

    def _refresh_warning(self):
        if self._warn_key:
            self.lbl_warning.config(text=self._tr(self._warn_key, *self._warn_args))

    def _refresh_status_text(self):
        if self._status_key:
            self.status.set(self._tr(self._status_key, *self._status_args))
        elif self._status_raw:
            self.status.set(self._status_raw)

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

        # Zona principală din stânga
        m = ttk.Frame(shell)
        m.pack(side="left", fill="both", expand=True)
        self.main_left = m

        self.i18n = I18N
        self.lang = tk.StringVar(value=self.cfg.get("language", "ro"))
        self.lang_name_var = tk.StringVar(value=CODE_TO_LANG_NAME.get(self.lang.get(), "Română"))
        set_msg_lang(self.lang.get())
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
        ttk.Separator(right, orient="horizontal").pack(side="bottom", fill="x", pady=(RIGHT_GAP, RIGHT_GAP))
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
        self.btn_rec.pack(side="right", padx=(4, 0))
        self.rec_fmt_box.pack(side="left", fill="x", expand=True)
        self._tip_rec = ToolTip(self.btn_rec, "")

        # --- Panou dreapta: 1) Limbă pe același rând ---
        langrow = ttk.Frame(right)
        langrow.pack(fill="x", pady=(0, 0))
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

        self._sep_top = ttk.Separator(right, orient="horizontal")
        self._sep_top.pack(fill="x", pady=(RIGHT_GAP, RIGHT_GAP))
        self._sep_top.bind("<Configure>", self._schedule_row_align)

        # --- Panou dreapta: 2) Acordare & control (adaptiv FM vs Aviație/Radioamatori) ---
        tune_box = ttk.Frame(right)
        self._tune_box = tune_box
        tune_box.pack(fill="x", pady=(0, 0))
        sec_tune = label(tune_box, "tuning", font=("TkDefaultFont", 9, "bold"), anchor="center")
        sec_tune.pack(fill="x", pady=(0, RIGHT_GAP))
        self._sec_tune = sec_tune

        # Rând 2a pentru FM: Precedent / Următor
        step_row = ttk.Frame(tune_box)
        step_row.pack(fill="x", pady=(0, RIGHT_GAP))
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

        # Rând 2a alternativ pentru Aviație / Radioamatori: Marcaj ant. / Marcaj urm.
        mark_step_row = ttk.Frame(tune_box)
        self._mark_step_row = mark_step_row
        mark_step_row.columnconfigure(0, weight=1, uniform="mark_pair")
        mark_step_row.columnconfigure(1, weight=1, uniform="mark_pair")
        button(mark_step_row, "prev_mark", lambda: self.step_marker(-1),
               icon_key="prev", tip_key="tip_prev_mark").grid(row=0, column=0, sticky="ew", padx=(0, 3))
        button(mark_step_row, "next_mark", lambda: self.step_marker(1),
               icon_key="next", tip_key="tip_next_mark").grid(row=0, column=1, sticky="ew", padx=(3, 0))

        # Frecvență: [Frecvență: ........ − +] | [căsuță MHz ........ Mergi]
        go_row = ttk.Frame(tune_box)
        go_row.pack(fill="x", pady=(0, RIGHT_GAP))
        go_row.columnconfigure(0, weight=1, uniform="go_pair")
        go_row.columnconfigure(1, weight=1, uniform="go_pair")
        go_left = ttk.Frame(go_row)
        go_left.grid(row=0, column=0, sticky="ew", padx=(0, 3))
        go_right = ttk.Frame(go_row)
        go_right.grid(row=0, column=1, sticky="ew", padx=(3, 0))
        label(go_left, "freq").pack(side="left")
        b_up = ttk.Button(go_left, text=ICONS["nudge_up"], width=3, command=lambda: self.nudge(1))
        b_up.pack(side="right")
        add_tip(b_up, "tip_nudge_up")
        b_down = ttk.Button(go_left, text=ICONS["nudge_down"], width=3, command=lambda: self.nudge(-1))
        b_down.pack(side="right", padx=(0, 3))
        add_tip(b_down, "tip_nudge_down")
        self.ent = ttk.Entry(go_right, width=9, justify="center")
        self.ent.pack(side="left", fill="x", expand=True)
        self.ent.bind("<Return>", lambda e: self.go_entry())
        self.ent.bind("<Key>", self._on_ent_key)
        self.ent.bind("<FocusOut>", lambda e: self.root.after(4000, self._release_ent))
        add_tip(self.ent, "tip_freq_entry")
        ttk.Label(go_right, text="MHz").pack(side="left", padx=(3, 0))
        btn_go = button(go_right, "go", self.go_entry, icon_key="go", tip_key="tip_go", width=5)
        btn_go.pack(side="right")

        pwr_row = ttk.Frame(tune_box)
        pwr_row.pack(fill="x")
        pwr_row.columnconfigure(0, weight=1, uniform="pwr_pair")
        pwr_row.columnconfigure(1, weight=1, uniform="pwr_pair")
        self.btn_power = button(pwr_row, "start", self.toggle_power, icon_key="start", tip_key="tip_start")
        self.btn_power.grid(row=0, column=0, sticky="ew", padx=(0, 3))
        self.btn_add_station = button(pwr_row, "add", self.add_station, icon_key="add", tip_key="tip_add")
        self.btn_add_station.grid(row=0, column=1, sticky="ew", padx=(3, 0))
        self.btn_clear_marks = button(pwr_row, "clear_marks", self.clear_all_markers,
                                      icon_key="clear", tip_key="tip_clear_marks")

        self._sep_after_tune = ttk.Separator(right, orient="horizontal")
        self._sep_after_tune.pack(fill="x", pady=(RIGHT_GAP, RIGHT_GAP))

        # --- Panou dreapta: 3) Audio & SDR ---
        audio_box = ttk.Frame(right)
        self._audio_box = audio_box
        audio_box.pack(fill="x", pady=(0, 0))
        sec_audio = label(audio_box, "audio_sdr", font=("TkDefaultFont", 9, "bold"), anchor="center")
        sec_audio.pack(fill="x", pady=(0, RIGHT_GAP))

        # Rând Gain | Corecție ppm: două jumătăți egale (simetric față de centru); widget-urile își păstrează înălțimea
        # normală, iar butonul „Corecție ppm” are înălțimea celorlalte butoane. În Radio FM rămâne doar Gain.
        sdr_row = ttk.Frame(audio_box)
        self._sdr_row = sdr_row
        sdr_row.pack(fill="x", pady=(0, RIGHT_GAP))
        sdr_row.columnconfigure(0, weight=1, uniform="sdr_half")
        sdr_row.columnconfigure(2, weight=1, uniform="sdr_half")
        self._gain_half = ttk.Frame(sdr_row)
        self._gain_half.grid(row=0, column=0, sticky="ew")
        self._sdr_sep = ttk.Separator(sdr_row, orient="vertical")
        self._sdr_sep.grid(row=0, column=1, sticky="ns", padx=5, pady=2)
        self._ppm_half = ttk.Frame(sdr_row)
        self._ppm_half.grid(row=0, column=2, sticky="ew")

        # Butoane comutator: apăsat = fundal albastru, ca la Squelch / Ieșire
        tstyle = ttk.Style(self.root)
        tstyle.configure("SqlAutoOn.TButton", background="#9ec5fe", foreground="#000000")
        tstyle.map("SqlAutoOn.TButton", background=[("active", "#86b7fe"), ("pressed", "#86b7fe")])
        self.gain_auto_var = tk.IntVar(value=1)
        self.gain_btn = ttk.Button(self._gain_half, text=self._tr("gain"), width=7, command=self._toggle_gain_auto)
        self.gain_btn.pack(side="left")
        self.i18n_widgets.append((self.gain_btn, "gain", None))
        add_tip(self.gain_btn, "tip_gain")
        self.gain_var = tk.StringVar(value="30")
        self.gain_combo = ttk.Combobox(self._gain_half, textvariable=self.gain_var, width=6, state="readonly",
                                       values=GAIN_VALUES)
        self.gain_combo.pack(side="right")          # se oprește la mijlocul panoului
        self.gain_combo.bind("<<ComboboxSelected>>", lambda e: self._on_gain_selected())
        add_tip(self.gain_combo, "tip_gain_val")

        self.ppm_var = tk.StringVar(value="0")
        ppm_spin = ttk.Spinbox(self._ppm_half, from_=-200, to=200, increment=1, width=4, textvariable=self.ppm_var,
                               command=self._on_ppm_changed)
        ppm_spin.pack(side="right")
        ppm_spin.bind("<Return>", lambda _e: self._on_ppm_changed())
        ppm_spin.bind("<FocusOut>", lambda _e: self._on_ppm_changed())
        add_tip(ppm_spin, "tip_ppm")
        # „Corecție ppm” nu e text, ci butonul care pornește calibrarea; valoarea e în câmpul din dreapta
        self.btn_cal = button(self._ppm_half, "ppm_lbl", self.open_calibration, tip_key="tip_cal",
                              padding=self._btn_padding())
        self.btn_cal.pack(side="left", fill="x", expand=True, padx=(0, 4))

        # Rând Filtru | valoare (lățimea benzii de recepție), același stil
        bw_row = ttk.Frame(audio_box)
        self.bw_row = bw_row
        bw_row.pack(fill="x", pady=(0, RIGHT_GAP))
        bw_row.columnconfigure(0, weight=1, uniform="bw_half")
        bw_row.columnconfigure(2, weight=1, uniform="bw_half")
        bw_left = ttk.Frame(bw_row)
        bw_left.grid(row=0, column=0, sticky="ew")
        ttk.Separator(bw_row, orient="vertical").grid(row=0, column=1, sticky="ns", padx=5, pady=2)
        bw_right = ttk.Frame(bw_row)
        bw_right.grid(row=0, column=2, sticky="ew")
        self.bw_lock_var = tk.IntVar(value=1)
        self.bw_btn = ttk.Button(bw_left, text=self._tr("bw_lbl"), width=7, command=self._toggle_bw_lock)
        self.bw_btn.pack(side="left")
        self.i18n_widgets.append((self.bw_btn, "bw_lbl", None))
        add_tip(self.bw_btn, "tip_bw_lock")
        self.bw_preset_var = tk.StringVar(value="")
        self.bw_combo = ttk.Combobox(bw_left, textvariable=self.bw_preset_var, state="readonly", width=8)
        self.bw_combo.pack(side="right")
        self.bw_combo.bind("<<ComboboxSelected>>", self._on_bw_preset)
        add_tip(self.bw_combo, "tip_bw_preset")
        ttk.Label(bw_right, text="kHz").pack(side="right", padx=(4, 0))
        self.bw_val_var = tk.StringVar(value="")
        self.bw_spin = ttk.Spinbox(bw_right, from_=2, to=40, increment=0.5, width=5, textvariable=self.bw_val_var,
                                   command=self._on_bw_value)
        self.bw_spin.pack(side="left", fill="x", expand=True)
        self.bw_spin.bind("<Return>", self._on_bw_value)
        self.bw_spin.bind("<FocusOut>", self._on_bw_value)
        add_tip(self.bw_spin, "tip_bw_val")

        # Selector rapid bandă în modul Aviație / Radioamatori (ascuns în FM)
        mode_controls_box = ttk.Frame(right)
        self._mode_controls_box = mode_controls_box
        self.upper_band_row = ttk.Frame(mode_controls_box)
        label(self.upper_band_row, "band_lbl").pack(side="left")
        self.upper_band_var = tk.StringVar(value="")
        self.upper_band_box = ttk.Combobox(
            self.upper_band_row,
            textvariable=self.upper_band_var,
            state="readonly",
            width=30,
            values=self._upper_band_values(),
        )
        self.upper_band_box.pack(side="right", fill="x", expand=True, padx=(6, 0))
        self.upper_band_box.bind("<<ComboboxSelected>>", lambda _e: self._on_right_band_selected())
        add_tip(self.upper_band_box, "tip_band_sel")

        # Reglaj Squelch pentru Aviație / Radioamatori (ascuns în FM)
        self.sql_row = ttk.Frame(mode_controls_box)
        self.sql_auto_var = tk.IntVar(value=0)
        style = ttk.Style(self.root)
        style.configure("SqlAutoOn.TButton", background="#9ec5fe", foreground="#000000")
        style.map("SqlAutoOn.TButton", background=[("active", "#8bb9fe"), ("pressed", "#8bb9fe")])
        self.sql_auto_btn = ttk.Button(
            self.sql_row,
            text=self._tr("squelch_lbl"),
            command=self._toggle_squelch_auto,
        )
        self.sql_auto_btn.pack(side="left", padx=(0, 6))
        self.i18n_widgets.append((self.sql_auto_btn, "squelch_lbl", None))
        add_tip(self.sql_auto_btn, "tip_squelch_auto")
        self.sql_var = tk.DoubleVar(value=12.0)
        self.lbl_sql_val = ttk.Label(self.sql_row, text="12 dB", width=7, anchor="e")
        self.lbl_sql_val.pack(side="right")
        self.sc_sql = ttk.Scale(self.sql_row, from_=0, to=50, variable=self.sql_var,
                                command=lambda _v: self._on_squelch_change(save=True))
        self.sc_sql.pack(side="left", fill="x", expand=True)
        add_tip(self.sc_sql, "tip_squelch")
        self._bind_wheel(self.sc_sql, 1, lambda: self._on_squelch_change(save=True))

        # Comutator Mesaje <-> Cascadă (mereu e selectat unul). Textele pornesc dinspre întrerupătorul din mijloc.
        self.decode_pkt_row = ttk.Frame(mode_controls_box)
        self.decode_pkt_row.columnconfigure(0, weight=1, uniform="view_side")
        self.decode_pkt_row.columnconfigure(2, weight=1, uniform="view_side")
        self.decode_pkt_var = tk.IntVar(value=1)        # 1 = mesaje (decodare activă); derivat din wf_var
        self.wf_var = tk.IntVar(value=0)                # 1 = cascadă
        self.lbl_view_msgs = label(self.decode_pkt_row, "view_msgs", anchor="e", cursor="hand2")
        self.lbl_view_msgs.grid(row=0, column=0, sticky="e", padx=(0, 8))
        self.view_switch = ToggleSwitch(self.decode_pkt_row, command=self._on_view_switch)
        self.view_switch.grid(row=0, column=1)
        self.lbl_view_wf = label(self.decode_pkt_row, "waterfall", anchor="w", cursor="hand2")
        self.lbl_view_wf.grid(row=0, column=2, sticky="w", padx=(8, 0))
        self.lbl_view_msgs.bind("<Button-1>", lambda _e: self._set_view(False))
        self.lbl_view_wf.bind("<Button-1>", lambda _e: self._set_view(True))
        add_tip(self.lbl_view_msgs, "tip_decode_pkt")
        add_tip(self.lbl_view_wf, "tip_waterfall")
        add_tip(self.view_switch, "tip_view_switch")

        # Volum: butonul „Volum” = mute (apăsat = fundal roșu deschis, ca la Squelch); slider-ul rămâne neschimbat
        volrow = ttk.Frame(audio_box)
        volrow.pack(fill="x", pady=(0, RIGHT_GAP))
        vstyle = ttk.Style(self.root)
        vstyle.configure("MuteOn.TButton", background="#ffb3b3", foreground="#000000")
        vstyle.map("MuteOn.TButton", background=[("active", "#ff9d9d"), ("pressed", "#ff9d9d")])
        self.mute_var = tk.IntVar(value=0)
        self.mute_btn = ttk.Button(volrow, text=self._tr("volume"), width=7, command=self._toggle_mute)
        self.mute_btn.pack(side="left", padx=(0, 6))
        self.i18n_widgets.append((self.mute_btn, "volume", None))
        add_tip(self.mute_btn, "tip_mute")
        self.lbl_vol_pct = ttk.Label(volrow, text="70%", width=4, anchor="e")
        self.lbl_vol_pct.pack(side="right", padx=(6, 0))
        self.vol_var = tk.DoubleVar(value=70)
        sc = ttk.Scale(volrow, from_=0, to=100, variable=self.vol_var, command=lambda v: self._on_volume())
        sc.pack(side="left", fill="x", expand=True)
        add_tip(sc, "tip_volume")
        self._bind_wheel(sc, 2, self._on_volume)

        outrow = ttk.Frame(audio_box)
        outrow.pack(fill="x", pady=(0, RIGHT_GAP))
        # „Ieșire” = buton: apăsat (fundal albastru, ca la Squelch) blochează lista, ca să nu schimbi dispozitivul din greșeală
        ostyle = ttk.Style(self.root)
        ostyle.configure("SqlAutoOn.TButton", background="#9ec5fe", foreground="#000000")
        ostyle.map("SqlAutoOn.TButton", background=[("active", "#86b7fe"), ("pressed", "#86b7fe")])
        self.out_lock_var = tk.IntVar(value=0)
        self.out_lock_btn = ttk.Button(outrow, text=self._tr("audio_out_btn"), width=7, command=self._toggle_out_lock)
        self.out_lock_btn.pack(side="left", padx=(0, 6))
        self.i18n_widgets.append((self.out_lock_btn, "audio_out_btn", None))
        add_tip(self.out_lock_btn, "tip_out_lock")
        self.audio_out_var = tk.StringVar()
        self.audio_out_box = ttk.Combobox(outrow, textvariable=self.audio_out_var, state="readonly",
                                          postcommand=self._refresh_audio_sinks)
        self.audio_out_box.pack(side="left", fill="x", expand=True)
        self.audio_out_box.bind("<<ComboboxSelected>>", lambda e: self._on_audio_sink_selected())
        add_tip(self.audio_out_box, "tip_audio_out")

        self._sep_after_audio = ttk.Separator(right, orient="horizontal")
        self._sep_after_audio.pack(fill="x", pady=(RIGHT_GAP, RIGHT_GAP))
        tv_air_row = ttk.Frame(right)
        self._tv_air_row = tv_air_row
        tv_air_row.pack(fill="x")
        self.btn_air_ham = button(tv_air_row, "air_ham_btn", self.toggle_air_ham_mode,
                                  icon_key="air_ham", tip_key="tip_air_ham")
        self.btn_air_ham.pack(fill="x", pady=(0, RIGHT_GAP))
        button(tv_air_row, "tv_release", self.release_for_tv,
               icon_key="tv_release", tip_key="tip_tv_release").pack(fill="x")

        self._sep_after_mode = ttk.Separator(right, orient="horizontal")
        self._sep_after_mode.pack(fill="x", pady=(RIGHT_GAP, RIGHT_GAP))
        self._sep_status = ttk.Separator(right, orient="horizontal")
        self._sep_status.pack(fill="x", pady=(RIGHT_GAP, RIGHT_GAP))

        # --- Panou dreapta: 4) Frecvență / RDS / informații ---
        status_box = ttk.Frame(right)
        self._status_box = status_box
        status_box.pack(fill="x")

        self.status_hdr = ttk.Frame(status_box)
        self.status_hdr.pack(fill="x", pady=(0, 4))
        self.rds_var = tk.IntVar(value=0)
        self.rds_btn = ttk.Checkbutton(
            self.status_hdr,
            text=self._tr("rds" if HAS_RDS_DEPS else "rds_na"),
            variable=self.rds_var,
            command=lambda: self._sync_rds_state(save=True),
        )
        self.rds_btn.pack(side="left")
        self.i18n_widgets.append((self.rds_btn, "rds" if HAS_RDS_DEPS else "rds_na", None))
        add_tip(self.rds_btn, "tip_rds" if HAS_RDS_DEPS else "tip_rds_na")

        self.lbl_hold_badge = ttk.Label(status_box, text="", font=("TkDefaultFont", 9, "bold"),
                                        anchor="center", justify="center")

        self.lbl_freq = ttk.Label(status_box, text="--.- MHz", font=("TkDefaultFont", 20, "bold"),
                                  anchor="center", justify="center")
        self.lbl_freq.pack(fill="x")

        self.lbl_ps = ttk.Label(status_box, text="", font=("TkDefaultFont", 13, "bold"),
                                wraplength=RIGHT_PANEL_W - 16, anchor="center", justify="center")
        self.lbl_ps.pack(fill="x", pady=(2, 0))

        self.lbl_rt = ttk.Label(status_box, text="", font=("TkDefaultFont", 9, "italic"),
                                wraplength=RIGHT_PANEL_W - 16, anchor="center", justify="center")
        self.lbl_rt.pack(fill="x", pady=(2, 2))

        self.lbl_info = ttk.Label(status_box, text="", font=("TkDefaultFont", 8),
                                  wraplength=RIGHT_PANEL_W - 16, anchor="center", justify="center")
        self.lbl_info.pack(fill="x", pady=(0, 0))

        # efectul corecției ppm: același font și aceeași mărime ca rândul de deasupra (RDS în FM, pas fin în Aviație/Radioamatori)
        self.lbl_ppm_effect = ttk.Label(status_box, text="", font=("TkDefaultFont", 8),
                                        wraplength=RIGHT_PANEL_W - 16, anchor="center", justify="center")
        self.lbl_ppm_effect.pack(fill="x", pady=(0, 6))

        self.status_messages_box = ttk.Frame(right)
        self.status = tk.StringVar(value="")
        ttk.Label(self.status_messages_box, textvariable=self.status, wraplength=RIGHT_PANEL_W - 16,
                  anchor="center", justify="center").pack(fill="x")

        self.lbl_warning = ttk.Label(self.status_messages_box, text="", font=("TkDefaultFont", 9, "bold"),
                                     wraplength=RIGHT_PANEL_W - 16, anchor="center", justify="center")
        self.lbl_warning.pack(fill="x", pady=(RIGHT_GAP, 0))

        # --- Conținut principal FM (stânga): scala + rândul caută/anulează/prag/listă + grila ---
        fm_container = ttk.Frame(m)
        fm_container.pack(fill="both", expand=True)
        self.fm_container = fm_container

        scale_row = ttk.Frame(fm_container)
        scale_row.pack(fill="x", pady=(self._scale_pad, 0))
        self._scale_row = scale_row
        self.tune_canvas = tk.Canvas(scale_row, height=SCALE_H, highlightthickness=0)
        self.tune_canvas.pack(fill="x", expand=True)
        self.tune_canvas.bind("<Configure>", self._draw_frequency_scale)
        self.tune_canvas.bind("<Button-1>", self._scale_click)
        self.tune_canvas.bind("<B1-Motion>", self._scale_click)

        row = ttk.Frame(fm_container)
        row.pack(fill="x", pady=(self._toolbar_pad, 0))
        self._toolbar_row = row
        row.bind("<Configure>", self._schedule_row_align)
        self.btn_scan = button(row, "scan", self.start_scan, icon_key="scan", tip_key="tip_scan")
        self.btn_scan.pack(side="left")
        self.btn_cancel = button(row, "cancel", lambda: self.scan_cancel.set(),
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
        fr = ttk.Frame(fm_container)
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

        self.prog = ttk.Progressbar(fm_container, maximum=1.0)

        # --- Conținut Aviație / Radioamatori (ascuns implicit, secțiuni separate prin bare) ---
        air_ham_container = ttk.Frame(m)
        self.air_ham_container = air_ham_container
        # Sus: graficul benzii alese; jos: mesaje / cascadă. Bara dintre ele se trage cu mouse-ul.
        self.air_ham_paned = ttk.PanedWindow(air_ham_container, orient="vertical")
        self.air_ham_paned.pack(fill="both", expand=True)
        self.air_ham_paned.bind("<Configure>", self._on_paned_configure)
        self.air_ham_paned.bind("<B1-Motion>", lambda _e: self.root.after_idle(self._clamp_sash))
        self.air_ham_paned.bind("<ButtonRelease-1>", self._on_sash_release)
        chart_pane = ttk.Frame(self.air_ham_paned)
        self.air_ham_paned.add(chart_pane, weight=1)

        # Zona 1: Aviație
        air_box = ttk.Frame(chart_pane)
        self.air_box = air_box
        air_hdr = ttk.Frame(air_box)
        air_hdr.pack(fill="x", pady=(0, 4))
        self.btn_scan_air = ttk.Button(
            air_hdr,
            text=self._btn_label("scan", self._tr("scan_toggle")),
            command=self.toggle_air_scan,
        )
        self.btn_scan_air.pack(side="left", padx=(0, 10))
        label(air_hdr, "threshold").pack(side="left")
        self.thr_air_var = tk.IntVar(value=10)
        sp_air = ttk.Spinbox(air_hdr, from_=3, to=30, width=4, textvariable=self.thr_air_var)
        sp_air.pack(side="left", padx=(2, 12))
        add_tip(sp_air, "tip_threshold_band")
        self.lbl_air_title = ttk.Label(air_hdr, text=self._tr("air_title"), font=("TkDefaultFont", 9, "bold"))
        self.lbl_air_title.pack(side="left")
        add_tip(self.btn_scan_air, "tip_scan_toggle")
        self.air_chart = BandActivityChart(
            air_box, AIR_BAND_START, AIR_BAND_END, AIR_STEP_MHZ, self._tune_aviation_from_chart, height=106
        )
        self.air_chart.pack(fill="both", expand=True)

        # Zona 2: Radioamatori
        ham_box = ttk.Frame(chart_pane)
        self.ham_box = ham_box
        ham_hdr = ttk.Frame(ham_box)
        ham_hdr.pack(fill="x", pady=(0, 4))
        self.btn_scan_ham = ttk.Button(
            ham_hdr,
            text=self._btn_label("scan", self._tr("scan_toggle")),
            command=self.toggle_ham_scan,
        )
        self.btn_scan_ham.pack(side="left", padx=(0, 10))
        label(ham_hdr, "threshold").pack(side="left")
        self.thr_ham_var = tk.IntVar(value=10)
        sp_ham = ttk.Spinbox(ham_hdr, from_=3, to=30, width=4, textvariable=self.thr_ham_var)
        sp_ham.pack(side="left", padx=(2, 12))
        add_tip(sp_ham, "tip_threshold_band")
        self.lbl_ham_title = ttk.Label(ham_hdr, text=band_name(self.ham_band, self.lang.get()), font=("TkDefaultFont", 9, "bold"))
        self.lbl_ham_title.pack(side="left")
        add_tip(self.btn_scan_ham, "tip_scan_toggle")

        h_start, h_end = self._current_ham_bounds()
        self.ham_chart = BandActivityChart(
            ham_box, h_start, h_end, BAND_BY_ID[self.ham_band][4], self._tune_ham_from_chart, height=106
        )
        self.ham_chart.pack(fill="both", expand=True)
        self._sync_chart_visibility()

        # Zona 3: Panou de carduri pentru mesaje decodificate
        msgs_box = ttk.Frame(self.air_ham_paned)
        self.air_ham_paned.add(msgs_box, weight=2)
        self.msgs_box = msgs_box
        msgs_hdr = ttk.Frame(msgs_box)
        msgs_hdr.pack(fill="x", pady=(0, 4))
        self.btn_clear_msgs = button(msgs_hdr, "msgs_clear", self.clear_messages, icon_key="clear")
        self.btn_clear_msgs.pack(side="left", padx=(0, 10))
        self.lbl_msgs_title = ttk.Label(msgs_hdr, text=self._tr("msgs_title"), font=("TkDefaultFont", 9, "bold"))
        self.lbl_msgs_title.pack(side="left")

        # Rezoluție + viteză cascadă: pe același rând cu „Curăță”, vizibile doar cât e bifată cascada
        self.wf_ctrl = ttk.Frame(msgs_hdr)
        self.wf_res_var = tk.StringVar(value=WF_DEFAULT_RES)
        self.wf_speed_var = tk.StringVar(value=WF_DEFAULT_SPEED)
        self.wf_sens_var = tk.StringVar(value=WF_DEFAULT_SENS)
        label(self.wf_ctrl, "wf_res").pack(side="left", padx=(0, 4))
        res_box = ttk.Combobox(self.wf_ctrl, textvariable=self.wf_res_var, state="readonly",
                               values=tuple(WF_RES), width=8)
        res_box.pack(side="left", padx=(0, 12))
        res_box.bind("<<ComboboxSelected>>", lambda _e: self._on_waterfall_change(save=True))
        add_tip(res_box, "tip_wf_res")
        label(self.wf_ctrl, "wf_speed").pack(side="left", padx=(0, 4))
        speed_box = ttk.Combobox(self.wf_ctrl, textvariable=self.wf_speed_var, state="readonly",
                                 values=tuple(WF_SPEEDS), width=5)
        speed_box.pack(side="left")
        speed_box.bind("<<ComboboxSelected>>", lambda _e: self._on_waterfall_change(save=True))
        add_tip(speed_box, "tip_wf_speed")
        label(self.wf_ctrl, "wf_sens").pack(side="left", padx=(12, 4))
        sens_box = ttk.Combobox(self.wf_ctrl, textvariable=self.wf_sens_var, state="readonly",
                                values=tuple(WF_SENS), width=6)
        sens_box.pack(side="left")
        sens_box.bind("<<ComboboxSelected>>", lambda _e: self._on_wf_sens_change())
        add_tip(sens_box, "tip_wf_sens")

        cards_wrap = ttk.Frame(msgs_box)
        cards_wrap.pack(fill="both", expand=True)
        self.cards_wrap = cards_wrap
        self.wf_wrap = ttk.Frame(msgs_box)
        # zoom + vârfuri: pe același rând cu rezoluția, viteza și sensibilitatea
        label(self.wf_ctrl, "wf_zoom").pack(side="left", padx=(12, 4))
        self.wf_zoom_var = tk.StringVar(value="×1")
        zoom_box = ttk.Combobox(self.wf_ctrl, textvariable=self.wf_zoom_var, state="readonly",
                                values=tuple(WF_ZOOM), width=4)
        zoom_box.pack(side="left")
        zoom_box.bind("<<ComboboxSelected>>", lambda _e: self._on_wf_zoom_change())
        add_tip(zoom_box, "tip_wf_zoom")
        self.wf_peak_var = tk.IntVar(value=0)
        peak_chk = ttk.Checkbutton(self.wf_ctrl, text=self._tr("wf_peak"), variable=self.wf_peak_var,
                                   command=self._on_wf_peak_change)
        peak_chk.pack(side="left", padx=(12, 0))
        self.i18n_widgets.append((peak_chk, "wf_peak", None))
        add_tip(peak_chk, "tip_wf_peak")
        self.wf_view = WaterfallView(self.wf_wrap, self._wf_click, self._wf_zoom_step,
                                     lambda khz: self._set_bw(self._bw_mode(), khz), height=210)
        self.wf_view.pack(fill="both", expand=True)
        self.msg_cards = MessageCardsPanel(cards_wrap, height=132)
        self.msg_sb = ttk.Scrollbar(cards_wrap, orient="vertical", command=self.msg_cards.yview)
        self.msg_cards.configure(yscrollcommand=self.msg_sb.set)
        self.msg_sb.pack(side="right", fill="y")
        self.msg_cards.pack(side="left", fill="both", expand=True)
        self.msg_cards.set_hint(self._tr("msgs_empty_hint"))

    def _sync_chart_visibility(self):
        """Un singur grafic: cel al benzii alese în „Bandă” (Aviație / VHF / UHF)."""
        show, hide = (self.air_box, self.ham_box) if self.active_upper_band == "air" else (self.ham_box, self.air_box)
        hide.pack_forget()
        show.pack(fill="both", expand=True)

    def _on_paned_configure(self, _e=None):
        h = self.air_ham_paned.winfo_height()
        if h < 220:
            return
        try:
            if not self._split_applied:             # prima afișare: proporția salvată
                self._split_applied = True
                self.air_ham_paned.sashpos(0, int(h * self._split))
            self._clamp_sash()
        except tk.TclError:
            pass

    def _clamp_sash(self):
        """Nici graficul, nici zona de jos nu pot fi trase până dispar."""
        h = self.air_ham_paned.winfo_height()
        if h < 220:
            return
        try:
            pos = self.air_ham_paned.sashpos(0)
            fixed = max(110, min(h - 150, pos))
            if fixed != pos:
                self.air_ham_paned.sashpos(0, fixed)
        except tk.TclError:
            pass

    def _on_sash_release(self, _e=None):
        self._clamp_sash()
        h = self.air_ham_paned.winfo_height()
        if h >= 220:
            try:
                self._split = max(0.15, min(0.7, self.air_ham_paned.sashpos(0) / h))
            except tk.TclError:
                return
            self._schedule_save()

    # ------------------------------------------------------------------ benzi (tabelul BANDS)
    def _band_id(self):
        return "air" if self.active_upper_band == "air" else self.ham_band

    def _band_mode(self):
        return BAND_BY_ID[self._band_id()][5]

    def _band_step(self):
        return BAND_BY_ID[self._band_id()][4]

    def _band_bounds(self):
        b = BAND_BY_ID[self._band_id()]
        return b[2], b[3]

    def _upper_band_values(self):
        lang = self.lang.get()
        return tuple(band_label(b[0], lang) for b in BANDS)

    def _current_ham_bounds(self):
        b = BAND_BY_ID[self.ham_band]
        return b[2], b[3]

    def _current_fine_step(self):
        """Pasul butoanelor − / + : Radio FM 0,1 MHz; în modul SDR depinde de bandă (vezi BAND_FINE)."""
        return band_fine_step(self._band_id()) if self.air_ham_active else 0.1

    def _sync_unsupported(self):
        """Marchează pe grafic părțile benzii pe care dongle-ul (tuner + HF detectat) nu le poate recepționa."""
        e = self.eng
        tt = e.tuner_type
        ranges = tuner_supported_ranges(tt, e.hf_mode)
        who = TUNER_NAMES.get(tt, "?") + (f", {e.device_label}" if e.device_label else "")
        long_txt = self._tr("unsupported_long", who, "; ".join(f"{a:g}–{z:g}" for a, z in ranges))
        short_txt = self._tr("unsupported_short")
        hf_below = HF_DIRECT_BELOW_HZ / 1e6
        for chart, bid in ((self.air_chart, "air"), (self.ham_chart, self.ham_band)):
            b = BAND_BY_ID[bid]
            note = ""
            if b[2] < hf_below:
                note = self._tr("hf_direct_note") if e.hf_mode == "direct" else (
                    "" if e.hf_mode == "native" else self._tr("unsupported_hf"))
            chart.set_unsupported(unsupported_parts(b[2], b[3], ranges), long_txt, short_txt, note)

    def _apply_ham_band(self, old=None):
        """Graficul generic trece pe banda `self.ham_band`: limite, pas, marcajele ei, titlu, zone nesuportate."""
        if old is not None and old != self.ham_band:
            self._band_markers[old] = dict(self.ham_chart.markers)
        b = BAND_BY_ID[self.ham_band]
        self.ham_chart.set_band(b[2], b[3], b[4])
        self.ham_chart.markers.update(self._band_markers.get(self.ham_band, {}))
        self.ham_chart.active_freq = None
        self.lbl_ham_title.configure(text=band_name(self.ham_band, self.lang.get()))
        self._sync_unsupported()

    def _select_band(self, bid, tune=True):
        """Trece pe banda `bid`: oprește scanările, schimbă graficul și reia ascultarea pe ultima frecvență de acolo."""
        self._stop_air_scan()
        self._stop_ham_scan()
        if bid == "air":
            self.active_upper_band = "air"
            self._apply_band_bw()
            self._sync_upper_band_combo()
            if tune:
                target = self.air_freq if self.air_freq is not None else BAND_BY_ID["air"][6]
                self._tune_aviation_from_chart(target)
                self.air_chart.active_freq = target
                self.air_chart.redraw()
            return
        old = self.ham_band
        self.active_upper_band = "ham"
        self.ham_band = bid
        self._apply_ham_band(old)
        self._apply_band_bw()
        self._sync_upper_band_combo()
        if tune:
            b = BAND_BY_ID[bid]
            f = self.ham_freqs.get(bid)
            if f is None or not (b[2] <= f <= b[3]):
                f = b[6]
            self._tune_ham_from_chart(f)
            self.ham_chart.active_freq = f
            self.ham_chart.redraw()
        self._save_cfg()

    def _on_ent_key(self, event):
        if event.char or event.keysym in ("BackSpace", "Delete"):
            self._ent_dirty = True

    def _release_ent(self):
        """După ce căsuța pierde focusul (ex. clic pe Go!), textul scris rămâne câteva secunde protejat
        de reîmprospătarea automată; apoi revine la frecvența curentă dacă n-a fost folosit."""
        try:
            if self.root.focus_get() is not self.ent:
                self._ent_dirty = False
        except Exception:
            self._ent_dirty = False

    # --- ieșire audio -------------------------------------------------------
    def _refresh_audio_sinks(self):
        sinks = list_pipewire_sinks()
        labels, seen = [], {}
        for _name, desc in sinks:
            seen[desc] = seen.get(desc, 0) + 1
            labels.append(desc if seen[desc] == 1 else f"{desc} ({seen[desc]})")
        self._sink_names = [n for n, _d in sinks]
        self._sink_labels = labels
        default_lbl = self._tr("audio_default")
        self.audio_out_box.configure(values=[default_lbl] + labels)
        if self.audio_sink_name in self._sink_names:
            self.audio_out_var.set(labels[self._sink_names.index(self.audio_sink_name)])
            self.eng.audio_sink = self.audio_sink_name
        else:                                   # dispozitivul salvat lipsește acum: ieșirea implicită
            self.audio_out_var.set(default_lbl)
            self.eng.audio_sink = None
        self.audio_out_box.state(["disabled"] if (not sinks or self.out_lock_var.get()) else ["!disabled"])

    def _on_audio_sink_selected(self):
        lbl = self.audio_out_var.get()
        if lbl in self._sink_labels:
            self.audio_sink_name = self._sink_names[self._sink_labels.index(lbl)]
        else:
            self.audio_sink_name = None
        self.eng.audio_sink = self.audio_sink_name
        self._save_cfg()
        self.audio_out_box.selection_clear()

    # ------------------------------------------------------------------ butoane comutator: Gain (auto) și Filtru (recomandat)
    @staticmethod
    def _toggle_look(btn, on):
        """Apăsat = fundal albastru, ca la Squelch și la Ieșire."""
        btn.configure(style="SqlAutoOn.TButton" if on else "TButton")
        btn.state(["pressed"] if on else ["!pressed"])

    def _effective_gain(self):
        return "auto" if self.gain_auto_var.get() else (self.gain_var.get() or "30")

    def _toggle_gain_auto(self):
        self.gain_auto_var.set(0 if self.gain_auto_var.get() else 1)
        self._apply_gain_ui()
        self.eng.set_gain(self._effective_gain())
        self._save_cfg()

    def _on_gain_selected(self):
        self.eng.set_gain(self._effective_gain())
        self._save_cfg()

    def _apply_gain_ui(self):
        auto = bool(self.gain_auto_var.get())
        self._toggle_look(self.gain_btn, auto)
        self.gain_combo.state(["disabled"] if auto else ["!disabled"])      # în automat, lista manuală e inactivă

    def _toggle_bw_lock(self):
        self.bw_lock_var.set(0 if self.bw_lock_var.get() else 1)
        self._apply_bw_lock_state()
        if self.bw_lock_var.get() and self.air_ham_active:
            self._apply_band_bw()                   # blocat = valoarea recomandată pentru banda curentă
        self._save_cfg()

    def _apply_bw_lock_state(self):
        locked = bool(self.bw_lock_var.get())
        self._toggle_look(self.bw_btn, locked)
        state = ["disabled"] if locked else ["!disabled"]
        self.bw_combo.state(state)
        self.bw_spin.state(state)
        self.wf_view.bw_locked = locked              # nici chenarul din cascadă nu se mai trage

    def _toggle_out_lock(self):
        self.out_lock_var.set(0 if self.out_lock_var.get() else 1)
        self._apply_out_lock()
        self._save_cfg()

    def _apply_out_lock(self):
        locked = bool(self.out_lock_var.get())
        self.out_lock_btn.configure(style="SqlAutoOn.TButton" if locked else "TButton")
        self.out_lock_btn.state(["pressed"] if locked else ["!pressed"])
        self.audio_out_box.state(["disabled"] if locked or not self._sink_names else ["!disabled"])

    def _toggle_squelch_auto(self):
        self.sql_auto_var.set(0 if self.sql_auto_var.get() else 1)
        self._on_squelch_auto_change(save=True)

    def _on_squelch_auto_change(self, save=True):
        auto = bool(self.sql_auto_var.get())
        if auto:
            self.sql_auto_btn.state(["pressed"])
            self.sql_auto_btn.configure(style="SqlAutoOn.TButton")
        else:
            self.sql_auto_btn.state(["!pressed"])
            self.sql_auto_btn.configure(style="TButton")
        self.eng.set_squelch_auto(auto)
        self.sc_sql.state(["disabled"] if auto else ["!disabled"])
        self._on_squelch_change(save=False)
        if save:
            self._save_cfg()

    def _on_squelch_change(self, save=True):
        val = round(float(self.sql_var.get()), 1)
        self.eng.squelch_db = val
        self.lbl_sql_val.configure(text=f"{self.eng.effective_squelch_db():.0f} dB")
        if self.air_ham_active and self.eng.running and self.eng.demod_mode in LISTEN_MODES:
            sql_txt = self._tr("sql_open" if self.eng.squelch_open else "sql_closed")
            self.lbl_rt.config(text=f"{self.eng.level_db:.1f} dB   |   {sql_txt}")
        if save:
            self._save_cfg()

    # ------------------------------------------------------------------ corecție ppm
    def _on_ppm_changed(self, *_):
        """Scrierea manuală sau săgețile: aplicăm după o scurtă pauză, ca să nu trimitem fiecare cifră tastată."""
        if self._ppm_after is not None:
            self.root.after_cancel(self._ppm_after)
        self._ppm_after = self.root.after(350, self._apply_ppm)

    def _apply_ppm(self):
        self._ppm_after = None
        try:
            v = int(round(float(self.ppm_var.get().replace(",", "."))))
        except ValueError:
            v = self._ppm
        v = max(-200, min(200, v))
        self.ppm_var.set(str(v))
        if v != self._ppm:
            self._ppm = v
            self._post(self._job_ppm, v)
        self._save_cfg()

    # ------------------------------------------------------------------ cascadă: zoom + vârfuri
    def _on_wf_zoom_change(self):
        self.wf_view.zoom = WF_ZOOM.get(self.wf_zoom_var.get(), 1)
        self.wf_view._invalidate()
        self._save_cfg()

    def _wf_zoom_step(self, direction):
        names = list(WF_ZOOM)
        i = names.index(self.wf_zoom_var.get()) if self.wf_zoom_var.get() in names else 0
        j = max(0, min(len(names) - 1, i + direction))
        if j != i:
            self.wf_zoom_var.set(names[j])
            self._on_wf_zoom_change()

    def _on_wf_peak_change(self):
        self.wf_view.set_peak_hold(bool(self.wf_peak_var.get()))
        self._save_cfg()

    # ------------------------------------------------------------------ asistentul de calibrare ppm
    def open_calibration(self):
        if MISSING_DEPS:
            return
        if self._cal_win is not None:
            self._cal_win.lift()
            return
        self._cancel_scans()
        win = tk.Toplevel(self.root)
        win.title(self._tr("cal_title"))
        win.transient(self.root)
        win.resizable(False, False)
        self._cal_win = win
        body = ttk.Frame(win, padding=12)
        body.pack(fill="both", expand=True)
        ttk.Label(body, text=self._tr("cal_intro"), wraplength=460, justify="left").pack(anchor="w", pady=(0, 10))
        row = ttk.Frame(body)
        row.pack(fill="x", pady=(0, 4))
        ttk.Label(row, text=self._tr("cal_src")).pack(side="left")
        labels = {self._tr("cal_src_gsm900"): "gsm900", self._tr("cal_src_gsm850"): "gsm850",
                  self._tr("cal_src_manual"): "manual"}
        self._cal_src_map = labels
        self._cal_src_var = tk.StringVar(value=next(iter(labels)))
        box = ttk.Combobox(row, textvariable=self._cal_src_var, values=list(labels), state="readonly", width=30)
        box.pack(side="left", padx=6)
        ref_row = ttk.Frame(body)
        ref_row.pack(fill="x", pady=(0, 8))
        ttk.Label(ref_row, text=self._tr("cal_ref")).pack(side="left")
        self._cal_ref_var = tk.StringVar(value="")
        self._cal_ref_entry = ttk.Entry(ref_row, textvariable=self._cal_ref_var, width=14, state="disabled")
        self._cal_ref_entry.pack(side="left", padx=6)
        box.bind("<<ComboboxSelected>>", lambda _e: self._cal_ref_entry.configure(
            state="normal" if labels.get(self._cal_src_var.get()) == "manual" else "disabled"))
        self._cal_prog = ttk.Progressbar(body, maximum=100, length=460)
        self._cal_prog.pack(fill="x", pady=(2, 6))
        self._cal_status = ttk.Label(body, text="", wraplength=460, justify="left")
        self._cal_status.pack(anchor="w", pady=(0, 8))
        btns = ttk.Frame(body)
        btns.pack(fill="x")
        self._cal_new_ppm = None
        self._cal_btn_start = ttk.Button(btns, text=self._tr("cal_start"), command=self._cal_start)
        self._cal_btn_stop = ttk.Button(btns, text=self._tr("cal_stop"), command=self._cal_cancel.set, state="disabled")
        self._cal_btn_apply = ttk.Button(btns, text=self._tr("cal_apply"), command=self._cal_apply, state="disabled")
        ttk.Button(btns, text=self._tr("cal_close"), command=self._cal_close).pack(side="right")
        self._cal_btn_apply.pack(side="right", padx=6)
        self._cal_btn_stop.pack(side="right", padx=6)
        self._cal_btn_start.pack(side="right", padx=6)
        win.protocol("WM_DELETE_WINDOW", self._cal_close)
        try:
            win.wait_visibility()
            win.grab_set()                         # modală: nimeni nu schimbă frecvența cât măsoară asistentul
        except tk.TclError:
            pass

    def _cal_start(self):
        source = self._cal_src_map.get(self._cal_src_var.get(), "gsm900")
        ref = 0.0
        if source == "manual":
            try:
                ref = float(self._cal_ref_var.get().replace(",", "."))
                if not 24.0 <= ref <= 1700.0:
                    raise ValueError
            except ValueError:
                self._cal_status.configure(text=self._tr("cal_err_ref"))
                return
        self._cancel_scans()
        self._cal_cancel = threading.Event()        # eveniment nou: cel vechi a fost setat de _cancel_scans
        self._cal_btn_start.configure(state="disabled")
        self._cal_btn_stop.configure(state="normal", command=self._cal_cancel.set)
        self._cal_btn_apply.configure(state="disabled")
        self._cal_new_ppm = None
        self._cal_prog["value"] = 0
        self._cal_status.configure(text="…")
        self._want_on = True
        self._post(self._job_calibrate, source, ref, self._cal_cancel)

    def _cal_progress(self, text, frac):
        if self._cal_win is not None:
            self._cal_status.configure(text=text)
            self._cal_prog["value"] = max(0.0, min(1.0, frac)) * 100

    def _cal_finish(self, result, error):
        if self._cal_win is None:
            return
        self._cal_btn_start.configure(state="normal")
        self._cal_btn_stop.configure(state="disabled")
        if result:
            new = max(-200, min(200, int(round(result["ppm"]))))
            lines = [self._tr("cal_result", new, int(result["p0"]))]
            lines += [self._tr("cal_detail", c["mhz"], c["ppm"], c["n"], c["std"]) for c in result["channels"]]
            lines.append(self._tr("cal_residual", result["ppm"] - result["p0"]))
            if len(result["channels"]) == 1 and result["channels"][0]["n"] > 1:
                lines.append(self._tr("cal_one_channel"))
            self._cal_status.configure(text="\n".join(lines))
            self._cal_prog["value"] = 100
            self._cal_new_ppm = new
            self._cal_btn_apply.configure(state="normal")
        else:
            self._cal_prog["value"] = 0
            self._cal_status.configure(text=error or self._tr("cal_cancelled"))

    def _cal_apply(self):
        if self._cal_new_ppm is None:
            return
        self.ppm_var.set(str(self._cal_new_ppm))
        self._apply_ppm()
        self._cal_status.configure(text=self._tr("cal_applied"))
        self._cal_btn_apply.configure(state="disabled")

    def _cal_close(self):
        self._cal_cancel.set()
        win, self._cal_win = self._cal_win, None
        if win is not None:
            try:
                win.grab_release()
            except tk.TclError:
                pass
            win.destroy()

    def _set_view(self, waterfall):
        if bool(self.wf_var.get()) != waterfall:
            self.wf_var.set(1 if waterfall else 0)
            self._on_waterfall_change(save=True)

    def _on_wf_sens_change(self):
        self.wf_view.sens_db = WF_SENS.get(self.wf_sens_var.get(), 0.0)
        self.wf_view._invalidate()                  # se aplică imediat și pe imaginea deja desenată
        self._save_cfg()

    def _on_view_switch(self):
        self._set_view(self.view_switch.right)

    def _on_waterfall_change(self, save=True):
        """Mesaje (decodare activă) și cascadă se exclud: mereu e activă exact una."""
        self.decode_pkt_var.set(0 if self.wf_var.get() else 1)
        self.eng.decode_packets = bool(self.decode_pkt_var.get())
        self.eng.reset_decoders()
        self._apply_waterfall_state()
        if save:
            self._save_cfg()

    def _apply_waterfall_state(self):
        e = self.eng
        on = bool(self.wf_var.get())
        e.wf_fft = WF_RES.get(self.wf_res_var.get(), WF_RES[WF_DEFAULT_RES])
        e.wf_rate = WF_SPEEDS.get(self.wf_speed_var.get(), WF_SPEEDS[WF_DEFAULT_SPEED])
        if on and self.air_ham_active and not e.wf_enabled:
            self.wf_view.clear()
            self._drain_queue(e.wf_q)
        self.wf_view.sens_db = WF_SENS.get(self.wf_sens_var.get(), 0.0)
        self.wf_view.zoom = WF_ZOOM.get(self.wf_zoom_var.get(), 1)
        if bool(self.wf_peak_var.get()) != self.wf_view.peak_hold:
            self.wf_view.set_peak_hold(bool(self.wf_peak_var.get()))
        e.wf_enabled = on and bool(self.air_ham_active)      # în Radio FM cascada nu se calculează deloc
        self.view_switch.set(on)
        self.lbl_view_msgs.configure(font=("TkDefaultFont", 9, "normal" if on else "bold"))
        self.lbl_view_wf.configure(font=("TkDefaultFont", 9, "bold" if on else "normal"))
        self._sync_bottom_panel()

    @staticmethod
    def _drain_queue(q):
        try:
            while True:
                q.get_nowait()
        except queue.Empty:
            pass

    def _sync_bottom_panel(self):
        """Zona de jos din modul Aviație / Radioamatori: mesaje recepționate SAU cascadă."""
        if self.wf_var.get():
            self.cards_wrap.pack_forget()
            self.wf_wrap.pack(fill="both", expand=True)
            self.wf_ctrl.pack(side="right")
            self.wf_view.wait_text = self._tr("wf_wait")
            self.wf_view._invalidate()
            self.lbl_msgs_title.pack_forget()           # titlul ar lua loc din rândul de opțiuni
        else:
            self.wf_wrap.pack_forget()
            self.wf_ctrl.pack_forget()
            self.cards_wrap.pack(fill="both", expand=True)
            self.lbl_msgs_title.configure(text=self._tr("msgs_title"))
            self.lbl_msgs_title.pack(side="left")

    def _wf_click(self, f):
        """Clic pe cascadă: acordare pe frecvența respectivă, la pasul benzii active."""
        lo, hi = self._band_bounds()
        step = self._current_fine_step()                   # clicul se rotunjește la pasul fin, nu la canalul întreg
        f = max(lo, min(hi, round(round(f / step) * step, 4)))
        if self.active_upper_band == "air":
            self._tune_aviation_from_chart(f)
        else:
            self._tune_ham_from_chart(f)

    def _wf_tick(self):
        """Desenează cascada și waveform-ul în pas cu viteza aleasă. Cât e oprită, verifică de 2 ori pe secundă."""
        delay = 500
        try:
            if self.air_ham_active and self.wf_var.get():
                rate = max(0.5, float(self.eng.wf_rate))
                delay = max(30, min(250, int(round(1000.0 / rate))))
                bw = self._bw[self._bw_mode()]                              # lățimea benzii de recepție (kHz)
                side = {"usb": 1, "lsb": -1}.get(self._band_mode(), 0)      # SSB: banda stă de o parte a purtătoarei
                self.wf_view.peak_snap = side == 0 and self._band_mode() != "fm"   # SSB și FM larg nu au un vârf de purtătoare
                if side != self.wf_view.bw_side or (bw != self.wf_view.bw_khz and not self.wf_view._drag):
                    self.wf_view.bw_khz, self.wf_view.bw_side = bw, side
                    self.wf_view._invalidate()
                items = []
                try:
                    while True:
                        items.append(self.eng.wf_q.get_nowait())
                except queue.Empty:
                    pass
                if items:
                    self.wf_view.add_rows(items)
                self.wf_view.render()
        except Exception:
            traceback.print_exc()
        finally:
            try:
                self.root.after(delay, self._wf_tick)
            except tk.TclError:
                pass

    def _sync_right_panel_mode(self):
        """Reordonează containerele panoului drept fără a modifica aspectul controalelor."""
        for _w in (self._status_box, self._sep_after_tune, self._mode_controls_box,
                   self._tune_box, self._audio_box, self._sep_after_audio,
                   self._tv_air_row, self._sep_after_mode, self._sep_status,
                   self.status_messages_box):
            _w.pack_forget()

        if self.air_ham_active:
            # Hold/frecvență/date semnal rămân în partea de sus.
            self._status_box.pack(fill="x")
            self._sep_after_tune.pack(fill="x", pady=(RIGHT_GAP, RIGHT_GAP))
            self._audio_box.pack(fill="x")
            self._sep_after_audio.pack(fill="x", pady=(RIGHT_GAP, RIGHT_GAP))
            self._tune_box.pack(fill="x")
            self._mode_controls_box.pack(fill="x", pady=(RIGHT_GAP * 2, 0))
            self._sep_after_mode.pack(fill="x", pady=(RIGHT_GAP * 2, RIGHT_GAP))
            self._tv_air_row.pack(fill="x")
            self._sep_status.pack(fill="x", pady=(RIGHT_GAP, RIGHT_GAP))
            self.status_messages_box.pack(fill="both", expand=True)

            self._sec_tune.configure(text=self._tr("tuning_air_ham"))
            self._step_row.pack_forget()
            self._mark_step_row.pack(fill="x", pady=(0, RIGHT_GAP), after=self._sec_tune)
            self.btn_add_station.grid_forget()
            self.btn_clear_marks.grid(row=0, column=1, sticky="ew", padx=(3, 0))
            self.upper_band_row.pack(fill="x", pady=(RIGHT_GAP, RIGHT_GAP * 2))
            self.sql_row.pack(fill="x", pady=(0, RIGHT_GAP))
            self.decode_pkt_row.pack(fill="x", pady=(0, RIGHT_GAP))
            self.status_hdr.pack_forget()
            self.lbl_hold_badge.pack(fill="x", pady=(0, 4), before=self.lbl_freq)
            self._sync_upper_band_combo()
        else:
            # FM: RDS/frecvență/date, Audio & SDR, apoi Tuning & Control.
            self._status_box.pack(fill="x")
            self._sep_after_tune.pack(fill="x", pady=(RIGHT_GAP, RIGHT_GAP))
            self._audio_box.pack(fill="x")
            self._sep_after_audio.pack(fill="x", pady=(RIGHT_GAP, RIGHT_GAP))
            self._tune_box.pack(fill="x")
            self._sep_after_mode.pack(fill="x", pady=(RIGHT_GAP, RIGHT_GAP))
            self._tv_air_row.pack(fill="x")
            self._sep_status.pack(fill="x", pady=(RIGHT_GAP, RIGHT_GAP))
            self.status_messages_box.pack(fill="both", expand=True)

            self._sec_tune.configure(text=self._tr("tuning"))
            self._mark_step_row.pack_forget()
            self._step_row.pack(fill="x", pady=(0, RIGHT_GAP), after=self._sec_tune)
            self.btn_clear_marks.grid_forget()
            self.btn_add_station.grid(row=0, column=1, sticky="ew", padx=(3, 0))
            self.upper_band_row.pack_forget()
            self.sql_row.pack_forget()
            self.decode_pkt_row.pack_forget()
            self.lbl_hold_badge.pack_forget()
            self.status_hdr.pack(fill="x", pady=(0, 4), before=self.lbl_freq)
            self._sync_bw_controls()

    def _sync_upper_band_combo(self):
        self.upper_band_box.configure(values=self._upper_band_values())
        self.upper_band_var.set(band_label(self._band_id(), self.lang.get()))
        self._sync_chart_visibility()               # un singur grafic: cel al benzii alese
        self._sync_bw_controls()
        self._sync_unsupported()

    def _on_right_band_selected(self):
        lang = self.lang.get()
        bid = next((b[0] for b in BANDS if band_label(b[0], lang) == self.upper_band_var.get()), None)
        if bid is not None:
            self._select_band(bid)

    def clear_all_markers(self):
        self.air_chart.clear_markers()
        self.ham_chart.clear_markers()
        self._band_markers.pop(self.ham_band, None)
        self._set_status_key("marks_cleared")

    def step_marker(self, direction):
        chart = self.air_chart if self.active_upper_band == "air" else self.ham_chart
        marks = chart.sorted_marker_freqs()
        if not marks:
            self._set_status_key("no_marks_yet")
            return
        cur = self._cur_freq()
        if direction > 0:
            nxt = next((f for f in marks if f > cur + 1e-5), marks[0])
        else:
            nxt = next((f for f in reversed(marks) if f < cur - 1e-5), marks[-1])
        chart.active_freq = nxt
        chart.set_hold(True)
        if self.active_upper_band == "air":
            self._tune_aviation_from_chart(nxt)
        else:
            self._tune_ham_from_chart(nxt)
        chart.redraw()

    def _update_msg_hint(self):
        """Cât timp lista e goală, arată ce canale se monitorizează și câte cadre s-au văzut."""
        cards = self.msg_cards.cards
        if not (cards and cards[0].get("hint")):
            return
        text = self._tr("msgs_empty_hint")
        e = self.eng
        if self.air_ham_active and e.decode_packets and e.running:
            freqs, sync, ok, bad = e.bank_status()
            if freqs:
                text += "\n" + self._tr("bank_active", ", ".join(f"{f:.3f}" for f in freqs), sync, ok, bad)
            else:
                text += "\n" + self._tr("bank_none")
        if text != getattr(self, "_last_hint", None):
            self._last_hint = text
            self.msg_cards.set_hint(text)

    def append_message(self, item_or_text):
        if not item_or_text:
            return
        if isinstance(item_or_text, dict):
            self.msg_cards.add_message(item_or_text)
        else:
            self.msg_cards.set_hint(str(item_or_text))

    def clear_messages(self):
        if self.wf_var.get():
            self.wf_view.clear()
            return
        self.msg_cards.clear_cards(self._tr("msgs_empty_hint"))

    def toggle_air_ham_mode(self):
        self._cancel_scans()
        self._set_air_ham_mode(not self.air_ham_active)

    def _air_ham_target(self):
        """(mod, frecvență) pe care se reia ascultarea la intrarea în modul SDR (banda curentă)."""
        if self.active_upper_band == "ham":
            b = BAND_BY_ID[self.ham_band]
            f = self.ham_freqs.get(self.ham_band)
            if f is None or not (b[2] <= f <= b[3]):
                f = b[6]
            return b[5], f
        f = self.air_freq
        if f is None or not (AIR_BAND_START <= f <= AIR_BAND_END):
            f = BAND_BY_ID["air"][6]
        return "am", f

    def _set_air_ham_mode(self, active, retune=True):
        self.air_ham_active = active
        if active:
            self._apply_band_bw()
            mode, f = self._air_ham_target()
            self.fm_container.pack_forget()
            self.air_ham_container.pack(fill="both", expand=True)
            self.btn_air_ham.configure(text=self._btn_label("air_ham", self._tr("air_ham_back")))
            self.air_chart.set_hold(True)
            self.ham_chart.set_hold(True)
            (self.air_chart if self.active_upper_band == "air" else self.ham_chart).active_freq = f
            if retune:
                self.tune(f, demod_mode=mode)
            else:                               # la pornirea programului: radioul se deschide după aceea
                self.eng.freq = f
                self.eng.demod_mode = mode
                self._ui_freq = f
            self._sync_right_panel_mode()
            self.air_chart.redraw()
            self.ham_chart.redraw()
            self.msg_cards.redraw()
            self._apply_waterfall_state()
        else:
            self._set_bw("fm", BW_DEFAULT["fm"], remember=False)    # în Radio FM filtrul e mereu cel recomandat
            self.air_ham_container.pack_forget()
            self.fm_container.pack(fill="both", expand=True)
            self.btn_air_ham.configure(text=self._btn_label("air_ham", self._tr("air_ham_btn")))
            self._sync_right_panel_mode()
            self.tune(self.fm_freq, demod_mode="fm")        # reia direct postul FM ascultat înainte
            if MISSING_DEPS:
                self._set_status_key("missing_deps")
            self._refresh_station_buttons(force_layout=True)
            self.root.after(100, self._align_toolbar_row)
            self._apply_waterfall_state()

    def _sync_scan_toggle_buttons(self):
        if self.air_scan_running:
            self.btn_scan_air.state(["selected", "pressed"])
        else:
            self.btn_scan_air.state(["!selected", "!pressed"])
        if self.ham_scan_running:
            self.btn_scan_ham.state(["selected", "pressed"])
        else:
            self.btn_scan_ham.state(["!selected", "!pressed"])

    def toggle_air_scan(self):
        if self.air_scan_running:
            self._stop_air_scan()
            self._set_status_key("band_scan_stopped")
        else:
            self._stop_ham_scan()
            self._start_air_scan()

    def toggle_ham_scan(self):
        if self.ham_scan_running:
            self._stop_ham_scan()
            self._set_status_key("band_scan_stopped")
        else:
            self._stop_air_scan()
            self._start_ham_scan()

    def _start_band_scan(self, kind):
        if MISSING_DEPS:
            return
        self.active_upper_band = kind
        self._sync_upper_band_combo()
        chart = self.air_chart if kind == "air" else self.ham_chart
        chart.set_hold(False)
        cancel = threading.Event()              # un eveniment NOU pentru fiecare scanare: fără curse între vechi și nou
        if kind == "air":
            self.air_scan_running, self._air_scan_cancel = True, cancel
        else:
            self.ham_scan_running, self._ham_scan_cancel = True, cancel
        self._want_on = True
        self._sync_scan_toggle_buttons()
        self._post(self._job_band_scan, kind, cancel)

    def _start_air_scan(self):
        self._start_band_scan("air")

    def _stop_air_scan(self):
        self.air_scan_running = False
        self._air_scan_cancel.set()
        self.air_chart.set_hold(True)
        self._sync_scan_toggle_buttons()

    def _start_ham_scan(self):
        self._start_band_scan("ham")

    def _stop_ham_scan(self):
        self.ham_scan_running = False
        self._ham_scan_cancel.set()
        self.ham_chart.set_hold(True)
        self._sync_scan_toggle_buttons()



    def _remember_freq(self, f, mode=None):
        if not self.air_ham_active:
            self.fm_freq = f
        elif self.active_upper_band == "air":
            self.air_freq = f
        else:
            self.ham_freqs[self.ham_band] = f

    def _tune_aviation_from_chart(self, freq_mhz):
        self.active_upper_band = "air"
        self._remember_freq(freq_mhz)
        self._stop_air_scan()
        self._stop_ham_scan()
        self.air_chart.set_hold(True)
        self.ham_chart.set_hold(True)
        self._sync_upper_band_combo()
        self._ui_freq = freq_mhz
        self._want_on = True
        self._post(self._job_tune, freq_mhz, "am", "air_listening")

    def _tune_ham_from_chart(self, freq_mhz):
        self.active_upper_band = "ham"
        self._remember_freq(freq_mhz)
        self._stop_air_scan()
        self._stop_ham_scan()
        self.air_chart.set_hold(True)
        self.ham_chart.set_hold(True)
        self._sync_upper_band_combo()
        self._ui_freq = freq_mhz
        self._want_on = True
        self._post(self._job_tune, freq_mhz, BAND_BY_ID[self.ham_band][5], "ham_listening")

    def _schedule_row_align(self, _event=None):
        if not self._align_pending:
            self._align_pending = True
            self.root.after_idle(self._align_toolbar_row)

    def _set_right_pad(self, v):
        self._right_pad = max(0, v)
        top = self._right_pad // 2
        self._sec_tune.pack_configure(pady=(top, RIGHT_GAP + self._right_pad - top))

    def _align_toolbar_row(self):
        """Aliniază scala la separatorul din dreapta; bara de scanare rămâne imediat sub scală."""
        self._align_pending = False
        if self.air_ham_active:
            return
        self.root.update_idletasks()
        if not self._sep_top.winfo_ismapped() or self._scale_row.winfo_height() <= 1:
            return

        base_top = self._scale_row.winfo_rooty() - self._scale_pad
        sep_y = self._sep_top.winfo_rooty() + self._sep_top.winfo_height() // 2
        want = max(0, sep_y - base_top - SCALE_AXIS_Y)
        if want != self._scale_pad:
            self._scale_pad = want
            self._scale_row.pack_configure(pady=(want, 0))
            self.root.update_idletasks()

        if self._toolbar_pad != TOOLBAR_MIN_GAP:
            self._toolbar_pad = TOOLBAR_MIN_GAP
            self._toolbar_row.pack_configure(pady=(TOOLBAR_MIN_GAP, 0))

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
        if self.air_ham_active:
            return
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
        self._highlight_active_station(force=True)

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

    def _highlight_active_station(self, force=False):
        cur = round(self._cur_freq(), 2)
        sig = (cur, self.selected_freq, len(self._station_buttons))
        if sig == self._hl_sig and not force:
            return
        self._hl_sig = sig
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
        """Oprește radioul (dacă rulează) și redă dongle-ul driverului TV. Merge mereu."""
        self._cancel_scans()
        self._want_on = False
        self._post(self._job_release)

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
        set_msg_lang(self.lang.get())
        self._sync_power_button()
        self.btn_air_ham.configure(
            text=self._btn_label("air_ham", self._tr("air_ham_back" if self.air_ham_active else "air_ham_btn"))
        )
        self.lbl_air_title.configure(text=self._tr("air_title"))
        self.lbl_ham_title.configure(text=band_name(self.ham_band, self.lang.get()))
        self._sync_bottom_panel()
        self._sync_bw_controls()
        self._sync_unsupported()
        self.btn_scan_air.configure(text=self._btn_label("scan", self._tr("scan_toggle")))
        self.btn_scan_ham.configure(text=self._btn_label("scan", self._tr("scan_toggle")))
        if self.msg_cards.cards and self.msg_cards.cards[0].get("hint"):
            self.msg_cards.set_hint(self._tr("msgs_empty_hint"))
        self._sync_right_panel_mode()
        self._refresh_audio_sinks()
        self._refresh_rec_ui()
        self._refresh_status_text()
        self._refresh_warning()
        if save:
            self._save_cfg()

    def _change_language(self):
        code = LANG_NAMES.get(self.lang_name_var.get(), "ro")
        self.lang.set(code)
        self._apply_translations(save=True)

    def _draw_frequency_scale(self, _event=None):
        c = self.tune_canvas
        c.delete("all")
        width = max(c.winfo_width(), 2)
        left, right = 12, width - 12
        y = SCALE_AXIS_Y                         # axa scalei
        c.create_line(left, y, right, y)
        px_per_mhz = (right - left) / (BAND_END - BAND_START)
        step = 0.1 if px_per_mhz >= 8 else (0.2 if px_per_mhz >= 4 else 0.5)
        count = int(round((BAND_END - BAND_START) / step))
        for i in range(count + 1):
            f = BAND_START + i * step
            x = left + (f - BAND_START) * px_per_mhz
            major = abs(f - round(f)) < 0.001
            mid = not major and abs(f * 2 - round(f * 2)) < 0.001
            tick = 15 if major else (10 if mid else 5)
            c.create_line(x, y - tick / 2, x, y + tick / 2)
            if major:
                c.create_text(x, y + 10, text=f"{f:.0f}", anchor="n")
        f = max(BAND_START, min(BAND_END, self.eng.freq))
        self._scale_sig = (round(self.eng.freq, 2), width)
        x = left + (f - BAND_START) * px_per_mhz
        c.create_line(x, y - 12, x, y + 10, width=2)              # indicator scurt
        lx = min(max(x, 40), width - 40)                          # textul nu iese din fereastră la capete
        c.create_text(lx, y - 14, text=f"{f:.1f} MHz", anchor="s")  # frecvența, deasupra indicatorului

    def _scale_click(self, event):
        width = self.tune_canvas.winfo_width()
        left, right = 12, width - 12
        if right <= left:
            return
        f = BAND_START + (event.x - left) / (right - left) * (BAND_END - BAND_START)
        self.tune(round(max(BAND_START, min(BAND_END, f)), 1), demod_mode="fm")

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
        cur = self._cur_freq()
        if d > 0:
            nxt = next((f for f in fs if f > cur + 0.01), fs[0])
        else:
            nxt = next((f for f in reversed(fs) if f < cur - 0.01), fs[-1])
        self.selected_freq = round(nxt, 2)
        self.tune(nxt, demod_mode="fm")

    # ======================================================================
    #  Control hardware: coadă de comenzi executate pe un singur fir
    # ======================================================================
    def _post(self, fn, *args):
        """Pune o comandă în coadă (doar din firul UI). Nu blochează."""
        self._snapshot_params()
        self._pending += 1
        self.jobs.put((fn, args))

    def _ctl_loop(self):
        while True:
            fn, args = self.jobs.get()
            try:
                fn(*args)
            except Exception as ex:
                traceback.print_exc()
                self.ui_q.put(("status_key", ("sdr_unavail_status", (str(ex)[:300],))))
            finally:
                self.ui_q.put(("job_done", None))

    def _cancel_scans(self):
        """Oprește orice scanare (FM sau bandă). Imediat, fără așteptare; firul de control iese singur."""
        self.scan_cancel.set()
        self._cal_cancel.set()
        self._stop_air_scan()
        self._stop_ham_scan()

    def _job_open(self, user=False, force=False):
        e, q = self.eng, self.ui_q
        if e.running:
            return True
        if MISSING_DEPS:
            return False
        try:
            e.ppm = self._ppm
            e.open(self._gain, force=force)
        except DeviceBusy as ex:
            who = ", ".join(ex.procs)
            q.put(("busy_ask", (who,)) if user else ("status_key", ("tv_busy_status", (who,))))
            return False
        except Exception as ex:
            q.put(("warning", ("sdr_unavail_warn",)))
            q.put(("status_key", ("sdr_unavail_status", (str(ex)[:300],))))
            return False
        q.put(("warning", (None,)))
        q.put(("status_key", ("listening", ())))
        q.put(("tuner", None))                      # tipul tunerului e cunoscut abia acum: actualizează zonele nesuportate
        return True

    def _job_startup(self):
        self.eng.guard.recover()
        self._job_open(user=False)

    def _job_tune(self, f, mode, status=None):
        e = self.eng
        if not e.running:
            e.freq, e.demod_mode = f, mode
            if not self._job_open(user=True):
                return
        e.audio_enabled = True
        e.tune(f, demod_mode=mode)
        if status:
            self.ui_q.put(("status_key", (status, ())))

    def _job_close(self):
        self.eng.close()
        self.ui_q.put(("status_key", ("stopped_free", ())))

    def _job_release(self):
        e = self.eng
        if e.running:
            e.close()
        else:
            e.guard.reattach()
        if not e.guard.detached:
            self.ui_q.put(("status_key", ("tv_free", ())))
        else:
            self.ui_q.put(("status", e.guard.last_error or self._tr("tv_err")))

    def _job_ppm(self, ppm):
        self.eng.set_ppm(ppm)

    def _job_calibrate(self, source, ref_mhz, cancel):
        e, q = self.eng, self.ui_q
        prev_f, prev_mode = e.freq, e.demod_mode
        result = error = None
        try:
            if not e.running and not self._job_open(user=True):
                error = _L("cal_err_radio")
                return
            e.stop_recording()
            result = run_ppm_calibration(e, source, ref_mhz, e.ppm, cancel,
                                         lambda text, frac: q.put(("cal_progress", (text, frac))))
        except Exception as ex:
            error = str(ex)
        finally:
            e.mode = "listen"
            try:
                e.audio_enabled = True
                if e.running and not self._closing:
                    e.tune(prev_f, demod_mode=prev_mode)
            except Exception:
                pass
            q.put(("cal_result", (result, error)))

    def _job_shutdown(self):
        try:
            self.eng.close()
        finally:
            self._closed_evt.set()

    def _job_fm_scan(self, thr, cancel):
        e, q = self.eng, self.ui_q
        prev = e.freq
        try:
            if not e.running and not self._job_open(user=True):
                return
            prev = e.freq
            q.put(("status_key", ("scanning", ())))
            found = e.scan_band(thr, lambda p: q.put(("progress", p)), cancel)
            if found is None:
                q.put(("status_key", ("scan_cancelled", ())))
                return
            old = dict(self.stations)
            q.put(("set_stations", {round(f, 2): old.get(round(f, 2), "") for f in found}))
            q.put(("status_key", ("scan_done", (len(found),))))
        except Exception as ex:
            q.put(("status_key", ("scan_err", (str(ex),))))
        finally:
            e.mode = "listen"
            try:
                e.audio_enabled = True
                if e.running and not self._closing:
                    e.tune(prev, demod_mode="fm")
            except Exception:
                pass
            q.put(("scan_done", None))      # mereu: altfel interfața rămâne blocată în "scanare"

    def _job_band_scan(self, kind, cancel):
        e, q = self.eng, self.ui_q
        b = BAND_BY_ID["air" if kind == "air" else self.ham_band]
        start_m, end_m, step_m, mode = b[2], b[3], b[4], b[5]
        half_bw = max(5e3, self._bw[bw_key(mode)] * 500.0)              # jumătate din lățimea canalului (Hz)
        try:
            if not e.running and not self._job_open(user=True):
                return
            e.stop_recording()
            e.demod_mode = mode
            q.put(("status_key", ("air_scan_on" if kind == "air" else "ham_scan_on", ())))
            while not cancel.is_set() and e.running:
                pos = start_m
                while pos < end_m - 1e-6 and not cancel.is_set() and e.running:
                    hits = e.scan_window_step(pos, end_m, step_m, half_bw, self.band_thr[kind], cancel, pace_sleep=0.04)
                    if hits and not cancel.is_set():
                        q.put(("band_hits", (kind, hits)))
                    pos += 1.45
        finally:
            e.mode = "listen"
            if e.running and not self._closing:     # revine pe frecvența ascultată, nu rămâne pe fereastra de scanare
                try:
                    mode, f = self._air_ham_target()
                    e.audio_enabled = True
                    e.tune(f, demod_mode=mode)
                except Exception:
                    pass
            q.put(("scan_ended", (kind, cancel)))

    def _check_system_status(self):
        if MISSING_DEPS:
            self._set_warning("missing_deps_warn", " | ".join(MISSING_DEPS))
            self._set_status_key("missing_deps")
            self.btn_power.config(state="disabled")
            self.btn_scan.config(state="disabled")
        else:
            self._want_on = True
            self._post(self._job_startup)

    def start_radio(self, user=False, force=False):
        if not MISSING_DEPS:
            self._want_on = True
            self._post(self._job_open, user, force)

    def toggle_power(self):
        """Start/Stop. Merge MEREU: întâi anulează orice scanare, apoi pune comanda în coadă."""
        self._cancel_scans()
        self._want_on = not self._want_on
        if self._want_on:
            self.start_radio(user=True)
        else:
            self._post(self._job_close)

    def tune(self, f, demod_mode=None, status=None):
        if self.scanning:                       # o scanare FM în curs: o oprim, iar acordarea așteaptă în coadă
            self.scan_cancel.set()
        if demod_mode is None:
            demod_mode = self.eng.demod_mode if self.air_ham_active else "fm"
        if not self.air_ham_active:
            f = max(64.0, min(110.0, round(f, 2)))
        else:
            lo, hi = self._band_bounds()
            f = max(lo, min(hi, round(float(f), 4)))
        self.selected_freq = round(f, 2)
        self._ui_freq = f
        self._remember_freq(f, demod_mode)
        self._ent_dirty = False
        self._want_on = True
        self._post(self._job_tune, f, demod_mode, status)
        self._highlight_active_station()
        self._save_cfg()

    def nudge(self, direction):
        step = self._current_fine_step()
        mode = self.eng.demod_mode if self.air_ham_active else "fm"
        if self.air_ham_active:
            self._stop_air_scan()
            self._stop_ham_scan()
        self.tune(round(self._cur_freq() + direction * step, 4), demod_mode=mode)

    def go_entry(self):
        try:
            val = float(self.ent.get().replace(",", "."))
        except ValueError:
            self._set_status_key("invalid_freq")
            return
        if not self.air_ham_active:
            self.tune(val, demod_mode="fm")
            return
        self._stop_air_scan()
        self._stop_ham_scan()
        lo, hi = self._band_bounds()
        if not (lo - 1e-9 <= val <= hi + 1e-9):             # în afara benzii curente: trece pe banda care o conține
            bid = next((b[0] for b in BANDS if b[2] - 1e-9 <= val <= b[3] + 1e-9), None)
            if bid is not None:
                self._select_band(bid, tune=False)
        self.tune(val, demod_mode=self._band_mode())

    def _btn_padding(self, hpad=3):
        """Padding orizontal mic, dar cel vertical al temei: butonul are aceeași înălțime ca restul butoanelor."""
        try:
            parts = str(ttk.Style(self.root).lookup("TButton", "padding") or "5").replace("{", "").replace("}", "").split()
            vpad = int(float(parts[1] if len(parts) > 1 else parts[0]))
        except (ValueError, IndexError):
            vpad = 5
        return (hpad, vpad)

    def _schedule_save(self):
        """Salvare amânată: tragerea unui slider/chenar nu scrie fișierul la fiecare mișcare."""
        if self._save_after is None:
            self._save_after = self.root.after(500, self._flush_save)

    def _flush_save(self):
        self._save_after = None
        self._save_cfg()

    def _bind_wheel(self, scale, step, on_change):
        """Mouse deasupra slider-ului + rotița = mută slider-ul, fără clic. Linux: Button-4/5; Windows/macOS: MouseWheel."""
        def on_wheel(event):
            if scale.instate(["disabled"]):
                return "break"
            up = getattr(event, "num", 0) == 4 or getattr(event, "delta", 0) > 0
            lo, hi = float(scale.cget("from")), float(scale.cget("to"))
            scale.set(max(lo, min(hi, float(scale.get()) + (step if up else -step))))
            on_change()                         # apelat direct: nu depindem de -command al lui ttk.Scale
            return "break"                      # nu derulează și lista de posturi
        for seq in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            scale.bind(seq, on_wheel)

    # ------------------------------------------------------------------ filtru (lățimea benzii de recepție)
    def _bw_mode(self):
        return bw_key(self._band_mode()) if self.air_ham_active else "fm"

    def _sync_sdr_rows(self):
        """Radio FM: filtrul e mereu cel recomandat pentru FM comercial, deci fără rând de filtru și fără corecție ppm."""
        fm = not self.air_ham_active
        if fm:
            self.bw_row.pack_forget()
            self.lbl_ppm_effect.pack_forget()
            self._sdr_sep.grid_remove()
            self._ppm_half.grid_remove()
            self._gain_half.grid_configure(columnspan=1)
            self.gain_combo.pack_configure(side="right", fill="none", expand=False, padx=0)
        else:
            self._gain_half.grid_configure(columnspan=1)
            self.gain_combo.pack_configure(side="right", fill="none", expand=False, padx=0)
            self._sdr_sep.grid()
            self._ppm_half.grid()
            self.bw_row.pack(fill="x", pady=(0, RIGHT_GAP), after=self._sdr_row)
            self.lbl_ppm_effect.pack(fill="x", pady=(0, 6), after=self.lbl_info)

    def _sync_bw_controls(self):
        """Presetările, limitele și valoarea afișată urmează modul curent (WFM / AM / NFM / SSB)."""
        self._sync_sdr_rows()
        mode = self._bw_mode()
        lo, hi = BW_RANGE[mode]
        self.bw_spin.configure(from_=lo, to=hi, increment={"fm": 10.0, "ssb": 0.1}.get(mode, 0.5))
        self.bw_combo.configure(values=[n for n, _k in BW_PRESETS[mode]] + [self._tr("bw_custom")])
        self.wf_view.bw_limits = (lo, hi)
        self._bw_show(mode)

    def _bw_show(self, mode):
        v = self._bw[mode]
        self.bw_val_var.set(f"{v:g}")
        name = next((n for n, k in BW_PRESETS[mode] if abs(k - v) < 1e-6), None)
        self.bw_preset_var.set(name or self._tr("bw_custom"))

    def _set_bw(self, mode, khz, remember=True):
        lo, hi = BW_RANGE[mode]
        khz = round(max(lo, min(hi, float(khz))), 2)
        self._bw[mode] = khz
        self.eng.set_bandwidth(mode, khz)
        if remember and self.air_ham_active and bw_key(self._band_mode()) == mode:
            self._band_bw[self._band_id()] = khz            # ce alegi tu pe o bandă se păstrează pentru ea
        if mode == self._bw_mode():
            self._bw_show(mode)
        self._schedule_save()

    def _apply_band_bw(self):
        """Filtrul urmează banda: blocat = mereu cel recomandat; deblocat = ce ai ales tu pe ea data trecută (altfel recomandat)."""
        bid = self._band_id()
        khz = band_rec_bw(bid) if self.bw_lock_var.get() else self._band_bw.get(bid, band_rec_bw(bid))
        self._set_bw(bw_key(BAND_BY_ID[bid][5]), khz, remember=False)

    def _on_bw_preset(self, _e=None):
        mode = self._bw_mode()
        name = self.bw_preset_var.get()
        for n, k in BW_PRESETS[mode]:
            if n == name:
                self._set_bw(mode, k)
                return
        self.bw_spin.focus_set()                    # „Personalizat”: scrii tu valoarea
        self._bw_show(mode)

    def _on_bw_value(self, _e=None):
        mode = self._bw_mode()
        try:
            self._set_bw(mode, float(self.bw_val_var.get().replace(",", ".")))
        except ValueError:
            self._bw_show(mode)

    def _on_volume(self):
        val = float(self.vol_var.get())
        self.eng.volume = val / 100.0
        self.lbl_vol_pct.config(text=f"{round(val)}%")

    def _toggle_mute(self):
        self.mute_var.set(0 if self.mute_var.get() else 1)
        self._on_mute()

    def _on_mute(self):
        muted = bool(self.mute_var.get())
        self.eng.muted = muted
        self.mute_btn.configure(style="MuteOn.TButton" if muted else "TButton")
        self.mute_btn.state(["pressed"] if muted else ["!pressed"])

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
            threading.Thread(target=self.eng.stop_recording, daemon=True).start()
            self._refresh_rec_ui()
            return
        if not (HAS_FFMPEG and self.eng.running and not self.scanning):
            return
        freq = self.eng.freq
        name = self.stations.get(round(freq, 2), "").strip()
        prefix = name or ("FM" if not self.air_ham_active else ("AIR" if self.active_upper_band == "air" else self.ham_band.upper()))
        label = f"{prefix}_{self._fmt_freq(freq)}MHz"
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
        if tip.text != text:
            tip.set_text(text)

    def _refresh_rec_ui(self):
        """Starea butonului REC (activ doar cât se redă, cu ffmpeg instalat) și textele din tooltip-uri."""
        elapsed = self.eng.rec_elapsed()
        can = HAS_FFMPEG and self.eng.running and not self.scanning and not (self.air_scan_running or self.ham_scan_running)
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
        self.scanning = True
        self.scan_cancel = threading.Event()
        self.prog.pack(fill="x", pady=(8, 0))
        self.prog["value"] = 0
        self.btn_scan.config(state="disabled")
        self.btn_cancel.config(state="normal")
        self._want_on = True
        self._post(self._job_fm_scan, self._int_var(self.thr_var, 10), self.scan_cancel)



    def _poll(self):
        """Buclă la 200 ms. Orice eroare e prinsă și reprogramarea se face MEREU (altfel interfața rămâne moartă)."""
        try:
            self._drain_ui_queue()
            self._drain_decoded()
            self._refresh_labels()
        except Exception:
            traceback.print_exc()
        finally:
            try:
                self.root.after(200, self._poll)
            except tk.TclError:
                pass

    def _drain_ui_queue(self):
        try:
            while True:
                kind, val = self.ui_q.get_nowait()
                try:
                    self._handle_ui_event(kind, val)
                except Exception:
                    traceback.print_exc()       # un eveniment stricat nu le blochează pe celelalte
        except queue.Empty:
            pass

    def _handle_ui_event(self, kind, val):
        if kind == "status_key":
            self._set_status_key(val[0], *val[1])
        elif kind == "status":
            self._set_status_text(val)
        elif kind == "warning":
            self._set_warning(*val)
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
            self._highlight_active_station(force=True)
            self._save_cfg()
        elif kind == "band_hits":
            band_kind, hits = val
            (self.air_chart if band_kind == "air" else self.ham_chart).record_hits(hits)
        elif kind == "scan_ended":
            band_kind, ev = val                 # ignorăm scanările vechi, înlocuite între timp
            if band_kind == "air" and ev is self._air_scan_cancel:
                self._stop_air_scan()
            elif band_kind == "ham" and ev is self._ham_scan_cancel:
                self._stop_ham_scan()
        elif kind == "busy_ask":
            if messagebox.askyesno(self.root.title(), self._tr("tv_busy_ask", val[0]), parent=self.root):
                self._want_on = True
                self._post(self._job_open, True, True)
            else:
                self._want_on = False
                self._set_status_key("tv_busy_status", val[0])
        elif kind == "tuner":
            self._sync_unsupported()
        elif kind == "cal_progress":
            self._cal_progress(*val)
        elif kind == "cal_result":
            self._cal_finish(*val)
        elif kind == "job_done":
            self._pending = max(0, self._pending - 1)
            if self._pending == 0:
                self._want_on = self.eng.running

    def _drain_decoded(self):
        try:
            while True:
                self.msg_cards.add_message(self.eng.decoded_msgs.get_nowait())
        except queue.Empty:
            pass
        self._update_msg_hint()

    def _refresh_labels(self):
        e = self.eng
        sig = (self._ppm, round(e.freq, 3), self.lang.get())
        if sig != self._ppm_sig:                    # efectul corecției: deplasarea frecvenței la banda curentă
            self._ppm_sig = sig
            self.lbl_ppm_effect.config(text=self._tr("ppm_effect", self._ppm * e.freq / 1000.0, e.freq)
                                       if self._ppm else self._tr("ppm_none"))
        if e.error:
            self._set_status_text(e.error)
            e.error = None
        e.check_recording()
        self._drain_rec_events()
        self._refresh_rec_ui()
        if e.running != self._last_running:
            self._last_running = e.running
            self._sync_power_button()

        fmt_main = f"{e.freq:.4f}".rstrip("0").rstrip(".") if e.demod_mode != "fm" else f"{e.freq:.1f}"
        self.lbl_freq.config(text=f"{fmt_main} MHz")

        if self.air_ham_active:
            (self.air_chart if self.active_upper_band == "air" else self.ham_chart).active_freq = e.freq
            now = time.time()
            self.air_chart.prune_expired(now)
            self.ham_chart.prune_expired(now)
            (self.air_chart if self.active_upper_band == "air" else self.ham_chart).redraw_if_changed()   # doar graficul vizibil
            if self.sql_auto_var.get():
                self.lbl_sql_val.config(text=f"{e.effective_squelch_db():.0f} dB")
            is_scanning_any = self.air_scan_running or self.ham_scan_running
            self.lbl_hold_badge.config(text=self._tr("hold_off" if is_scanning_any else "hold_on"))
        else:
            if self._scale_sig != (round(e.freq, 2), self.tune_canvas.winfo_width()):
                self._draw_frequency_scale()
            self._highlight_active_station()

        try:
            has_focus = self.root.focus_get() is self.ent
        except Exception:
            has_focus = False
        if not has_focus and not self._ent_dirty:
            self.ent.delete(0, "end")
            self.ent.insert(0, fmt_main)

        known = self.stations.get(round(e.freq, 2), "")
        if e.running:
            if e.demod_mode == "fm" and e.rds_enabled and HAS_RDS_DEPS:
                r = e.rds
                self.lbl_ps.config(text=r.ps_text().strip() or known)
                self.lbl_rt.config(text=r.rt_text())
                if r.n_groups == 0:
                    rds_state = self._tr("rds_no_data")
                elif time.time() - r.last_group_t < 3:
                    rds_state = self._tr("rds_ok")
                else:
                    rds_state = self._tr("rds_lost")
                self.lbl_info.config(
                    text=f"{rds_state}   {self._tr('pi_lbl')}: {r.pi_hex()}   {self._tr('gen_lbl')}: {r.pty_name()}")
            elif self.air_ham_active:
                sql_txt = self._tr("sql_open" if e.squelch_open else "sql_closed")
                self.lbl_ps.config(text=band_name(self._band_id(), self.lang.get()))
                self.lbl_rt.config(text=f"{e.level_db:.1f} dB   |   {sql_txt}" if e.demod_mode in LISTEN_MODES else "")
                self.lbl_info.config(text=self._tr("fine_step_khz", f"{self._current_fine_step() * 1000:g}"))
            else:
                self.lbl_ps.config(text=known)
                self.lbl_rt.config(text="")
                self.lbl_info.config(text=self._tr("rds_off"))
        else:
            self.lbl_ps.config(text=known)
            self.lbl_rt.config(text="")
            if not MISSING_DEPS:
                self.lbl_info.config(text=self._tr("stopped_hint"))

    def on_close(self):
        """Închide fereastra imediat; curățenia (rtl_tcp, driver TV) se face în fundal, cu timp limită."""
        if self._closing:
            return
        self._closing = True
        self._cancel_scans()
        try:
            self._save_cfg()
        except Exception:
            traceback.print_exc()
        self.root.withdraw()
        self._post(self._job_shutdown)
        self._close_deadline = time.time() + 15.0
        self._finish_close()

    def _finish_close(self):
        if self._closed_evt.is_set() or time.time() > self._close_deadline:
            timed_out = not self._closed_evt.is_set()
            try:
                self.root.destroy()
            finally:
                if timed_out:                   # firul de control e blocat în kernel/USB: nu ne mai oprește nimic
                    os._exit(0)
            return
        self.root.after(100, self._finish_close)

# ============================================================================
#  10. MAIN
# ============================================================================
def main():
    root = tk.Tk()
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
