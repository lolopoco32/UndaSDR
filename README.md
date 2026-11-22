# UndaSDR RTL-SDR

A lightweight FM radio application with a graphical interface for RTL-SDR USB dongles, built with Python and Tkinter.

UndaSDR receives and demodulates the FM broadcast band, plays audio through ALSA/PipeWire, scans for stations, stores favorite stations, decodes RDS information, and records audio. It also includes an Aviation / Ham Radio mode with interactive band charts, continuous scanning, squelch control, and packet/data message decoding.

The application is designed for Linux and supports RTL-SDR devices based on Realtek DVB-T chipsets, including compatible Astrometa dongles.

## Changelog

### Added
* **Aviation & Ham Radio Mode**: Switch from standard FM radio to listen across aviation AM frequencies (`118–137 MHz`) and ham radio bands (`144–146 MHz` VHF and `430–440 MHz` UHF).
* **Interactive Band Charts & HOLD**: View live signal markers on resizable band charts, click directly on a chart to tune, use **HOLD** to keep markers from fading while listening, jump between detected markers, or clear them anytime.
* **Continuous Band Scanning**: Scan aviation or ham bands continuously with a toggle button and stop easily with another click or by picking a frequency on the chart.
* **Squelch Control**: Adjust the squelch threshold in aviation and ham mode to quiet background static when no signal is present.
* **Packet & Data Message Cards**: Decode readable text and packet messages on tuned frequencies and view them as clean cards in a dedicated panel with a clear button.
* **Fine Tuning Steps**: Step frequencies using band-appropriate increments (`25 kHz` for aviation, `12.5 kHz` for ham radio, and `0.1 MHz` for FM).

### Changed
* **Right Sidebar Layout**: Reorganized the right panel when switching to Aviation / Ham mode so tuning controls, band selection, squelch, packet decoding, and marker **HOLD** status are right at hand.
* **Frequency Input & Tuning**: Expanded frequency entry and step controls to support finer decimal frequencies and direct band switching.
* **Saved Settings**: Remember your selected ham band, squelch level, and packet decoding preference alongside your existing configuration.
* **Translations**: Updated Romanian, English, and Italian interface labels and tooltips for all new modes, controls, and status messages.

## Features

- **FM radio reception** across the 87.5–108.0 MHz broadcast band.
- **Aviation & Ham Radio mode** covering aviation AM (`118–137 MHz`) and ham radio bands (`144–146 MHz` VHF and `430–440 MHz` UHF) with AM and NFM demodulation.
- **Interactive band activity charts** with persistent markers, marker **HOLD**, marker navigation, and manual clearing.
- **Continuous band scanning** for aviation and ham frequencies.
- **Squelch control** to filter out background noise when listening to aviation or ham signals.
- **Packet and data message decoding** displayed in a dedicated message card panel.
- **Automatic station scanning** with an adjustable signal-detection threshold.
- **Favorite station list** with custom station names.
- **Quick tuning** using the frequency scale, frequency entry, tuning buttons, or saved stations.
- **RDS decoding** for station name (PS), radio text (RT), program identification (PI), and program type (PTY).
- **Audio controls**, including volume, mute, and tuner gain selection.
- **Audio recording** to WAV, FLAC, MP3, or AAC/M4A.
- **ALSA/PipeWire playback** through `aplay`.
- **Automatic DVB driver management**: the application temporarily detaches the kernel DVB driver while using the dongle as an SDR and attempts to reattach it when the radio stops.
- **TV tuner recovery** after radio use, so compatible TV applications can use the dongle again.
- **Automatic configuration saving**, including stations, frequency, volume, gain, language, recording preferences, and window geometry.
- **Multilingual interface**: Romanian, English, and Italian.
- **Single-file application**: the program is currently distributed as one Python file.

## Requirements

### Hardware

- An RTL-SDR-compatible USB dongle.
- A Linux computer.
- An FM antenna suitable for the local broadcast band.

The available frequency range and reception quality depend on the tuner, antenna, and local radio environment.

### Software

The required packages can be installed from the Debian/Ubuntu repositories:

```bash
sudo apt update
sudo apt install rtl-sdr alsa-utils python3-tk python3-numpy
```

Optional packages:

```bash
# Enables RDS decoding
sudo apt install python3-scipy

# Enables audio recording
sudo apt install ffmpeg
```

| Package / tool | Required | Purpose |
|---|---|---|
| Python 3 | Yes | Runs the application |
| `python3-tk` | Yes | Graphical user interface |
| `python3-numpy` | Yes | FM demodulation, DSP, and scanning |
| `rtl-sdr` (`rtl_tcp`) | Yes | Communicates with the RTL-SDR dongle |
| `alsa-utils` (`aplay`) | Yes | Audio playback |
| `python3-scipy` | No | RDS decoding |
| `ffmpeg` | No | Audio recording and encoding |

No Python packages need to be installed with `pip` when using the packages listed above.

**Optional feature behavior:**
- Without SciPy, normal FM radio reception and playback still work, but RDS decoding is disabled.
- Without FFmpeg, radio reception still works, but the recording controls are disabled.

## Installation

Clone the repository:

```bash
git clone https://github.com/lolopoco32/UndaSDR.git
cd UndaSDR
```

Install the required dependencies:

```bash
sudo apt update
sudo apt install rtl-sdr alsa-utils python3-tk python3-numpy
```

Install the optional dependencies if needed:

```bash
sudo apt install python3-scipy ffmpeg
```

Make the script executable (optional):

```bash
chmod +x radiosdr.py
```

## Running

Start the application with:

```bash
python3 radiosdr.py
```

Or, if the executable permission has been set:

```bash
./radiosdr.py
```

The application opens the **UndaSDR RTL-SDR** graphical interface.

## USB permissions

> [!IMPORTANT]
> **USB PERMISSIONS — READ THIS BEFORE CHANGING ANYTHING**
>
> If UndaSDR can already access your RTL-SDR dongle, **you do not need to do anything in this section**. Many Linux distributions install RTL-SDR udev rules automatically. The rules may be located in `/lib/udev/rules.d/`, `/usr/lib/udev/rules.d/`, or `/etc/udev/rules.d/`.
>
> Do not create another rules file just because the example below exists. First check whether your system already has a working rule. Also, **do not run UndaSDR with `sudo` as a permissions workaround**. Configure USB access for your normal user instead.

Linux uses *udev rules* to decide which users and groups can access USB devices. If permissions are wrong, the application may report that it cannot access the dongle or cannot detach the DVB kernel driver.

### Step 1 — Check whether it already works

1. Connect the RTL-SDR dongle.
2. Open a terminal and run:

   ```bash
   lsusb
   ```

3. Find the line that describes your RTL-SDR. It will look similar to this (the numbers and description may be different):

   ```text
   Bus 001 Device 004: ID 0bda:2838 Realtek Semiconductor Corp. RTL2838 DVB-T
   ```

   In this example:
- `0bda` is the **Vendor ID** (VID).
- `2838` is the **Product ID** (PID).
- `001` is the USB bus number.
- `004` is the device number.

   **Use the IDs shown on your own computer.** Do not copy the example IDs unless they match your dongle.

4. Check whether your normal user can access the USB device. Replace `001` and `004` with the Bus and Device numbers from your `lsusb` output:

   ```bash
   ls -l /dev/bus/usb/001/004
   ```

   If the permissions include `rw` for your user or an accessible group, access may already be configured. For example, `crw-rw-rw-` means all local users can read and write the device. A group-based rule may instead show something like `root plugdev` with `rw` permissions for the group.

   The Bus and Device numbers can change when you unplug and reconnect the dongle, or after a reboot. Run `lsusb` again if the path no longer exists.

**If the dongle is accessible and UndaSDR starts normally, stop here. No extra udev rule is needed.**

### Method 1 — Use the udev rules already installed (recommended first step)

RTL-SDR packages often install rules automatically. Check the common rule directories with:

```bash
ls /etc/udev/rules.d/
ls /lib/udev/rules.d/ | grep -i rtl
ls /usr/lib/udev/rules.d/ | grep -i rtl
```

Some systems use `/lib` as a link to `/usr/lib`, so it is normal if the same rule appears in more than one listing.

You can search the rules for common RTL-SDR IDs with:

```bash
sudo grep -RiE 'rtl|0bda|2832|2838' \
  /etc/udev/rules.d/ /lib/udev/rules.d/ /usr/lib/udev/rules.d/ 2>/dev/null
```

If you find a rule matching your dongle's VID and PID, reconnect the dongle and try UndaSDR as your normal user. You usually do not need to add another rule.

### Method 2 — Create a simple rule (easiest, but less restrictive)

Use this method if no existing rule matches your dongle and you want the simplest setup. It grants read/write access to **all local users** for the matching USB device. This is convenient on a personal computer, but it is less restrictive than the group-based method below.

1. Open a new rules file:

   ```bash
   sudo nano /etc/udev/rules.d/99-rtlsdr.rules
   ```

2. Add this one-line rule. Replace the example IDs with the VID and PID from your own `lsusb` output:

   ```udev
   SUBSYSTEM=="usb", ATTRS{idVendor}=="0bda", ATTRS{idProduct}=="2838", MODE="0666"
   ```

3. Save the file in Nano:
- Press **Ctrl+O**, then **Enter** to save.
  - Press **Ctrl+X** to exit.

   If the file already exists and is empty, that is okay — it simply contains no rules yet. Add the rule, save it, and exit.

4. Tell Linux to reload the rules:

   ```bash
   sudo udevadm control --reload-rules
   sudo udevadm trigger --subsystem-match=usb
   ```

5. Unplug the RTL-SDR dongle and plug it back in. Then check its permissions again with `lsusb` and `ls -l` as described in Step 1.

6. Start UndaSDR normally:

   ```bash
   python3 radiosdr.py
   ```

### Method 3 — Use a dedicated group (more restrictive)

This method grants access only to users who belong to the `plugdev` group. It is a better choice on a computer with multiple user accounts, provided your distribution uses the `plugdev` group.

1. Check whether the group exists:

   ```bash
   getent group plugdev
   ```

2. If the command prints a line beginning with `plugdev:`, the group already exists. If it prints nothing, create it:

   ```bash
   sudo groupadd --system plugdev
   ```

3. Add your current user to the group:

   ```bash
   sudo usermod -aG plugdev "$USER"
   ```

4. Create or edit the rules file:

   ```bash
   sudo nano /etc/udev/rules.d/99-rtlsdr.rules
   ```

5. Add the rule, replacing the example IDs with your own:

   ```udev
   SUBSYSTEM=="usb", ATTRS{idVendor}=="0bda", ATTRS{idProduct}=="2838", MODE="0660", GROUP="plugdev"
   ```

6. Save the file (**Ctrl+O**, **Enter**, **Ctrl+X**) and reload the rules:

   ```bash
   sudo udevadm control --reload-rules
   sudo udevadm trigger --subsystem-match=usb
   ```

7. Unplug and reconnect the dongle.
8. **Log out of your Linux session and log back in** so the new group membership takes effect. A reboot also works, but is not normally necessary.
9. Check your groups:

   ```bash
   groups
   ```

   You should see `plugdev` in the output. Then run UndaSDR as your normal user.

### How to choose a method

| Situation | What to do |
|---|---|
| UndaSDR already accesses the dongle | Do nothing — keep the existing rules. |
| An installed RTL-SDR rule matches your dongle | Reconnect the dongle and test it before adding anything. |
| Personal computer, simplest setup wanted | Method 2 (`MODE="0666"`). |
| Prefer access limited to selected users | Method 3 (`MODE="0660"`, group `plugdev`). |

### Troubleshooting

- **The rule does not seem to take effect:** check that the VID/PID are correct, reload the rules, then physically unplug and reconnect the dongle.
- **The device path changed:** run `lsusb` again. The Bus and Device numbers can change after reconnecting.
- **You used the group method but it still says permission denied:** log out and back in, then check `groups` to confirm that `plugdev` is listed.
- **There are already several RTL-SDR rule files:** do not delete them blindly. They may have been installed by your Linux distribution or RTL-SDR packages. First check whether one already grants access. If you add a local rule, the `99-` filename makes it run late in the usual rule ordering, but avoid unnecessary duplicate rules.
- **It works only when launched with `sudo`:** this indicates a permissions or environment issue. Fix the udev rule instead of running the graphical application as root.

UndaSDR's DVB driver management uses the USB device node under `/dev/bus/usb/`. It does not require root privileges when your normal user already has the necessary USB permissions.

## Using the application

### Tuning and playback

- Press **Start** to initialize the SDR and start radio playback.
- Enter a frequency in MHz and press **Tune**.
- Use the frequency scale to select a frequency.
- Use the previous/next controls to move between saved stations.
- Press **Stop** to stop playback and release the device.

The default tuning frequency is **98.3 MHz**.

### Aviation and Ham Radio mode

- Switch between standard FM mode and **Aviation / Ham mode** from the right sidebar.
- Choose between Aviation AM (`118–137 MHz`), Ham VHF NFM (`144–146 MHz`), and Ham UHF NFM (`430–440 MHz`).
- Click on a band chart to tune directly to a frequency and keep markers in **HOLD**.
- Toggle **Scan** on a band to scan continuously, or click again / click a frequency on the chart to stop scanning.
- Use the previous/next marker buttons to step through detected markers or clear all markers when needed.
- Adjust **Squelch** to control when audio opens on a signal, and toggle **Packet / data decode** to display decoded messages in the message cards panel.

### Scanning for stations

1. Start the radio if it is not already running.
2. Select a detection threshold in dB.
3. Press **Scan**.
4. Wait for the scan to complete, or press **Cancel** to interrupt it.

The scan covers the **87.5–108.0 MHz** FM band.

The detection threshold controls the balance between sensitivity and false detections:
- Lower values can detect weaker stations but may produce more false positives.
- Higher values can reduce false detections but may miss weaker stations.
- A value around **10–12 dB** is a suggested starting point.

The resulting station list can be edited manually.

### Managing saved stations

- **Add channel** — add a frequency and a custom station name.
- **Rename** — change the name of a saved station.
- **Delete** — remove the selected station.
- **Clear** — remove all saved stations.
- Select a station button to tune directly to that frequency.
- Right-click a station button to edit its name.

Saved stations are restored when the application is launched again.

### RDS information

When the optional SciPy dependency is installed, enable **RDS** to decode supported broadcast information:

- **PS** — Program Service name.
- **RT** — Radio Text.
- **PI** — Program Identification code.
- **PTY** — Program Type.

RDS availability and decoding reliability depend on the received signal and whether the broadcaster transmits RDS data.

### Audio controls

The interface provides:
- Volume adjustment.
- Mute.
- Automatic or manual tuner gain.
- Audio playback through `aplay`, using PipeWire when the PipeWire ALSA device is available.

### Recording

Audio recording requires FFmpeg.

1. Start radio playback.
2. Tune to the desired station.
3. Choose a recording format: WAV, FLAC, MP3, or AAC.
4. Optionally change the recording directory.
5. Press **REC** to start recording.
6. Press the recording button again to stop and save the file.

The default recording directory is:

```text
~/Videos/UndaSDR/
```

The application uses the system's configured XDG Videos directory when available.

Recordings are made at the full audio level and are **not affected by the playback volume or mute setting**.

An active recording is automatically stopped and saved when the station changes, the radio is stopped, the dongle is released for TV use, or the application closes.

## DVB driver management

Many RTL-SDR-compatible dongles can also function as DVB-T television receivers. Linux may automatically attach the `dvb_usb_rtl28xxu` kernel driver to the device.

UndaSDR manages this situation automatically:

1. Before starting the SDR, it checks whether the DVB driver is attached to the dongle.
2. It checks whether a TV application is currently using the DVB device.
3. It temporarily detaches the DVB driver so that `rtl_tcp` can access the tuner.
4. When the radio stops, it attempts to restore the DVB driver.
5. It attempts to wake the TV frontend so that TV applications can use the tuner again.

The application also saves temporary driver state so it can attempt recovery after an unexpected shutdown.

**Important:** Starting the radio while a TV application is using the tuner may interrupt TV playback. The application warns about detected processes and asks for confirmation before taking over the device.

A **Release for TV** control is also available to stop the radio and return the dongle to the DVB driver.

This mechanism does not require adding the DVB driver to a blacklist or physically reconnecting the USB device.

## Configuration

User preferences are stored automatically in:

```text
~/.config/rtl_fm_gui.json
```

The configuration includes:

- Saved stations and their names.
- Last tuned frequency.
- Volume and mute state.
- RDS setting.
- Tuner gain.
- Station scanning threshold.
- Squelch level, selected ham band, and packet decoding preference.
- Recording directory and format.
- Interface language.
- Window size and position.

The application restores these preferences on the next launch.

## Technical overview

UndaSDR is implemented in a single Python file and is organized into independent sections:

| Component | Description |
|---|---|
| Dependency detection | Checks for NumPy, SciPy, `rtl_tcp`, `aplay`, and FFmpeg |
| DSP | FIR filtering, power spectrum calculation, peak detection, FM/AM/NFM demodulation, and message decoding |
| RDS decoder | Demodulates and decodes RDS groups and station information |
| DVB driver guard | Detaches and reattaches the Linux DVB kernel driver |
| RTL-TCP client | Starts `rtl_tcp` locally and receives IQ samples over TCP |
| Audio output | Converts demodulated audio to PCM and sends it to `aplay` |
| Recorder | Uses FFmpeg to encode audio recordings |
| Engine | Coordinates SDR input, DSP, audio playback, recording, and scanning |
| Internationalization | Romanian, English, and Italian interface translations |
| GUI | Tkinter-based graphical interface with band charts and message cards |

### Signal processing parameters

The current implementation uses:

| Parameter | Value |
|---|---:|
| FM tuning band | 87.5–108.0 MHz |
| Aviation AM band | 118.0–137.0 MHz (`25 kHz` step) |
| Ham VHF / UHF NFM bands | 144.0–146.0 MHz and 430.0–440.0 MHz (`12.5 kHz` step) |
| SDR sample rate | 1,920,000 samples/s |
| First decimation factor | 8 |
| Multiplex sample rate | 240,000 samples/s |
| Second decimation factor | 5 |
| Audio sample rate | 48,000 samples/s |
| De-emphasis | 50 µs |
| Audio output | 16-bit signed PCM, stereo |

The same mono audio signal is sent to both output channels.

## Troubleshooting

### The application cannot find `rtl_tcp`

Install the RTL-SDR utilities:

```bash
sudo apt install rtl-sdr
```

### The application cannot find `aplay`

Install ALSA utilities:

```bash
sudo apt install alsa-utils
```

### NumPy is missing

Install it with:

```bash
sudo apt install python3-numpy
```

### The dongle is busy

Close applications that may be using the DVB tuner, such as TV viewing or recording software, and try again.

If you choose to take over a busy tuner, its current TV session may be interrupted.

### No audio is heard

- Check the system audio output.
- Make sure the application is not muted.
- Check the volume level.
- Verify that `aplay` works on your system.
- Check that the dongle and antenna are connected correctly.
- Try another frequency with a known strong signal.

### RDS is unavailable

Install SciPy and restart the application:

```bash
sudo apt install python3-scipy
```

### Recording is unavailable

Install FFmpeg and restart the application:

```bash
sudo apt install ffmpeg
```

### The TV tuner is not available after radio use

Use **Release for TV** or stop the radio normally. The application attempts to reattach the DVB driver and initialize the TV frontend. If the operating system or device does not allow recovery, reconnecting the dongle may be necessary.

## Limitations

- Linux is required by the current implementation because it relies on Linux USB, DVB, and process interfaces.
- The application expects the `rtl_tcp` utility and an RTL-SDR-compatible device.
- RDS decoding requires the optional SciPy dependency.
- Recording requires the optional FFmpeg dependency.
- Station and band scanning detect signal peaks; it does not guarantee that every detected frequency is a usable signal.
- Reception quality depends on hardware, antenna placement, interference, and local signal strength.
- DVB driver recovery depends on the Linux kernel, device state, and USB permissions.

## Contributing

Bug reports, suggestions, and improvements are welcome.

When reporting an issue, please include:
- Linux distribution and version.
- Python version.
- RTL-SDR dongle model.
- Relevant application error messages.
- Steps needed to reproduce the issue.

## License

This project is licensed under the GNU General Public License v3.0 (GPLv3). Anyone is free to modify and redistribute this software, provided that any derivative works are also open-sourced under the same license terms.