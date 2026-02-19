# 🎤 Vocal Riyaaz for Indian Classical Singing Practice Tool

A real-time pitch detection and practice application built for Indian classical singers.  
Hear any sargam note on a synthesised harmonium, sing it back, and get instant visual feedback on your accuracy.

---

## ✨ Features

### 🎹 Sa Setup with Piano Keyboard
- Full chromatic keyboard spanning **C2 to E4** (every practical Sa position)
- Each key shows its **exact equal-temperament frequency** (A4 = 440 Hz)
- **Voice range bands** highlighted on the keyboard i.e teal for male (C3–G3), amber for female (G3–D4)
- Click any key to hear it, then confirm it as your Sa
- Voice-type quick-jump presets (Bass, Baritone, Tenor, Mezzo, Soprano)
- All 12 sargam notes update automatically the moment you set Sa

### 🎵 Free Practice
- Real-time pitch detection using **YIN algorithm** (FFT-vectorised, < 1 ms per frame)
- Click any sargam note button to hear it played as a harmonium tone
- **Glow circle** pulses gold while singing, green when you match a note
- Horizontal **pitch meter** shows cents sharp/flat with colour zones
- **Frequency history graph** with sargam note gridlines as reference
- Stability percentage shows how steadily you are holding a pitch
- Raga filter restricts detection to notes of a chosen raga

### 🎯 Guided Riyaaz
- Full **HEAR → SING → FEEDBACK** pedagogical loop (how a guru actually teaches)
- Choose an exercise sequence: Aaroh, Avaroh, Full Saptaka, custom intervals, or random
- App plays each note → shows countdown → you sing → scored on % of frames on-pitch
- **Live graph and pitch meter visible throughout** same feedback as Free Practice
- Note-by-note results with accuracy bars shown in real time
- Results saved to Session Stats automatically

### 📊 Session Stats
- Bar chart showing accuracy percentage per note across all sessions
- Average cents deviation table tells you exactly which notes your voice drifts on
- Persists across Free Practice and Guided sessions until cleared

### 🥁 Metronome & Sa Drone
- Configurable BPM (40–200) with accented downbeat
- Selectable time signatures: 3, 4, 6, 7, 8 beats per bar
- Continuous Sa + Pa drone (tanpura / shruti box style) for constant pitch reference
- Both run independently in background threads, no impact on detection

---

## 🖥️ Screenshots

| Sa Setup | Free Practice | Guided Riyaaz |
|----------|--------------|---------------|
| Piano keyboard with voice range bands | Glow circle + sargam keyboard | HEAR→SING loop with live graph |

---

## 🚀 Installation

**Requirements:** Python 3.10 or higher (tested on 3.12.2)

```bash
# 1. Clone the repository
git clone https://github.com/Umarii101/Voice_Tuner.git
cd Voice_Tuner

# 2. Create a virtual environment (recommended)
python -m venv venv

# On Windows:
venv\Scripts\activate
# On macOS / Linux:
source venv/bin/activate

# 3. Install dependencies
pip install -r requirements.txt

# 4. Run
python main.py
```

### PyAudio on Windows
If `pip install pyaudio` fails on Windows, install the pre-built wheel:
```bash
pip install pipwin
pipwin install pyaudio
```

### PyAudio on macOS
```bash
brew install portaudio
pip install pyaudio
```

---

## 🎼 How to Use

### Step 1 — Find Your Sa
Open the app and go to **① Sa Setup**.  
Click keys on the piano keyboard until you find the note that feels like "home" to your voice.  
Press **✅ Confirm This is My Sa**.  
All 12 sargam notes will tune themselves to your Sa automatically.

> **Tip:** If you own a harmonium, find which physical key you normally call Sa and select it here.

### Step 2 — Free Practice
Go to **② Free Practice** and press **▶ START**.  
Click any note button to hear the harmonium tone, then sing it.  
The glow circle turns **green** when your voice matches the note within tolerance.

### Step 3 — Guided Riyaaz
Go to **③ Guided Riyaaz**, choose an exercise sequence, and press **▶ Start Session**.  
The app plays each note, waits, then listens to you sing.  
After each note you'll see how many percent of the time you were on pitch.

### Step 4 — Review Stats
Go to **④ Session Stats** to see which notes you consistently nail and which need more work.

---

## ⚙️ Configuration

All user-tunable settings live in a clearly marked block near the top of `__init__` in `main.py`.  
Open the file and look for:

```python
# ╔══════════════════════════════════════════════════════════════════╗
# ║              USER CONFIGURATION — EDIT HERE                    ║
# ╠══════════════════════════════════════════════════════════════════╣
```

### Note Tone Duration
Controls how long a note plays when you click a sargam button or a piano key:

```python
self.NOTE_TONE_DURATION = 1.5   # ← CHANGE THIS NUMBER
```

| Value | Effect |
|-------|--------|
| `0.5` | Quick tap / flick |
| `1.0` | Short reference —> good for fast drills |
| `1.5` | **Default** —> comfortable listen time |
| `2.5` | Longer hold —> good for matching pitch before singing |
| `4.0` | Sustained tone —> meditative / slow riyaaz |

---

## 🏗️ Architecture Notes

| Component | Design decision |
|-----------|----------------|
| **Pitch detection** | YIN algorithm, FFT-vectorised — runs in the capture thread, never blocks UI |
| **Threading model** | `_audio_capture` thread → `result_queue` → `_poll_results` on UI thread |
| **Sa as source of truth** | `get_note_freq(name)` computes Hz from `sa_base` on every call —> no cached frequencies |
| **Tone playback** | Additive synthesis (6 harmonics) + ADSR envelope in a daemon thread |
| **Drone** | Continuous Sa + Pa + octave Sa loop in a daemon thread |

---

## 📦 Dependencies

| Package | Version | Purpose |
|---------|---------|---------|
| `numpy` | ≥ 2.3.5 | Array math, FFT, pitch detection |
| `PyAudio` | ≥ 0.2.14 | Microphone input, audio output |
| `scipy` | ≥ 1.16.3 | Signal processing utilities |

`tkinter` is part of the Python standard library (no install needed).

---

## 🎵 Sargam Reference

| Sargam | Semitones from Sa | Western equivalent |
|--------|------------------|--------------------|
| Sa     | 0  | Tonic (1st) |
| Re♭    | 1  | Komal Re —> minor 2nd |
| Re     | 2  | Shuddh Re —> major 2nd |
| Ga♭    | 3  | Komal Ga —> minor 3rd |
| Ga     | 4  | Shuddh Ga —> major 3rd |
| Ma     | 5  | Shuddh Ma —> perfect 4th |
| Ma#    | 6  | Tivra Ma —> augmented 4th |
| Pa     | 7  | Pa —> perfect 5th |
| Dha♭   | 8  | Komal Dha —> minor 6th |
| Dha    | 9  | Shuddh Dha —> major 6th |
| Ni♭    | 10 | Komal Ni —> minor 7th |
| Ni     | 11 | Shuddh Ni —> major 7th |
| Sa'    | 12 | Upper Sa —> octave |

---

## 🙏 Acknowledgements

- YIN pitch detection algorithm: de Cheveigné & Kawahara (2002), *JASA*
- Equal temperament tuning: A4 = 440 Hz standard
- Designed for Indian classical riyaaz practice, inspired by the guru–shishya tradition

---

## 📄 License

MIT License feel free to use, modify, and share.
