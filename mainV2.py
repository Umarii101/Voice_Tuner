import tkinter as tk
from tkinter import ttk, messagebox
import numpy as np
import pyaudio
import threading
import queue
import time
from collections import deque
import sys

# ─────────────────────────────────────────────────────────────────────────────
#  VOCAL PITCH ANALYZER PRO
#  Improvements over v1:
#    • YIN pitch detection algorithm (much more accurate for vocals)
#    • Median frequency smoothing (no more jitter)
#    • Harmonium-style tone synthesis for every sargam note (click to hear)
#    • Sa + Pa drone (continuous tanpura/shruti-box style background tone)
#    • Metronome with BPM slider, beat accent, selectable time signature
#    • Visual pitch meter needle (cents sharp/flat, color-coded)
#    • Sargam note gridlines on frequency graph
#    • All 12 notes shown (main + komal/tivra), all clickable
#    • Audio queue size limit to prevent lag build-up
#    • Octave apostrophe bug fixed
# ─────────────────────────────────────────────────────────────────────────────


class VocalPitchAnalyzer:
    def __init__(self, root):
        self.root = root
        self.root.title("Vocal Pitch Analyzer Pro")
        self.root.geometry("1280x860")
        self.root.configure(bg="#1a1a2e")

        # ── Audio parameters ───────────────────────────────────────────────
        self.CHUNK = 4096
        self.FORMAT = pyaudio.paFloat32
        self.CHANNELS = 1
        self.RATE = 44100
        self.running = False

        # ── Note / scale definitions ───────────────────────────────────────
        self.notes = ['C', 'C#', 'D', 'D#', 'E', 'F',
                      'F#', 'G', 'G#', 'A', 'A#', 'B']
        self.A4 = 440.0
        self.sa_base = 200.0          # default Sa (changed to sensible vocal range)

        # All 12 sargam notes + upper Sa
        self.indian_notes = [
            {'name': 'Sa',   'semitones': 0},
            {'name': 'Re♭',  'semitones': 1},
            {'name': 'Re',   'semitones': 2},
            {'name': 'Ga♭',  'semitones': 3},
            {'name': 'Ga',   'semitones': 4},
            {'name': 'Ma',   'semitones': 5},
            {'name': 'Ma#',  'semitones': 6},
            {'name': 'Pa',   'semitones': 7},
            {'name': 'Dha♭', 'semitones': 8},
            {'name': 'Dha',  'semitones': 9},
            {'name': 'Ni♭',  'semitones': 10},
            {'name': 'Ni',   'semitones': 11},
            {'name': "Sa'",  'semitones': 12},
        ]
        self.update_indian_note_frequencies()

        # ── Detection state ────────────────────────────────────────────────
        self.indian_note_tolerance = 15   # cents
        self.sargam_names = [n['name'] for n in self.indian_notes]
        self.last_match_time = {n: 0.0 for n in self.sargam_names}
        self.note_hold_time = 0.9         # seconds to keep note lit after match

        # ── Auto-Sa detection ──────────────────────────────────────────────
        self.auto_sa_enabled = tk.BooleanVar(value=True)
        self.sa_detection_samples = deque(maxlen=50)
        self.sa_locked = False

        # ── History buffers ────────────────────────────────────────────────
        self.freq_history = deque(maxlen=150)
        self.match_history = deque(maxlen=150)
        self.freq_buffer = deque(maxlen=7)   # for median smoothing
        self.audio_queue = queue.Queue(maxsize=10)

        # ── Playback state ─────────────────────────────────────────────────
        self.tone_playing = False
        self.drone_playing = False
        self.metro_running = False
        self.metro_bpm = tk.IntVar(value=60)
        self.beats_var = tk.IntVar(value=4)

        # ── PyAudio ───────────────────────────────────────────────────────
        self.p = pyaudio.PyAudio()
        self.stream = None

        self.setup_ui()

    # ═══════════════════════════════════════════════════════════════════════
    #  FREQUENCY / NOTE HELPERS
    # ═══════════════════════════════════════════════════════════════════════

    def update_indian_note_frequencies(self):
        """Recalculate all note frequencies from current Sa base."""
        for note in self.indian_notes:
            note['freq'] = self.sa_base * (2 ** (note['semitones'] / 12))

    def update_sargam_display(self):
        """Refresh note button labels after Sa changes."""
        for note_name, btn in self.sargam_btns.items():
            note_info = next((n for n in self.indian_notes if n['name'] == note_name), None)
            if note_info:
                btn.config(text=f"{note_info['name']}\n{note_info['freq']:.1f}Hz")
                btn.note_freq = note_info['freq']   # update stored freq

    # ═══════════════════════════════════════════════════════════════════════
    #  YIN PITCH DETECTION
    # ═══════════════════════════════════════════════════════════════════════

    def detect_pitch_yin(self, audio_data):
        """
        YIN algorithm — far superior to autocorrelation for singing.
        Returns fundamental frequency in Hz, or 0 if not confident.
        """
        N = len(audio_data)
        tau_max = min(N // 2, int(self.RATE / 50))   # min detectable: ~50 Hz
        tau_min = max(1, int(self.RATE / 1000))       # max detectable: ~1000 Hz

        # Step 2: difference function  d[tau] = sum((x[j] - x[j+tau])^2)
        # Computed efficiently via autocorrelation
        d = np.zeros(tau_max)
        for tau in range(1, tau_max):
            diff = audio_data[:N - tau] - audio_data[tau:N]
            d[tau] = np.dot(diff, diff)

        # Step 3: cumulative mean normalised difference function
        d_prime = np.empty(tau_max)
        d_prime[0] = 1.0
        running = 0.0
        for tau in range(1, tau_max):
            running += d[tau]
            d_prime[tau] = d[tau] * tau / running if running > 0 else 1.0

        # Step 4: absolute threshold  (default 0.15 per paper)
        threshold = 0.15
        tau_est = -1
        for tau in range(tau_min, tau_max):
            if d_prime[tau] < threshold:
                # slide to local minimum
                while tau + 1 < tau_max and d_prime[tau + 1] < d_prime[tau]:
                    tau += 1
                tau_est = tau
                break

        if tau_est == -1:
            # Fallback: global minimum in range
            tau_est = tau_min + int(np.argmin(d_prime[tau_min:tau_max]))
            if d_prime[tau_est] > 0.5:
                return 0  # not confident enough

        # Step 5: parabolic interpolation for sub-sample accuracy
        if 0 < tau_est < tau_max - 1:
            s0 = d_prime[tau_est - 1]
            s1 = d_prime[tau_est]
            s2 = d_prime[tau_est + 1]
            denom = 2 * (2 * s1 - s0 - s2)
            tau_interp = tau_est + (s2 - s0) / (denom + 1e-9)
        else:
            tau_interp = float(tau_est)

        return self.RATE / tau_interp if tau_interp > 0 else 0

    def smooth_frequency(self, freq):
        """Median filter over last N frames to eliminate jitter."""
        if freq > 0:
            self.freq_buffer.append(freq)
        if len(self.freq_buffer) < 3:
            return freq
        return float(np.median(list(self.freq_buffer)))

    # ═══════════════════════════════════════════════════════════════════════
    #  HARMONIUM TONE SYNTHESIS
    # ═══════════════════════════════════════════════════════════════════════

    def _harmonium_wave(self, frequency, duration=1.5, volume=0.55):
        """
        Synthesise a harmonium-like tone.
        Uses 6 harmonics with decaying amplitudes + ADSR envelope.
        """
        n_samples = int(self.RATE * duration)
        t = np.linspace(0, duration, n_samples, endpoint=False)

        # Harmonic profile: (multiple, relative_amplitude)
        harmonics = [(1, 1.0), (2, 0.55), (3, 0.28),
                     (4, 0.16), (5, 0.09), (6, 0.05)]
        wave = sum(a * np.sin(2 * np.pi * frequency * h * t)
                   for h, a in harmonics)
        wave /= np.max(np.abs(wave) + 1e-9)
        wave *= volume

        # ADSR envelope
        attack  = int(0.04 * self.RATE)
        decay   = int(0.10 * self.RATE)
        release = int(0.12 * self.RATE)
        sustain_level = 0.80

        env = np.ones(n_samples)
        if attack:
            env[:attack] = np.linspace(0, 1, attack)
        if decay and attack + decay < n_samples:
            env[attack:attack + decay] = np.linspace(1, sustain_level, decay)
        if release and n_samples > release:
            env[-release:] = np.linspace(sustain_level, 0, release)

        return (wave * env).astype(np.float32)

    def play_note_tone(self, freq):
        """Non-blocking: play a harmonium reference tone for the given frequency."""
        if self.tone_playing:
            return
        self.tone_playing = True

        def _play():
            try:
                wave = self._harmonium_wave(freq, duration=1.5)
                out = self.p.open(format=pyaudio.paFloat32, channels=1,
                                  rate=self.RATE, output=True)
                out.write(wave.tobytes())
                out.stop_stream()
                out.close()
            except Exception as e:
                print(f"Tone error: {e}")
            finally:
                self.tone_playing = False

        threading.Thread(target=_play, daemon=True).start()

    # ── Sa + Pa Drone ──────────────────────────────────────────────────────

    def toggle_drone(self):
        """Start or stop the continuous Sa+Pa background drone."""
        if self.drone_playing:
            self.drone_playing = False
            self.drone_btn.config(text="🎵 Sa Drone", bg=self.bg_light, fg=self.text_color)
        else:
            self.drone_playing = True
            self.drone_btn.config(text="🔇 Stop Drone", bg=self.success, fg="black")
            threading.Thread(target=self._drone_loop, daemon=True).start()

    def _drone_loop(self):
        CHUNK = 2048
        try:
            out = self.p.open(format=pyaudio.paFloat32, channels=1,
                              rate=self.RATE, output=True, frames_per_buffer=CHUNK)
            while self.drone_playing:
                sa = self.sa_base
                t = np.linspace(0, CHUNK / self.RATE, CHUNK, endpoint=False)
                # Sa + upper-octave Sa + Pa (perfect fifth) + gentle 2nd harmonic
                wave  = 0.40 * np.sin(2 * np.pi * sa       * t)
                wave += 0.20 * np.sin(2 * np.pi * sa * 2   * t)   # Sa upper octave
                wave += 0.18 * np.sin(2 * np.pi * sa * 1.5 * t)   # Pa
                wave += 0.06 * np.sin(2 * np.pi * sa * 4   * t)   # 2-octave Sa
                wave /= np.max(np.abs(wave) + 1e-9)
                wave  = (wave * 0.45).astype(np.float32)
                out.write(wave.tobytes())
            out.stop_stream()
            out.close()
        except Exception as e:
            print(f"Drone error: {e}")

    # ═══════════════════════════════════════════════════════════════════════
    #  METRONOME
    # ═══════════════════════════════════════════════════════════════════════

    def _make_click(self, freq=900, duration=0.05, volume=0.75):
        t = np.linspace(0, duration, int(self.RATE * duration), endpoint=False)
        env = np.exp(-t * 50)
        return (np.sin(2 * np.pi * freq * t) * env * volume).astype(np.float32)

    def toggle_metronome(self):
        if self.metro_running:
            self.metro_running = False
            self.metro_btn.config(text="▶  Metronome", bg=self.bg_light, fg=self.text_color)
        else:
            self.metro_running = True
            self.metro_btn.config(text="⏸  Metronome", bg=self.warning, fg="black")
            threading.Thread(target=self._metronome_loop, daemon=True).start()

    def _metronome_loop(self):
        click_hi = self._make_click(freq=1100, volume=0.85)   # downbeat
        click_lo = self._make_click(freq=800,  volume=0.60)   # other beats
        beat = 0
        try:
            out = self.p.open(format=pyaudio.paFloat32, channels=1,
                              rate=self.RATE, output=True)
            while self.metro_running:
                bpm      = self.metro_bpm.get()
                interval = 60.0 / bpm
                beats    = self.beats_var.get()

                click = click_hi if beat == 0 else click_lo
                out.write(click.tobytes())

                beat = (beat + 1) % beats
                sleep_time = interval - len(click) / self.RATE
                if sleep_time > 0:
                    time.sleep(sleep_time)
            out.stop_stream()
            out.close()
        except Exception as e:
            print(f"Metronome error: {e}")

    # ═══════════════════════════════════════════════════════════════════════
    #  UI SETUP
    # ═══════════════════════════════════════════════════════════════════════

    def setup_ui(self):
        # Colour palette
        self.bg_dark   = "#1a1a2e"
        self.bg_medium = "#16213e"
        self.bg_light  = "#0f3460"
        self.accent    = "#00d9ff"
        self.accent2   = "#ff00ff"
        self.text_color = "#ffffff"
        self.success   = "#00ff88"
        self.warning   = "#ffaa00"
        self.komal_bg  = "#1a0f3c"

        # ── Title bar ────────────────────────────────────────────────────
        title_frame = tk.Frame(self.root, bg=self.bg_dark)
        title_frame.pack(fill=tk.X, padx=20, pady=(14, 4))
        tk.Label(title_frame, text="🎤  VOCAL PITCH ANALYZER PRO",
                 font=("Arial", 26, "bold"), fg=self.accent, bg=self.bg_dark).pack()
        tk.Label(title_frame,
                 text="Real-time Sargam Detection  |  YIN Pitch  |  Harmonium Reference  |  Metronome",
                 font=("Arial", 10), fg="#aaaaaa", bg=self.bg_dark).pack()

        # ── Main split ───────────────────────────────────────────────────
        main = tk.Frame(self.root, bg=self.bg_dark)
        main.pack(fill=tk.BOTH, expand=True, padx=14, pady=6)

        # ── LEFT PANEL ───────────────────────────────────────────────────
        left = tk.Frame(main, bg=self.bg_medium, relief=tk.RAISED, bd=2, width=210)
        left.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 10))
        left.pack_propagate(False)

        def section(parent, text):
            tk.Label(parent, text=text, font=("Arial", 11, "bold"),
                     fg=self.accent, bg=self.bg_medium).pack(pady=(14, 6))
            tk.Frame(parent, bg=self.accent, height=1).pack(fill=tk.X, padx=12, pady=(0, 8))

        def slider(parent, label, var, lo, hi, res, cmd=None):
            tk.Label(parent, text=label, font=("Arial", 9),
                     fg=self.text_color, bg=self.bg_medium).pack()
            kw = dict(from_=lo, to=hi, resolution=res, orient=tk.HORIZONTAL,
                      variable=var, bg=self.bg_light, fg=self.text_color,
                      highlightthickness=0, length=170, troughcolor="#0a2040")
            if cmd:
                kw['command'] = cmd
            tk.Scale(parent, **kw).pack(pady=(0, 6))

        # ── Controls ─────────────────────────────────────────────────────
        section(left, "RECORDING")
        self.start_btn = tk.Button(left, text="▶  START", command=self.start_analysis,
                                   bg=self.success, fg="black", font=("Arial", 11, "bold"),
                                   relief=tk.FLAT, cursor="hand2", width=16, height=2)
        self.start_btn.pack(pady=3, padx=14)

        self.stop_btn = tk.Button(left, text="⏸  STOP", command=self.stop_analysis,
                                  bg=self.warning, fg="black", font=("Arial", 11, "bold"),
                                  relief=tk.FLAT, cursor="hand2", width=16, height=2,
                                  state=tk.DISABLED)
        self.stop_btn.pack(pady=3, padx=14)

        tk.Checkbutton(left, text="🎯  Auto-Detect Sa", variable=self.auto_sa_enabled,
                       font=("Arial", 9, "bold"), fg=self.accent, bg=self.bg_medium,
                       selectcolor=self.bg_light,
                       activebackground=self.bg_medium).pack(pady=4, padx=14)

        self.lock_sa_btn = tk.Button(left, text="🔒  Lock Sa", command=self.toggle_sa_lock,
                                     bg=self.accent2, fg="black", font=("Arial", 10, "bold"),
                                     relief=tk.FLAT, cursor="hand2", width=16)
        self.lock_sa_btn.pack(pady=3, padx=14)

        # ── Detection settings ────────────────────────────────────────────
        section(left, "DETECTION")
        self.sensitivity_var = tk.DoubleVar(value=0.01)
        slider(left, "Mic Sensitivity", self.sensitivity_var, 0.001, 0.1, 0.001)

        self.tolerance_var = tk.DoubleVar(value=15)
        slider(left, "Tolerance (cents)", self.tolerance_var, 5, 50, 1,
               cmd=lambda v: setattr(self, 'indian_note_tolerance', float(v)))

        tk.Label(left, text="Manual Sa (Hz)", font=("Arial", 9),
                 fg=self.text_color, bg=self.bg_medium).pack(pady=(4, 0))
        self.sa_var = tk.DoubleVar(value=self.sa_base)
        tk.Entry(left, textvariable=self.sa_var, width=10, bg=self.bg_light,
                 fg=self.text_color, insertbackground="white",
                 font=("Arial", 10)).pack(pady=3)
        tk.Button(left, text="Apply & Lock Sa", command=self.apply_sa_base,
                  bg=self.accent2, fg="black", font=("Arial", 9, "bold"),
                  relief=tk.FLAT, cursor="hand2").pack(pady=3)

        # ── Metronome ─────────────────────────────────────────────────────
        section(left, "METRONOME")

        bpm_row = tk.Frame(left, bg=self.bg_medium)
        bpm_row.pack()
        tk.Label(bpm_row, text="BPM ", font=("Arial", 10), fg=self.text_color,
                 bg=self.bg_medium).pack(side=tk.LEFT)
        self.bpm_display = tk.Label(bpm_row, text="60", font=("Arial", 14, "bold"),
                                    fg=self.accent, bg=self.bg_medium, width=4)
        self.bpm_display.pack(side=tk.LEFT)

        def _bpm_update(v):
            self.bpm_display.config(text=str(int(float(v))))

        slider(left, "", self.metro_bpm, 40, 200, 1, cmd=_bpm_update)

        beats_row = tk.Frame(left, bg=self.bg_medium)
        beats_row.pack(pady=2)
        tk.Label(beats_row, text="Beats/bar:", font=("Arial", 9),
                 fg=self.text_color, bg=self.bg_medium).pack(side=tk.LEFT)
        for b in [3, 4, 6, 7, 8]:
            tk.Radiobutton(beats_row, text=str(b), variable=self.beats_var, value=b,
                           bg=self.bg_medium, fg=self.text_color,
                           selectcolor=self.bg_light, font=("Arial", 9),
                           activebackground=self.bg_medium).pack(side=tk.LEFT)

        self.metro_btn = tk.Button(left, text="▶  Metronome", command=self.toggle_metronome,
                                   bg=self.bg_light, fg=self.text_color,
                                   font=("Arial", 10, "bold"),
                                   relief=tk.FLAT, cursor="hand2", width=16)
        self.metro_btn.pack(pady=5, padx=14)

        # Quick-help note
        tk.Frame(left, bg=self.accent, height=1).pack(fill=tk.X, padx=12, pady=8)
        info = tk.Frame(left, bg=self.bg_light, relief=tk.SUNKEN, bd=1)
        info.pack(padx=14, fill=tk.X, pady=4)
        tk.Label(info, text="HOW TO USE", font=("Arial", 9, "bold"),
                 fg=self.accent, bg=self.bg_light).pack(pady=(5, 2))
        tk.Label(info,
                 text="1. Click a note button\n   to hear it (harmonium)\n"
                      "2. Sing and try to match\n3. Green = you matched!\n"
                      "4. Use Sa Drone for\n   constant reference",
                 font=("Arial", 8), fg=self.text_color,
                 bg=self.bg_light, justify=tk.LEFT).pack(padx=8, pady=(0, 8))

        # ── RIGHT PANEL ──────────────────────────────────────────────────
        right = tk.Frame(main, bg=self.bg_dark)
        right.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # Top row: detected note (large) + info cards
        top_row = tk.Frame(right, bg=self.bg_dark)
        top_row.pack(fill=tk.X, padx=4, pady=4)

        note_card = tk.Frame(top_row, bg=self.bg_medium, relief=tk.RAISED, bd=2)
        note_card.pack(side=tk.LEFT, padx=(0, 6))
        tk.Label(note_card, text="DETECTED SARGAM",
                 font=("Arial", 10), fg=self.accent, bg=self.bg_medium).pack(pady=(8, 0))
        self.note_label = tk.Label(note_card, text="--",
                                   font=("Arial", 64, "bold"),
                                   fg=self.success, bg=self.bg_medium, width=5)
        self.note_label.pack(padx=20, pady=6)

        info_col = tk.Frame(top_row, bg=self.bg_dark)
        info_col.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        def info_card(parent, label):
            f = tk.Frame(parent, bg=self.bg_light, relief=tk.RAISED, bd=2)
            f.pack(fill=tk.X, pady=(0, 4))
            tk.Label(f, text=label, font=("Arial", 9), fg=self.accent,
                     bg=self.bg_light).pack(side=tk.LEFT, padx=10, pady=8)
            val = tk.Label(f, text="--", font=("Arial", 20, "bold"),
                           fg=self.text_color, bg=self.bg_light)
            val.pack(side=tk.RIGHT, padx=10, pady=8)
            return val

        self.freq_label = info_card(info_col, "FREQUENCY (Hz)")
        self.sa_display = info_card(info_col, "CURRENT Sa")
        self.sa_display.config(text=f"{self.sa_base:.2f} Hz", fg=self.warning)
        self.cents_label = info_card(info_col, "CENTS FROM NOTE")

        # ── Pitch meter ──────────────────────────────────────────────────
        meter_frame = tk.Frame(right, bg=self.bg_dark)
        meter_frame.pack(fill=tk.X, padx=4, pady=2)
        tk.Label(meter_frame, text="PITCH METER  (cents flat ◀ 0 ▶ cents sharp)",
                 font=("Arial", 9), fg=self.accent, bg=self.bg_dark).pack(anchor=tk.W, padx=4)
        self.tuner_canvas = tk.Canvas(meter_frame, bg="#0a0a15", height=52, highlightthickness=0)
        self.tuner_canvas.pack(fill=tk.X, padx=6, pady=4)

        # ── Sargam keyboard ──────────────────────────────────────────────
        sargam_outer = tk.Frame(right, bg=self.bg_dark)
        sargam_outer.pack(fill=tk.X, padx=4, pady=2)

        header_row = tk.Frame(sargam_outer, bg=self.bg_dark)
        header_row.pack(fill=tk.X, padx=4, pady=(2, 4))
        tk.Label(header_row,
                 text="SARGAM KEYBOARD  — Click any note to hear it (harmonium tone)",
                 font=("Arial", 9, "bold"), fg=self.accent, bg=self.bg_dark).pack(side=tk.LEFT)

        self.drone_btn = tk.Button(header_row, text="🎵  Sa Drone",
                                   command=self.toggle_drone,
                                   bg=self.bg_light, fg=self.text_color,
                                   font=("Arial", 9, "bold"),
                                   relief=tk.FLAT, cursor="hand2", width=14)
        self.drone_btn.pack(side=tk.RIGHT, padx=4)

        self.sargam_btns = {}   # name → Button widget

        # Row 1: 7 main notes + upper Sa
        row1 = tk.Frame(sargam_outer, bg=self.bg_dark)
        row1.pack(fill=tk.X, padx=4, pady=2)
        main_note_names = ['Sa', 'Re', 'Ga', 'Ma', 'Pa', 'Dha', 'Ni', "Sa'"]

        # Row 2: 5 komal / tivra variants
        row2 = tk.Frame(sargam_outer, bg=self.bg_dark)
        row2.pack(fill=tk.X, padx=4, pady=2)
        komal_note_names = ['Re♭', 'Ga♭', 'Ma#', 'Dha♭', 'Ni♭']

        for name in main_note_names:
            info = next((n for n in self.indian_notes if n['name'] == name), None)
            if info:
                freq = info['freq']
                btn = tk.Button(row1,
                                text=f"{name}\n{freq:.1f} Hz",
                                font=("Arial", 9, "bold"),
                                fg=self.text_color, bg=self.bg_light,
                                width=9, height=2, relief=tk.RAISED, cursor="hand2",
                                command=lambda f=freq: self.play_note_tone(f))
                btn.pack(side=tk.LEFT, padx=2)
                btn.note_freq = freq
                self.sargam_btns[name] = btn

        for name in komal_note_names:
            info = next((n for n in self.indian_notes if n['name'] == name), None)
            if info:
                freq = info['freq']
                btn = tk.Button(row2,
                                text=f"{name}\n{freq:.1f} Hz",
                                font=("Arial", 9, "bold"),
                                fg=self.text_color, bg=self.komal_bg,
                                width=9, height=2, relief=tk.RAISED, cursor="hand2",
                                command=lambda f=freq: self.play_note_tone(f))
                btn.pack(side=tk.LEFT, padx=2)
                btn.note_freq = freq
                self.sargam_btns[name] = btn

        # ── Frequency graph ───────────────────────────────────────────────
        graph_frame = tk.Frame(right, bg=self.bg_dark, relief=tk.SUNKEN, bd=2)
        graph_frame.pack(fill=tk.BOTH, expand=True, padx=4, pady=6)
        tk.Label(graph_frame, text="FREQUENCY HISTORY  (dashed lines = sargam note positions)",
                 font=("Arial", 9), fg=self.accent, bg=self.bg_dark).pack(pady=3)
        self.canvas = tk.Canvas(graph_frame, bg="#0a0a15", highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True, padx=8, pady=6)

        # ── Status bar ────────────────────────────────────────────────────
        self.status_bar = tk.Label(
            self.root,
            text="Ready — click a sargam note to hear it, or press START",
            font=("Arial", 9), fg=self.text_color,
            bg=self.bg_light, anchor=tk.W, relief=tk.SUNKEN, padx=8)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)

    # ═══════════════════════════════════════════════════════════════════════
    #  AUTO-SA DETECTION
    # ═══════════════════════════════════════════════════════════════════════

    def auto_detect_sa(self, freq):
        if not self.auto_sa_enabled.get() or self.sa_locked:
            return
        self.sa_detection_samples.append(freq)
        if len(self.sa_detection_samples) < 20:
            return
        samples = list(self.sa_detection_samples)
        if np.std(samples[-10:]) < 3.0:
            median_freq = float(np.median(samples))
            c3 = 130.81
            nearest = round(12 * np.log2(median_freq / c3))
            detected = c3 * (2 ** (nearest / 12))
            if abs(detected - self.sa_base) > 10:
                self.sa_base = detected
                self.sa_var.set(round(detected, 2))
                self.update_indian_note_frequencies()
                self.update_sargam_display()
                self.sa_display.config(text=f"{self.sa_base:.2f} Hz")

    # ═══════════════════════════════════════════════════════════════════════
    #  NOTE MATCHING
    # ═══════════════════════════════════════════════════════════════════════

    def check_indian_notes(self, freq):
        """
        Return name of the closest sargam note within tolerance, else None.
        Checks current octave ± one octave.
        """
        if not freq or freq <= 0:
            return None

        closest_name, closest_cents = None, float('inf')

        for mult in (0.5, 1.0, 2.0):
            for n in self.indian_notes:
                # "Sa'" already represents upper octave — avoid double-counting
                if n['name'] == "Sa'" and mult != 1.0:
                    continue
                target = n['freq'] * mult
                if not (80 <= target <= 1000):
                    continue
                cents = abs(1200 * np.log2(freq / target))
                if cents < closest_cents:
                    closest_cents = cents
                    base = n['name'].rstrip("'")
                    if mult == 0.5:
                        closest_name = base + "₋"
                    elif mult == 2.0:
                        closest_name = base + "'"
                    else:
                        closest_name = n['name']

        return closest_name if closest_cents <= self.indian_note_tolerance else None

    # ═══════════════════════════════════════════════════════════════════════
    #  AUDIO PIPELINE
    # ═══════════════════════════════════════════════════════════════════════

    def audio_callback(self):
        while self.running:
            try:
                raw = self.stream.read(self.CHUNK, exception_on_overflow=False)
                data = np.frombuffer(raw, dtype=np.float32)
                # Drop oldest if queue full to prevent lag
                if self.audio_queue.full():
                    try:
                        self.audio_queue.get_nowait()
                    except queue.Empty:
                        pass
                self.audio_queue.put(data)
            except Exception as e:
                print(f"Audio input error: {e}")

    def process_audio(self):
        if not self.running:
            return

        try:
            if not self.audio_queue.empty():
                data = self.audio_queue.get()
                rms = float(np.sqrt(np.mean(data ** 2)))

                if rms > self.sensitivity_var.get():
                    raw_freq = self.detect_pitch_yin(data)
                    freq = self.smooth_frequency(raw_freq)

                    if 80 < freq < 1000:
                        self.auto_detect_sa(freq)
                        self.freq_history.append(freq)
                        self.freq_label.config(text=f"{freq:.2f} Hz")

                        matched = self.check_indian_notes(freq)
                        now = time.time()

                        if matched:
                            self.note_label.config(text=matched, fg=self.success)
                            base = matched.rstrip("'₋")
                            self.last_match_time[base] = now
                            self.match_history.append(True)

                            note_info = next(
                                (n for n in self.indian_notes if n['name'] == base), None)
                            if note_info:
                                target = note_info['freq']
                                # Adjust for octave shift
                                if matched.endswith("₋"):
                                    target /= 2
                                elif matched.endswith("'") and base != "Sa":
                                    target *= 2
                                cents = 1200 * np.log2(freq / target)
                                self.cents_label.config(text=f"{cents:+.0f}¢")
                                clr = (self.success if abs(cents) < 5
                                       else self.warning if abs(cents) < 15
                                       else "#ff4444")
                                self.cents_label.config(fg=clr)
                                self.draw_tuner(cents)
                            else:
                                self.draw_tuner(None)
                        else:
                            self.note_label.config(text="--", fg="#666666")
                            self.cents_label.config(text="--")
                            self.match_history.append(False)
                            self.draw_tuner(None)

                        # Update button highlights
                        for name, btn in self.sargam_btns.items():
                            stripped = name.rstrip("'")
                            recently = (now - self.last_match_time.get(stripped, 0.0)
                                        < self.note_hold_time)
                            base_bg = (self.bg_light
                                       if name in ('Sa', 'Re', 'Ga', 'Ma', 'Pa', 'Dha', 'Ni', "Sa'")
                                       else self.komal_bg)
                            if recently:
                                btn.config(bg=self.success, fg="black")
                            else:
                                btn.config(bg=base_bg, fg=self.text_color)

                        self.status_bar.config(
                            text=f"Freq: {freq:.2f} Hz  |  Sa: {self.sa_base:.2f} Hz"
                                 + (f"  |  ✓ {matched}" if matched else ""))

                        self.draw_graph()
                else:
                    self.note_label.config(text="--", fg="#444444")
                    self.draw_tuner(None)

        except Exception as e:
            print(f"Processing error: {e}")

        if self.running:
            self.root.after(50, self.process_audio)

    # ═══════════════════════════════════════════════════════════════════════
    #  DRAWING
    # ═══════════════════════════════════════════════════════════════════════

    def draw_tuner(self, cents):
        """Horizontal pitch meter: needle moves ±50 cents around centre."""
        c = self.tuner_canvas
        c.delete("all")
        w = c.winfo_width()
        h = c.winfo_height()
        if w < 10:
            return

        mid = w // 2

        # Background colour zones
        zones = [
            (0,      w * 0.22, "#2a0000"),   # far flat  — red
            (w*0.22, w * 0.38, "#1a1400"),   # near flat — yellow
            (w*0.38, w * 0.62, "#001500"),   # in tune   — green
            (w*0.62, w * 0.78, "#1a1400"),   # near sharp — yellow
            (w*0.78, w,        "#2a0000"),   # far sharp  — red
        ]
        for x0, x1, col in zones:
            c.create_rectangle(x0, 0, x1, h, fill=col, outline="")

        # Centre line + tick marks
        c.create_line(mid, 0, mid, h, fill=self.success, width=2)
        for label, offset in [("-50", -0.5), ("-25", -0.25), ("0", 0),
                               ("+25", 0.25), ("+50", 0.5)]:
            x = mid + offset * w
            c.create_text(x, 9, text=label, fill="#888888", font=("Arial", 7))
            c.create_line(x, 14, x, 22, fill="#555555", width=1)

        if cents is not None:
            clamped = max(-50, min(50, cents))
            nx = mid + (clamped / 50) * (w * 0.5)
            color = (self.success if abs(cents) < 5
                     else self.warning if abs(cents) < 15
                     else "#ff4444")
            # Needle bar
            c.create_rectangle(nx - 5, 22, nx + 5, h - 6, fill=color, outline="")
            # Cents label on needle
            c.create_text(nx, h - 14, text=f"{cents:+.0f}¢",
                          fill=color, font=("Arial", 8, "bold"))

    def draw_graph(self):
        c = self.canvas
        c.delete("all")
        if len(self.freq_history) < 2:
            return

        w = c.winfo_width()
        h = c.winfo_height()
        if w < 10 or h < 10:
            return

        freqs = list(self.freq_history)
        lo = min(freqs) - 20
        hi = max(freqs) + 20
        span = hi - lo
        if span < 1:
            return

        def fy(f):
            return h - h * (f - lo) / span

        # Sargam note gridlines (dashed) — show across octaves
        for n in self.indian_notes:
            for mult in (0.5, 1.0, 2.0):
                target = n['freq'] * mult
                if lo <= target <= hi:
                    y = fy(target)
                    c.create_line(0, y, w, y, fill="#1e2a3a", width=1, dash=(4, 4))
                    label = n['name'] + ("₋" if mult == 0.5 else ("'" if mult == 2.0 else ""))
                    c.create_text(w - 4, y - 2, text=label, anchor=tk.NE,
                                  fill="#336688", font=("Arial", 7))

        # Horizontal scale gridlines
        for i in range(5):
            y = h * i / 4
            c.create_line(0, y, w, y, fill="#151528", width=1)
            c.create_text(4, y + 2, text=f"{hi - span * i / 4:.0f}",
                          anchor=tk.NW, fill="#444444", font=("Arial", 7))

        # Frequency polyline with glow layers
        pts = []
        for i, f in enumerate(freqs):
            pts.extend([w * i / (len(freqs) - 1), fy(f)])

        if len(pts) >= 4:
            for thickness in (8, 5, 3):
                alpha = thickness / 8
                col = "#{:02x}{:02x}{:02x}".format(
                    int(0 * alpha), int(180 * alpha), int(255 * alpha))
                c.create_line(pts, fill=col, width=thickness, smooth=True)
            c.create_line(pts, fill=self.accent, width=2, smooth=True)

            # Dot per sample, coloured by match
            n_pts = len(freqs)
            for i, f in enumerate(freqs):
                x = w * i / (n_pts - 1)
                y = fy(f)
                try:
                    hit = bool(self.match_history[i])
                except IndexError:
                    hit = False
                fill = self.success if hit else "#003850"
                c.create_oval(x - 2, y - 2, x + 2, y + 2, fill=fill, outline="")

        # Horizontal midline (decorative)
        c.create_line(0, h / 2, w, h / 2, fill="#2a003a", width=1, dash=(6, 6))

    # ═══════════════════════════════════════════════════════════════════════
    #  SA LOCK / APPLY
    # ═══════════════════════════════════════════════════════════════════════

    def toggle_sa_lock(self):
        self.sa_locked = not self.sa_locked
        if self.sa_locked:
            self.lock_sa_btn.config(text="🔓  Unlock Sa", bg=self.success, fg="black")
            self.sa_display.config(fg=self.success)
            self.status_bar.config(
                text=f"Sa locked at {self.sa_base:.2f} Hz — sing other notes!")
        else:
            self.lock_sa_btn.config(text="🔒  Lock Sa", bg=self.accent2, fg="black")
            self.sa_display.config(fg=self.warning)
            self.status_bar.config(text="Sa unlocked — auto-detection active")

    def apply_sa_base(self):
        try:
            val = float(self.sa_var.get())
            if not (80 <= val <= 500):
                raise ValueError("Sa must be between 80 and 500 Hz")
            self.sa_base = val
            self.update_indian_note_frequencies()
            self.update_sargam_display()
            self.sa_display.config(text=f"{self.sa_base:.2f} Hz")
            if not self.sa_locked:
                self.toggle_sa_lock()
            else:
                self.status_bar.config(
                    text=f"Sa manually set to {self.sa_base:.2f} Hz")
        except Exception as e:
            messagebox.showerror("Invalid Sa",
                                 f"Enter a frequency between 80–500 Hz.\n{e}")

    # ═══════════════════════════════════════════════════════════════════════
    #  START / STOP
    # ═══════════════════════════════════════════════════════════════════════

    def start_analysis(self):
        try:
            self.stream = self.p.open(
                format=self.FORMAT, channels=self.CHANNELS,
                rate=self.RATE, input=True, frames_per_buffer=self.CHUNK)
            self.running = True
            self.start_btn.config(state=tk.DISABLED)
            self.stop_btn.config(state=tk.NORMAL)
            msg = ("Listening — sing and hold Sa to auto-detect!"
                   if self.auto_sa_enabled.get() and not self.sa_locked
                   else "Listening — start singing!")
            self.status_bar.config(text=msg)
            threading.Thread(target=self.audio_callback, daemon=True).start()
            self.process_audio()
        except Exception as e:
            messagebox.showerror("Microphone Error",
                                 f"Could not open audio input:\n{e}")

    def stop_analysis(self):
        self.running = False
        if self.stream:
            self.stream.stop_stream()
            self.stream.close()
            self.stream = None
        self.start_btn.config(state=tk.NORMAL)
        self.stop_btn.config(state=tk.DISABLED)
        self.status_bar.config(text="Stopped")

    def on_closing(self):
        self.running = False
        self.metro_running = False
        self.drone_playing = False
        time.sleep(0.15)   # give threads a moment to exit
        if self.stream:
            try:
                self.stream.stop_stream()
                self.stream.close()
            except Exception:
                pass
        try:
            self.p.terminate()
        except Exception:
            pass
        self.root.destroy()


# ─────────────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    root = tk.Tk()
    app = VocalPitchAnalyzer(root)
    root.protocol("WM_DELETE_WINDOW", app.on_closing)
    try:
        root.mainloop()
    except KeyboardInterrupt:
        try:
            app.on_closing()
        except Exception:
            pass
        sys.exit(0)
