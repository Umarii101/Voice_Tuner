import tkinter as tk
from tkinter import ttk, messagebox
import numpy as np
import pyaudio
import threading
import queue
import time
from collections import deque, defaultdict
import sys
import random

# ─────────────────────────────────────────────────────────────────────────────
#  VOCAL RIYAAZ — Indian Classical Singing Practice Tool
#
#  Redesign philosophy:
#    Classical singing is learned as: HEAR → INTERNALIZE → SING → CORRECT
#    The previous app only did SING → CORRECT, which is backwards.
#    This app implements the full cycle, modelled on how a guru teaches.
#
#  Architecture fixes from v2:
#    • Auto-Sa removed entirely — replaced with "Sa Finder" (hear & choose)
#    • play_note_tone() now takes a NOTE NAME and looks up freq live from sa_base
#      → this fixes the "buttons don't update with Sa" bug at the root level
#    • _refresh_sargam_buttons() is called whenever Sa changes anywhere
#    • All note frequencies are computed on-demand via get_note_freq(name)
#    • 4 dedicated pages: Sa Setup / Free Practice / Guided Riyaaz / Stats
# ─────────────────────────────────────────────────────────────────────────────


class VocalRiyaaz:

    # ── Raga definitions (subset of notes used) ───────────────────────────
    RAGAS = {
        'All 12 Notes':          None,
        'Bilawal  (S R G M P D N)':   ['Sa','Re','Ga','Ma','Pa','Dha','Ni'],
        'Yaman    (S R G M# P D N)':   ['Sa','Re','Ga','Ma#','Pa','Dha','Ni'],
        'Kafi     (S R g M P D n)':    ['Sa','Re','Ga♭','Ma','Pa','Dha','Ni♭'],
        'Bhairavi (S r g M P d n)':    ['Sa','Re♭','Ga♭','Ma','Pa','Dha♭','Ni♭'],
        'Bhairav  (S r G M P d N)':    ['Sa','Re♭','Ga','Ma','Pa','Dha♭','Ni'],
        'Todi     (S r g M# P d N)':   ['Sa','Re♭','Ga♭','Ma#','Pa','Dha♭','Ni'],
        'Kalyan   (S R G M# P D N)':   ['Sa','Re','Ga','Ma#','Pa','Dha','Ni'],
        'Marwa    (S r G M# D N)':     ['Sa','Re♭','Ga','Ma#','Dha','Ni'],
    }

    # ── Guided exercise sequences (list of note names in order) ───────────
    EXERCISES = {
        'Hold Sa':              ['Sa'],
        'Sa – Re – Sa':         ['Sa','Re','Sa'],
        'Sa – Ga – Sa':         ['Sa','Ga','Sa'],
        'Sa – Pa – Sa':         ['Sa','Pa','Sa'],
        'Aaroh (scale up)':     ['Sa','Re','Ga','Ma','Pa','Dha','Ni',"Sa'"],
        'Avaroh (scale down)':  ["Sa'",'Ni','Dha','Pa','Ma','Ga','Re','Sa'],
        'Full Saptaka':         ['Sa','Re','Ga','Ma','Pa','Dha','Ni',"Sa'",
                                 'Ni','Dha','Pa','Ma','Ga','Re','Sa'],
        'All Komal notes':      ['Re♭','Ga♭','Ma#','Dha♭','Ni♭'],
        'Random (8 notes)':     '__random__',
    }

    def __init__(self, root):
        self.root = root
        self.root.title("Vocal Riyaaz — Indian Classical Singing Practice")
        self.root.geometry("1300x900")
        self.root.configure(bg="#0d0d1a")

        # ── Audio constants ────────────────────────────────────────────────
        self.CHUNK   = 4096
        self.FORMAT  = pyaudio.paFloat32
        self.CHANNELS = 1
        self.RATE    = 44100
        self.running = False

        # ── Sargam note table ──────────────────────────────────────────────
        self.indian_notes = [
            {'name': 'Sa',   'semitones':  0},
            {'name': 'Re♭',  'semitones':  1},
            {'name': 'Re',   'semitones':  2},
            {'name': 'Ga♭',  'semitones':  3},
            {'name': 'Ga',   'semitones':  4},
            {'name': 'Ma',   'semitones':  5},
            {'name': 'Ma#',  'semitones':  6},
            {'name': 'Pa',   'semitones':  7},
            {'name': 'Dha♭', 'semitones':  8},
            {'name': 'Dha',  'semitones':  9},
            {'name': 'Ni♭',  'semitones': 10},
            {'name': 'Ni',   'semitones': 11},
            {'name': "Sa'",  'semitones': 12},
        ]
        self.MAIN_NOTES  = ['Sa','Re','Ga','Ma','Pa','Dha','Ni',"Sa'"]
        self.KOMAL_NOTES = ['Re♭','Ga♭','Ma#','Dha♭','Ni♭']

        self.sa_base        = 220.0     # default A3 — sensible midpoint

        # ── Detection ─────────────────────────────────────────────────────
        self.tolerance_cents  = 20
        self.freq_buffer      = deque(maxlen=7)
        self.freq_history     = deque(maxlen=150)
        self.match_history    = deque(maxlen=150)
        self.last_match_time  = {}
        self.note_hold_time   = 0.8

        # ── Session stats ──────────────────────────────────────────────────
        # per note: hits, misses, list of cents deviations
        self.note_stats = defaultdict(lambda: {'hits':0,'miss':0,'cents':[]})

        # ── Guided session state ───────────────────────────────────────────
        self.guided_active      = False
        self.guided_target      = None   # current note name being tested
        self.guided_listen      = False  # True during "you sing now" window
        self.guided_listen_start = 0.0
        self.guided_step        = 0
        self.guided_sequence    = []
        self.guided_results     = []
        self.guided_cents_buf   = []     # cents errors collected in listen window

        # ── Playback / instruments ─────────────────────────────────────────
        self.tone_playing  = False
        self.drone_playing = False
        self.metro_running = False

        # ── Tk variables ───────────────────────────────────────────────────
        self.sensitivity_var  = tk.DoubleVar(value=0.012)
        self.tolerance_var    = tk.DoubleVar(value=20)
        self.metro_bpm        = tk.IntVar(value=60)
        self.beats_var        = tk.IntVar(value=4)
        self.sa_finder_freq   = tk.DoubleVar(value=220.0)
        self.selected_raga    = tk.StringVar(value='All 12 Notes')
        self.selected_exercise= tk.StringVar(value='Aaroh (scale up)')
        self.note_duration_var= tk.DoubleVar(value=3.0)
        self.current_page     = tk.StringVar(value='sa_setup')

        # ── PyAudio ───────────────────────────────────────────────────────
        self.p           = pyaudio.PyAudio()
        self.stream      = None
        self.audio_queue = queue.Queue(maxsize=10)

        # ── Widget caches ──────────────────────────────────────────────────
        self.sargam_btns  = {}   # name → Button
        self.mode_btns    = {}   # page_id → Button

        self._init_colors()
        self._build_ui()

    # ═════════════════════════════════════════════════════════════════════
    #  COLOUR PALETTE
    # ═════════════════════════════════════════════════════════════════════

    def _init_colors(self):
        self.C = dict(
            bg       = '#0d0d1a',
            panel    = '#141428',
            card     = '#1a1a35',
            light    = '#0f3060',
            accent   = '#00d9ff',
            accent2  = '#cc44ff',
            success  = '#00ff88',
            warning  = '#ffaa00',
            danger   = '#ff4444',
            text     = '#ffffff',
            muted    = '#888888',
            komal    = '#1e0f40',
            gold     = '#ffd700',
        )

    # ═════════════════════════════════════════════════════════════════════
    #  FREQUENCY HELPERS  — all frequencies are live, never baked-in
    # ═════════════════════════════════════════════════════════════════════

    def get_note_freq(self, name):
        """
        Compute frequency from current sa_base on every call.
        This is the architectural fix: no cached frequencies anywhere.
        """
        note = next((n for n in self.indian_notes if n['name'] == name), None)
        if note is None:
            return 0.0
        return self.sa_base * (2.0 ** (note['semitones'] / 12.0))

    def _note_name_at_freq(self, freq):
        """Western note name + octave for display only."""
        names = ['C','C#','D','D#','E','F','F#','G','G#','A','A#','B']
        ref = 130.81   # C3
        if freq <= 0:
            return ""
        st  = 12 * np.log2(freq / ref)
        idx = int(round(st)) % 12
        oct_= 3 + int(round(st)) // 12
        return f"{names[idx]}{oct_}"

    def _refresh_sargam_buttons(self):
        """Update all button text to current Sa. Called whenever Sa changes."""
        for name, btn in self.sargam_btns.items():
            freq = self.get_note_freq(name)
            btn.config(text=f"{name}\n{freq:.1f} Hz")
        self.sa_display_lbl.config(text=f"{self.sa_base:.1f} Hz")

    def set_sa(self, freq):
        """Central Sa-change method. Refresh everything."""
        self.sa_base = float(freq)
        self._refresh_sargam_buttons()
        self.status_bar.config(text=f"✅  Sa set to {self.sa_base:.1f} Hz")

    # ═════════════════════════════════════════════════════════════════════
    #  TONE SYNTHESIS — harmonium-style
    # ═════════════════════════════════════════════════════════════════════

    def _harmonium_wave(self, frequency, duration=1.5, volume=0.55):
        """Six-harmonic additive synthesis + ADSR, mimics a reed organ."""
        n   = int(self.RATE * duration)
        t   = np.linspace(0, duration, n, endpoint=False)
        harmonics = [(1,1.0),(2,0.50),(3,0.25),(4,0.13),(5,0.07),(6,0.04)]
        wave = sum(a * np.sin(2*np.pi*frequency*h*t) for h,a in harmonics)
        wave /= np.max(np.abs(wave) + 1e-9)
        wave *= volume
        # ADSR
        atk = int(0.04*self.RATE); dec = int(0.10*self.RATE); rel = int(0.14*self.RATE)
        env = np.ones(n)
        env[:atk] = np.linspace(0, 1, atk)
        if atk+dec < n: env[atk:atk+dec] = np.linspace(1, 0.80, dec)
        if n > rel:     env[-rel:]        = np.linspace(0.80, 0, rel)
        return (wave * env).astype(np.float32)

    def play_note_tone(self, note_name_or_freq):
        """
        Play harmonium tone. Accepts NOTE NAME (string) or raw Hz (float/int).
        When given a name, frequency is looked up live from sa_base.
        This is what fixes the 'buttons don't update with Sa' bug.
        """
        if isinstance(note_name_or_freq, str):
            freq = self.get_note_freq(note_name_or_freq)
        else:
            freq = float(note_name_or_freq)
        if freq <= 0 or self.tone_playing:
            return
        self.tone_playing = True
        def _play():
            try:
                wave = self._harmonium_wave(freq)
                out  = self.p.open(format=pyaudio.paFloat32, channels=1,
                                   rate=self.RATE, output=True)
                out.write(wave.tobytes())
                out.stop_stream(); out.close()
            except Exception as e:
                print(f"Tone error: {e}")
            finally:
                self.tone_playing = False
        threading.Thread(target=_play, daemon=True).start()

    # ── Sa+Pa drone ────────────────────────────────────────────────────

    def toggle_drone(self):
        if self.drone_playing:
            self.drone_playing = False
            self.drone_btn.config(text="🎵  Sa Drone", bg=self.C['light'], fg=self.C['text'])
        else:
            self.drone_playing = True
            self.drone_btn.config(text="🔇  Stop Drone", bg=self.C['success'], fg='black')
            threading.Thread(target=self._drone_loop, daemon=True).start()

    def _drone_loop(self):
        CHUNK = 2048
        try:
            out = self.p.open(format=pyaudio.paFloat32, channels=1,
                              rate=self.RATE, output=True, frames_per_buffer=CHUNK)
            while self.drone_playing:
                sa = self.sa_base
                t  = np.linspace(0, CHUNK/self.RATE, CHUNK, endpoint=False)
                w  = (0.40*np.sin(2*np.pi*sa*t)       # Sa
                    + 0.20*np.sin(2*np.pi*sa*2*t)      # Sa upper octave
                    + 0.18*np.sin(2*np.pi*sa*1.5*t)    # Pa — perfect fifth
                    + 0.06*np.sin(2*np.pi*sa*4*t))     # 2-octave Sa
                w /= np.max(np.abs(w)+1e-9)
                out.write((w * 0.45).astype(np.float32).tobytes())
            out.stop_stream(); out.close()
        except Exception as e:
            print(f"Drone error: {e}")

    # ── Metronome ──────────────────────────────────────────────────────

    def _make_click(self, freq=900, dur=0.05, vol=0.75):
        t = np.linspace(0, dur, int(self.RATE*dur), endpoint=False)
        return (np.sin(2*np.pi*freq*t) * np.exp(-t*50) * vol).astype(np.float32)

    def toggle_metronome(self):
        if self.metro_running:
            self.metro_running = False
            self.metro_btn.config(text="▶  Metronome", bg=self.C['light'], fg=self.C['text'])
        else:
            self.metro_running = True
            self.metro_btn.config(text="⏸  Metronome", bg=self.C['warning'], fg='black')
            threading.Thread(target=self._metro_loop, daemon=True).start()

    def _metro_loop(self):
        hi = self._make_click(1100, vol=0.85)
        lo = self._make_click(800,  vol=0.60)
        beat = 0
        try:
            out = self.p.open(format=pyaudio.paFloat32, channels=1,
                              rate=self.RATE, output=True)
            while self.metro_running:
                bpm  = self.metro_bpm.get()
                tick = hi if beat == 0 else lo
                out.write(tick.tobytes())
                beat = (beat+1) % self.beats_var.get()
                sleep = 60.0/bpm - len(tick)/self.RATE
                if sleep > 0: time.sleep(sleep)
            out.stop_stream(); out.close()
        except Exception as e:
            print(f"Metro error: {e}")

    # ═════════════════════════════════════════════════════════════════════
    #  YIN PITCH DETECTION
    # ═════════════════════════════════════════════════════════════════════

    def detect_pitch_yin(self, audio_data):
        N       = len(audio_data)
        tau_max = min(N//2, int(self.RATE/50))    # lowest detectable ~50 Hz
        tau_min = max(1, int(self.RATE/1000))     # highest detectable ~1000 Hz

        # Difference function
        d = np.zeros(tau_max)
        for tau in range(1, tau_max):
            diff = audio_data[:N-tau] - audio_data[tau:N]
            d[tau] = np.dot(diff, diff)

        # Cumulative mean normalised difference
        dp = np.ones(tau_max)
        running = 0.0
        for tau in range(1, tau_max):
            running += d[tau]
            dp[tau] = d[tau]*tau/running if running > 0 else 1.0

        # Absolute threshold search
        tau_est = -1
        for tau in range(tau_min, tau_max):
            if dp[tau] < 0.15:
                while tau+1 < tau_max and dp[tau+1] < dp[tau]:
                    tau += 1
                tau_est = tau
                break

        if tau_est == -1:
            tau_est = tau_min + int(np.argmin(dp[tau_min:tau_max]))
            if dp[tau_est] > 0.5:
                return 0

        # Parabolic interpolation
        if 0 < tau_est < tau_max-1:
            s0, s1, s2 = dp[tau_est-1], dp[tau_est], dp[tau_est+1]
            denom = 2*(2*s1-s0-s2)
            tau_f = tau_est + (s2-s0)/(denom+1e-9)
        else:
            tau_f = float(tau_est)

        return self.RATE/tau_f if tau_f > 0 else 0

    def _smooth(self, freq):
        if freq > 0:
            self.freq_buffer.append(freq)
        return float(np.median(list(self.freq_buffer))) if len(self.freq_buffer) >= 3 else freq

    # ═════════════════════════════════════════════════════════════════════
    #  NOTE MATCHING
    # ═════════════════════════════════════════════════════════════════════

    def check_note_match(self, freq):
        """
        Returns (matched_display_name, cents_error) or (None, None).
        Raga filter applied. Checks current + adjacent octaves.
        """
        if not freq or freq <= 0:
            return None, None

        raga_name = self.selected_raga.get()
        active    = self.RAGAS.get(raga_name)   # None = all notes

        best_name, best_cents = None, float('inf')

        for mult in (0.5, 1.0, 2.0):
            for n in self.indian_notes:
                # Sa' already represents upper octave — skip double-counting
                if n['name'] == "Sa'" and mult != 1.0:
                    continue
                # Raga filter
                if active is not None:
                    base = n['name'].rstrip("'")
                    if base not in active and n['name'] != "Sa'":
                        continue
                target = self.get_note_freq(n['name']) * mult
                if not (60 <= target <= 1200):
                    continue
                cents = abs(1200 * np.log2(freq / target))
                if cents < best_cents:
                    best_cents = cents
                    base = n['name'].rstrip("'")
                    if mult == 0.5:
                        best_name = base + "₋"
                    elif mult == 2.0 and n['name'] != "Sa'":
                        best_name = base + "'"
                    else:
                        best_name = n['name']

        if best_cents <= self.tolerance_cents:
            return best_name, best_cents
        return None, None

    def _cents_from_nearest(self, freq):
        """Signed cents from the closest note (ignores tolerance — for meter only)."""
        best = None
        best_abs = float('inf')
        for n in self.indian_notes:
            for mult in (0.5, 1.0, 2.0):
                t = self.get_note_freq(n['name']) * mult
                if 60 <= t <= 1200:
                    c = 1200 * np.log2(freq / t)
                    if abs(c) < best_abs:
                        best_abs = abs(c)
                        best = c
        return best if best is not None else 0.0

    # ═════════════════════════════════════════════════════════════════════
    #  UI BUILD
    # ═════════════════════════════════════════════════════════════════════

    def _build_ui(self):
        C = self.C
        root = self.root

        # ── Top nav bar ────────────────────────────────────────────────
        nav = tk.Frame(root, bg='#08081a', pady=8)
        nav.pack(fill=tk.X)

        tk.Label(nav, text="🎤  VOCAL RIYAAZ",
                 font=("Arial",18,"bold"), fg=C['accent'], bg='#08081a').pack(side=tk.LEFT, padx=18)

        nav_btn_frame = tk.Frame(nav, bg='#08081a')
        nav_btn_frame.pack(side=tk.LEFT, padx=12)

        page_defs = [
            ('sa_setup', '1 ·  Find Your Sa'),
            ('free',     '2 ·  Free Practice'),
            ('guided',   '3 ·  Guided Riyaaz'),
            ('stats',    '4 ·  Session Stats'),
        ]
        for pid, label in page_defs:
            btn = tk.Button(nav_btn_frame, text=label,
                            command=lambda p=pid: self._switch_page(p),
                            font=("Arial",10,"bold"), relief=tk.FLAT,
                            cursor="hand2", padx=12, pady=5)
            btn.pack(side=tk.LEFT, padx=3)
            self.mode_btns[pid] = btn

        # ── Persistent toolbar (always visible) ────────────────────────
        toolbar = tk.Frame(root, bg=C['panel'], pady=5)
        toolbar.pack(fill=tk.X, padx=10, pady=(2,0))

        # Sa value
        sa_pill = tk.Frame(toolbar, bg=C['card'], relief=tk.RAISED, bd=1, padx=10, pady=3)
        sa_pill.pack(side=tk.LEFT, padx=8)
        tk.Label(sa_pill, text="Sa =", font=("Arial",10), fg=C['muted'], bg=C['card']).pack(side=tk.LEFT)
        self.sa_display_lbl = tk.Label(sa_pill, text=f"{self.sa_base:.1f} Hz",
                                       font=("Arial",14,"bold"), fg=C['gold'], bg=C['card'])
        self.sa_display_lbl.pack(side=tk.LEFT, padx=6)

        # Raga selector
        tk.Label(toolbar, text="Raga:", font=("Arial",9),
                 fg=C['muted'], bg=C['panel']).pack(side=tk.LEFT, padx=(14,3))
        ttk.Combobox(toolbar, textvariable=self.selected_raga,
                     values=list(self.RAGAS.keys()), width=22,
                     state='readonly', font=("Arial",9)).pack(side=tk.LEFT)

        # Drone
        self.drone_btn = tk.Button(toolbar, text="🎵  Sa Drone",
                                   command=self.toggle_drone,
                                   bg=C['light'], fg=C['text'],
                                   font=("Arial",9,"bold"), relief=tk.FLAT,
                                   cursor="hand2", padx=10, pady=4)
        self.drone_btn.pack(side=tk.LEFT, padx=10)

        # Metronome
        self.metro_btn = tk.Button(toolbar, text="▶  Metronome",
                                   command=self.toggle_metronome,
                                   bg=C['light'], fg=C['text'],
                                   font=("Arial",9,"bold"), relief=tk.FLAT,
                                   cursor="hand2", padx=10, pady=4)
        self.metro_btn.pack(side=tk.LEFT, padx=4)

        self._bpm_lbl = tk.Label(toolbar, text="60 BPM", font=("Arial",8),
                                  fg=C['muted'], bg=C['panel'])
        self._bpm_lbl.pack(side=tk.LEFT, padx=3)
        self.metro_bpm.trace_add('write',
            lambda *_: self._bpm_lbl.config(text=f"{self.metro_bpm.get()} BPM"))

        tk.Scale(toolbar, from_=40, to=200, resolution=1, orient=tk.HORIZONTAL,
                 variable=self.metro_bpm, bg=C['panel'], fg=C['text'],
                 highlightthickness=0, length=90, showvalue=False,
                 troughcolor='#0a2040').pack(side=tk.LEFT)

        beat_f = tk.Frame(toolbar, bg=C['panel'])
        beat_f.pack(side=tk.LEFT, padx=4)
        for b in [3,4,6,7,8]:
            tk.Radiobutton(beat_f, text=str(b), variable=self.beats_var, value=b,
                           bg=C['panel'], fg=C['text'], selectcolor=C['light'],
                           font=("Arial",8), activebackground=C['panel']).pack(side=tk.LEFT)

        # ── Page host frame ────────────────────────────────────────────
        self.page_host = tk.Frame(root, bg=C['bg'])
        self.page_host.pack(fill=tk.BOTH, expand=True, padx=10, pady=4)

        self._build_page_sa_setup()
        self._build_page_free()
        self._build_page_guided()
        self._build_page_stats()

        # ── Status bar ─────────────────────────────────────────────────
        self.status_bar = tk.Label(root, text="Start with Step 1 — Find Your Sa",
                                   font=("Arial",9), fg=C['text'],
                                   bg=C['light'], anchor=tk.W, padx=10, relief=tk.SUNKEN)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)

        self._switch_page('sa_setup')

    # ─── SA SETUP PAGE ────────────────────────────────────────────────────

    def _build_page_sa_setup(self):
        C  = self.C
        pg = tk.Frame(self.page_host, bg=C['bg'])
        self.page_sa_setup = pg

        tk.Label(pg, text="STEP 1  —  FIND YOUR SA",
                 font=("Arial",24,"bold"), fg=C['gold'], bg=C['bg']).pack(pady=(18,4))

        tk.Label(pg,
            text="In Indian classical music, Sa is your personal tonic — the note your voice "
                 "sits in comfortably.\n"
                 "Drag the slider below to hear different pitches. When a note feels like "
                 "'home', click  ✅ THIS IS MY SA.",
            font=("Arial",11), fg=C['muted'], bg=C['bg'],
            wraplength=740, justify=tk.CENTER).pack(pady=6)

        # ── Slider card ─────────────────────────────────────────────────
        card = tk.Frame(pg, bg=C['card'], relief=tk.RAISED, bd=2, padx=30, pady=20)
        card.pack(pady=14)

        # Live display of current slider value
        freq_disp = tk.Label(card, text="220.0 Hz  —  A3",
                             font=("Arial",22,"bold"), fg=C['accent'], bg=C['card'])
        freq_disp.pack(pady=(0,8))

        def _on_slider(val):
            freq = float(val)
            note = self._note_name_at_freq(freq)
            freq_disp.config(text=f"{freq:.1f} Hz  —  {note}")

        tk.Scale(card, from_=100, to=320, resolution=0.5,
                 orient=tk.HORIZONTAL, variable=self.sa_finder_freq,
                 bg=C['card'], fg=C['text'], highlightthickness=0,
                 length=620, showvalue=False, troughcolor='#0a2040',
                 command=_on_slider).pack(pady=4)

        # Preset buttons
        preset_row = tk.Frame(card, bg=C['card'])
        preset_row.pack(pady=6)
        tk.Label(preset_row, text="Quick presets:", font=("Arial",9),
                 fg=C['muted'], bg=C['card']).pack(side=tk.LEFT, padx=6)
        presets = [
            ("C3  130", 130.81), ("D3  147", 146.83), ("E3  165", 164.81),
            ("F3  175", 174.61), ("G3  196", 196.00),
            ("A3  220", 220.00), ("B3  247", 246.94), ("C4  262", 261.63),
        ]
        for name, hz in presets:
            tk.Button(preset_row, text=name, cursor="hand2",
                      command=lambda h=hz: (self.sa_finder_freq.set(h), _on_slider(h)),
                      bg=C['light'], fg=C['text'], font=("Arial",8),
                      relief=tk.FLAT, padx=5, pady=2).pack(side=tk.LEFT, padx=2)

        # Buttons row
        btn_row = tk.Frame(card, bg=C['card'])
        btn_row.pack(pady=10)

        tk.Button(btn_row, text="🔊  Preview",
                  command=lambda: self.play_note_tone(self.sa_finder_freq.get()),
                  bg=C['light'], fg=C['text'], font=("Arial",11,"bold"),
                  relief=tk.FLAT, cursor="hand2", padx=14, pady=8).pack(side=tk.LEFT, padx=10)

        confirm_lbl = tk.Label(card, text="", font=("Arial",12,"bold"),
                                fg=C['success'], bg=C['card'])

        def _confirm_sa():
            self.set_sa(self.sa_finder_freq.get())
            confirm_lbl.config(text=f"✅  Sa locked at {self.sa_base:.1f} Hz — ready to practice!")
            self.root.after(4000, lambda: confirm_lbl.config(text=""))

        tk.Button(btn_row, text="✅  THIS IS MY SA",
                  command=_confirm_sa,
                  bg=C['success'], fg='black', font=("Arial",14,"bold"),
                  relief=tk.FLAT, cursor="hand2", padx=18, pady=8).pack(side=tk.LEFT, padx=10)

        confirm_lbl.pack(pady=4)

        # ── Tips ─────────────────────────────────────────────────────────
        tips = tk.Frame(pg, bg=C['card'], relief=tk.RAISED, bd=1, padx=22, pady=12)
        tips.pack(pady=8, padx=60)
        tk.Label(tips, text="💡  Tips for finding your Sa",
                 font=("Arial",11,"bold"), fg=C['accent'], bg=C['card']).pack(anchor=tk.W)
        for tip in [
            "•  Male voices: Sa is usually C3 – G3  (130 – 196 Hz)",
            "•  Female voices: Sa is usually G3 – C4  (196 – 262 Hz)",
            "•  The right Sa feels comfortable — neither strained nor too low",
            "•  If you use a harmonium, match the key you normally call Sa",
            "•  You can change Sa at any time — all notes update automatically",
        ]:
            tk.Label(tips, text=tip, font=("Arial",10), fg=C['text'],
                     bg=C['card'], anchor=tk.W).pack(anchor=tk.W, pady=1)

        tk.Button(pg, text="→  Go to Free Practice",
                  command=lambda: self._switch_page('free'),
                  bg=C['accent'], fg='black', font=("Arial",12,"bold"),
                  relief=tk.FLAT, cursor="hand2", padx=16, pady=8).pack(pady=14)

    # ─── FREE PRACTICE PAGE ───────────────────────────────────────────────

    def _build_page_free(self):
        C  = self.C
        pg = tk.Frame(self.page_host, bg=C['bg'])
        self.page_free = pg

        # Split layout
        left  = tk.Frame(pg, bg=C['panel'], width=195)
        left.pack(side=tk.LEFT, fill=tk.Y, padx=(0,8))
        left.pack_propagate(False)

        right = tk.Frame(pg, bg=C['bg'])
        right.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # ── Left panel ───────────────────────────────────────────────────
        def _sect(text):
            tk.Label(left, text=text, font=("Arial",11,"bold"),
                     fg=C['accent'], bg=C['panel']).pack(pady=(14,4))
            tk.Frame(left, bg=C['accent'], height=1).pack(fill=tk.X, padx=12)

        _sect("RECORDING")
        self.start_btn = tk.Button(left, text="▶  START", command=self.start_analysis,
                                   bg=C['success'], fg='black', font=("Arial",12,"bold"),
                                   relief=tk.FLAT, cursor="hand2", width=15, height=2)
        self.start_btn.pack(pady=5, padx=12)

        self.stop_btn = tk.Button(left, text="⏸  STOP", command=self.stop_analysis,
                                  bg=C['warning'], fg='black', font=("Arial",12,"bold"),
                                  relief=tk.FLAT, cursor="hand2", width=15, height=2,
                                  state=tk.DISABLED)
        self.stop_btn.pack(pady=4, padx=12)

        _sect("DETECTION")

        tk.Label(left, text="Mic Sensitivity", font=("Arial",8),
                 fg=C['muted'], bg=C['panel']).pack()
        tk.Scale(left, from_=0.001, to=0.10, resolution=0.001, orient=tk.HORIZONTAL,
                 variable=self.sensitivity_var, bg=C['light'], fg=C['text'],
                 highlightthickness=0, length=170, troughcolor='#0a2040').pack(pady=3)

        tk.Label(left, text="Tolerance (cents)", font=("Arial",8),
                 fg=C['muted'], bg=C['panel']).pack(pady=(6,0))
        tk.Scale(left, from_=5, to=50, resolution=1, orient=tk.HORIZONTAL,
                 variable=self.tolerance_var, bg=C['light'], fg=C['text'],
                 highlightthickness=0, length=170, troughcolor='#0a2040',
                 command=lambda v: setattr(self,'tolerance_cents',float(v))).pack(pady=3)

        _sect("HOW TO USE")
        tk.Label(left,
            text="1. Click a note button\n   → hear it (harmonium)\n"
                 "2. Sing and match it\n3. Green = you hit it!\n"
                 "4. Turn on Sa Drone\n   for constant reference",
            font=("Arial",8), fg=C['text'], bg=C['panel'],
            justify=tk.LEFT).pack(padx=10, pady=6)

        # ── Right panel ──────────────────────────────────────────────────
        top_row = tk.Frame(right, bg=C['bg'])
        top_row.pack(fill=tk.X, pady=4)

        # Big note display
        note_card = tk.Frame(top_row, bg=C['card'], relief=tk.RAISED, bd=2)
        note_card.pack(side=tk.LEFT, padx=(0,8))
        tk.Label(note_card, text="SINGING", font=("Arial",9),
                 fg=C['muted'], bg=C['card']).pack(pady=(8,0), padx=20)
        self.free_note_lbl = tk.Label(note_card, text="--",
                                      font=("Arial",62,"bold"),
                                      fg=C['success'], bg=C['card'], width=5)
        self.free_note_lbl.pack(padx=20, pady=4)

        # Info cards column
        info_col = tk.Frame(top_row, bg=C['bg'])
        info_col.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        def _info_card(parent, label):
            f = tk.Frame(parent, bg=C['light'], relief=tk.RAISED, bd=1)
            f.pack(fill=tk.X, pady=2)
            tk.Label(f, text=label, font=("Arial",9), fg=C['muted'],
                     bg=C['light']).pack(side=tk.LEFT, padx=10, pady=6)
            v = tk.Label(f, text="--", font=("Arial",18,"bold"),
                         fg=C['text'], bg=C['light'])
            v.pack(side=tk.RIGHT, padx=10, pady=6)
            return v

        self.free_freq_lbl      = _info_card(info_col, "FREQUENCY")
        self.free_cents_lbl     = _info_card(info_col, "CENTS ±")
        self.free_stability_lbl = _info_card(info_col, "STABILITY")

        # Pitch meter
        tk.Label(right, text="◀  FLAT          PITCH METER          SHARP  ▶",
                 font=("Arial",8), fg=C['muted'], bg=C['bg']).pack(anchor=tk.W, padx=8)
        self.free_tuner = tk.Canvas(right, bg="#08080f", height=50, highlightthickness=0)
        self.free_tuner.pack(fill=tk.X, padx=8, pady=3)

        # Sargam keyboard
        kb = tk.Frame(right, bg=C['bg'])
        kb.pack(fill=tk.X, padx=4, pady=2)
        tk.Label(kb, text="SARGAM KEYBOARD  —  click any note to hear it  "
                          "(frequencies always reflect current Sa)",
                 font=("Arial",9,"bold"), fg=C['accent'], bg=C['bg']).pack(anchor=tk.W, pady=(4,2))

        row1 = tk.Frame(kb, bg=C['bg'])
        row1.pack(fill=tk.X, pady=2)
        row2 = tk.Frame(kb, bg=C['bg'])
        row2.pack(fill=tk.X, pady=2)

        for name in self.MAIN_NOTES:
            btn = tk.Button(row1, text=f"{name}\n-- Hz",
                            font=("Arial",9,"bold"), fg=C['text'], bg=C['light'],
                            width=9, height=2, relief=tk.RAISED, cursor="hand2",
                            command=lambda n=name: self.play_note_tone(n))
            btn.pack(side=tk.LEFT, padx=2)
            self.sargam_btns[name] = btn

        for name in self.KOMAL_NOTES:
            btn = tk.Button(row2, text=f"{name}\n-- Hz",
                            font=("Arial",9,"bold"), fg=C['text'], bg=C['komal'],
                            width=9, height=2, relief=tk.RAISED, cursor="hand2",
                            command=lambda n=name: self.play_note_tone(n))
            btn.pack(side=tk.LEFT, padx=2)
            self.sargam_btns[name] = btn

        # Frequency history graph
        gf = tk.Frame(right, bg=C['bg'], relief=tk.SUNKEN, bd=1)
        gf.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)
        tk.Label(gf, text="PITCH HISTORY  (dashed lines = sargam positions)",
                 font=("Arial",8), fg=C['muted'], bg=C['bg']).pack(pady=2)
        self.graph_canvas = tk.Canvas(gf, bg="#04040e", highlightthickness=0)
        self.graph_canvas.pack(fill=tk.BOTH, expand=True, padx=6, pady=4)

        self._refresh_sargam_buttons()

    # ─── GUIDED RIYAAZ PAGE ───────────────────────────────────────────────

    def _build_page_guided(self):
        C  = self.C
        pg = tk.Frame(self.page_host, bg=C['bg'])
        self.page_guided = pg

        left  = tk.Frame(pg, bg=C['panel'], width=210)
        left.pack(side=tk.LEFT, fill=tk.Y, padx=(0,8))
        left.pack_propagate(False)

        right = tk.Frame(pg, bg=C['bg'])
        right.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # ── Left: exercise config ─────────────────────────────────────
        tk.Label(left, text="EXERCISE", font=("Arial",12,"bold"),
                 fg=C['accent'], bg=C['panel']).pack(pady=(16,6))
        tk.Frame(left, bg=C['accent'], height=1).pack(fill=tk.X, padx=12)

        tk.Label(left, text="Sequence:", font=("Arial",9),
                 fg=C['muted'], bg=C['panel']).pack(pady=(10,2))
        ttk.Combobox(left, textvariable=self.selected_exercise,
                     values=list(self.EXERCISES.keys()), width=20,
                     state='readonly', font=("Arial",9)).pack(padx=12)

        tk.Label(left, text="Time per note (s):", font=("Arial",9),
                 fg=C['muted'], bg=C['panel']).pack(pady=(10,2))
        tk.Scale(left, from_=1.5, to=8.0, resolution=0.5, orient=tk.HORIZONTAL,
                 variable=self.note_duration_var, bg=C['light'], fg=C['text'],
                 highlightthickness=0, length=170, troughcolor='#0a2040').pack(padx=12)

        tk.Label(left, text="Mic Sensitivity:", font=("Arial",9),
                 fg=C['muted'], bg=C['panel']).pack(pady=(10,2))
        tk.Scale(left, from_=0.001, to=0.10, resolution=0.001, orient=tk.HORIZONTAL,
                 variable=self.sensitivity_var, bg=C['light'], fg=C['text'],
                 highlightthickness=0, length=170, troughcolor='#0a2040').pack(padx=12)

        tk.Frame(left, bg=C['accent'], height=1).pack(fill=tk.X, padx=12, pady=12)

        self.guided_start_btn = tk.Button(left, text="▶  Start Session",
                                          command=self.start_guided_session,
                                          bg=C['success'], fg='black',
                                          font=("Arial",12,"bold"),
                                          relief=tk.FLAT, cursor="hand2",
                                          width=16, height=2)
        self.guided_start_btn.pack(pady=5, padx=12)

        self.guided_stop_btn  = tk.Button(left, text="⏹  Stop Session",
                                          command=self.stop_guided_session,
                                          bg=C['warning'], fg='black',
                                          font=("Arial",11,"bold"),
                                          relief=tk.FLAT, cursor="hand2",
                                          width=16, state=tk.DISABLED)
        self.guided_stop_btn.pack(pady=4, padx=12)

        tk.Frame(left, bg=C['accent'], height=1).pack(fill=tk.X, padx=12, pady=10)
        tk.Label(left,
            text="HOW GUIDED WORKS:\n\n"
                 "1. App plays a note\n   on harmonium\n\n"
                 "2. 'Now Sing!' appears\n   — match the note\n\n"
                 "3. See your accuracy\n   after each note\n\n"
                 "4. Results saved to\n   Session Stats",
            font=("Arial",8), fg=C['text'], bg=C['panel'],
            justify=tk.LEFT).pack(padx=12, pady=4)

        # ── Right: live display ───────────────────────────────────────
        # Target note (very large)
        target_card = tk.Frame(right, bg=C['card'], relief=tk.RAISED, bd=2)
        target_card.pack(fill=tk.X, padx=4, pady=4)

        tr = tk.Frame(target_card, bg=C['card'])
        tr.pack(fill=tk.X, padx=20, pady=8)

        tl = tk.Frame(tr, bg=C['card'])
        tl.pack(side=tk.LEFT, padx=16)
        tk.Label(tl, text="TARGET", font=("Arial",9), fg=C['muted'], bg=C['card']).pack()
        self.guided_target_lbl = tk.Label(tl, text="--",
                                          font=("Arial",76,"bold"),
                                          fg=C['gold'], bg=C['card'])
        self.guided_target_lbl.pack()
        self.guided_target_hz  = tk.Label(tl, text="Press  ▶ Start Session",
                                          font=("Arial",11), fg=C['muted'], bg=C['card'])
        self.guided_target_hz.pack()

        rr = tk.Frame(tr, bg=C['card'])
        rr.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=20)

        self.guided_phase_lbl   = tk.Label(rr, text="",
                                           font=("Arial",18,"bold"),
                                           fg=C['accent'], bg=C['card'])
        self.guided_phase_lbl.pack(anchor=tk.W, pady=(4,0))

        self.guided_countdown   = tk.Label(rr, text="",
                                           font=("Arial",40,"bold"),
                                           fg=C['text'], bg=C['card'])
        self.guided_countdown.pack(anchor=tk.W)

        tk.Label(rr, text="You are singing:", font=("Arial",9),
                 fg=C['muted'], bg=C['card']).pack(anchor=tk.W, pady=(6,0))
        self.guided_singing_lbl = tk.Label(rr, text="--",
                                           font=("Arial",30,"bold"),
                                           fg=C['text'], bg=C['card'])
        self.guided_singing_lbl.pack(anchor=tk.W)

        self.guided_result_lbl  = tk.Label(rr, text="",
                                           font=("Arial",13,"bold"),
                                           fg=C['success'], bg=C['card'])
        self.guided_result_lbl.pack(anchor=tk.W, pady=4)

        # Progress
        prog = tk.Frame(right, bg=C['bg'])
        prog.pack(fill=tk.X, padx=8, pady=2)
        tk.Label(prog, text="Progress:", font=("Arial",9),
                 fg=C['muted'], bg=C['bg']).pack(side=tk.LEFT, padx=4)
        self.guided_progress = tk.Label(prog, text="0 / 0",
                                        font=("Arial",10,"bold"),
                                        fg=C['accent'], bg=C['bg'])
        self.guided_progress.pack(side=tk.LEFT)

        # Pitch meter
        self.guided_tuner = tk.Canvas(right, bg="#08080f", height=50, highlightthickness=0)
        self.guided_tuner.pack(fill=tk.X, padx=8, pady=3)

        # Results list
        res_frame = tk.Frame(right, bg=C['card'], relief=tk.RAISED, bd=1)
        res_frame.pack(fill=tk.BOTH, expand=True, padx=8, pady=4)
        tk.Label(res_frame, text="NOTE-BY-NOTE RESULTS",
                 font=("Arial",10,"bold"), fg=C['accent'], bg=C['card']).pack(pady=5)
        self.results_canvas = tk.Canvas(res_frame, bg=C['card'], highlightthickness=0)
        self.results_canvas.pack(fill=tk.BOTH, expand=True, padx=6, pady=4)

    # ─── STATS PAGE ───────────────────────────────────────────────────────

    def _build_page_stats(self):
        C  = self.C
        pg = tk.Frame(self.page_host, bg=C['bg'])
        self.page_stats = pg

        tk.Label(pg, text="SESSION STATISTICS",
                 font=("Arial",20,"bold"), fg=C['accent'], bg=C['bg']).pack(pady=(16,2))
        tk.Label(pg, text="Accumulated from Free Practice and Guided sessions",
                 font=("Arial",10), fg=C['muted'], bg=C['bg']).pack()

        tk.Button(pg, text="🔄  Clear Stats", command=self._clear_stats,
                  bg=C['danger'], fg='white', font=("Arial",10,"bold"),
                  relief=tk.FLAT, cursor="hand2", padx=10, pady=4).pack(pady=8)

        self.stats_canvas = tk.Canvas(pg, bg=C['card'], highlightthickness=0)
        self.stats_canvas.pack(fill=tk.BOTH, expand=True, padx=20, pady=8)
        self.stats_canvas.bind('<Configure>', lambda _e: self._draw_stats())

    # ─── PAGE SWITCHER ─────────────────────────────────────────────────────

    def _switch_page(self, pid):
        C = self.C
        pages = {
            'sa_setup': self.page_sa_setup,
            'free':     self.page_free,
            'guided':   self.page_guided,
            'stats':    self.page_stats,
        }
        for p in pages.values():
            p.pack_forget()
        pages[pid].pack(fill=tk.BOTH, expand=True)

        for name, btn in self.mode_btns.items():
            if name == pid:
                btn.config(bg=C['accent'], fg='black', font=("Arial",10,"bold"))
            else:
                btn.config(bg=C['light'], fg=C['text'], font=("Arial",10))

        self.current_page.set(pid)
        if pid == 'stats':
            self._draw_stats()

    # ═════════════════════════════════════════════════════════════════════
    #  AUDIO PIPELINE
    # ═════════════════════════════════════════════════════════════════════

    def start_analysis(self):
        try:
            self.stream = self.p.open(format=self.FORMAT, channels=self.CHANNELS,
                                      rate=self.RATE, input=True,
                                      frames_per_buffer=self.CHUNK)
            self.running = True
            self.start_btn.config(state=tk.DISABLED)
            self.stop_btn.config(state=tk.NORMAL)
            self.status_bar.config(text="Listening — sing!")
            threading.Thread(target=self._audio_capture, daemon=True).start()
            self._process_audio()
        except Exception as e:
            messagebox.showerror("Microphone Error", str(e))

    def stop_analysis(self):
        self.running = False
        self.guided_active = False
        self.guided_listen = False
        if self.stream:
            self.stream.stop_stream(); self.stream.close(); self.stream = None
        try:
            self.start_btn.config(state=tk.NORMAL)
            self.stop_btn.config(state=tk.DISABLED)
        except Exception:
            pass
        self.status_bar.config(text="Stopped")

    def _audio_capture(self):
        while self.running:
            try:
                raw  = self.stream.read(self.CHUNK, exception_on_overflow=False)
                data = np.frombuffer(raw, dtype=np.float32)
                # Drop oldest frame if queue is full (prevents lag buildup)
                if self.audio_queue.full():
                    try: self.audio_queue.get_nowait()
                    except queue.Empty: pass
                self.audio_queue.put(data)
            except Exception as e:
                print(f"Capture error: {e}")

    def _process_audio(self):
        if not self.running:
            return
        try:
            if not self.audio_queue.empty():
                data = self.audio_queue.get()
                rms  = float(np.sqrt(np.mean(data**2)))

                if rms > self.sensitivity_var.get():
                    raw  = self.detect_pitch_yin(data)
                    freq = self._smooth(raw)

                    if 60 < freq < 1200:
                        self.freq_history.append(freq)
                        matched, cents_err = self.check_note_match(freq)
                        meter_cents        = self._cents_from_nearest(freq)
                        now = time.time()

                        # ── Update stats on any match ─────────────────
                        if matched:
                            base = matched.rstrip("'₋")
                            self.note_stats[base]['hits'] += 1
                            if cents_err is not None:
                                self.note_stats[base]['cents'].append(cents_err)
                            self.last_match_time[base] = now

                        # ── Route to active page's display logic ──────
                        pg = self.current_page.get()
                        if pg == 'free':
                            self._free_update(freq, matched, meter_cents, now)
                        elif pg == 'guided' and self.guided_active and self.guided_listen:
                            self._guided_voice_update(freq, matched, meter_cents, cents_err)
                else:
                    # Silence — reset note display
                    if self.current_page.get() == 'free':
                        self.free_note_lbl.config(text="--", fg=self.C['muted'])

        except Exception as e:
            print(f"Process error: {e}")

        if self.running:
            self.root.after(50, self._process_audio)

    # ─── Free practice UI update ──────────────────────────────────────────

    def _free_update(self, freq, matched, meter_cents, now):
        C = self.C
        self.free_freq_lbl.config(text=f"{freq:.1f} Hz")

        if matched:
            self.free_note_lbl.config(text=matched, fg=C['success'])
            clr = (C['success']  if abs(meter_cents) < 5
                   else C['warning'] if abs(meter_cents) < 15
                   else C['danger'])
            self.free_cents_lbl.config(text=f"{meter_cents:+.0f}¢", fg=clr)
            self.match_history.append(True)
        else:
            self.free_note_lbl.config(text="--", fg=C['muted'])
            self.free_cents_lbl.config(text="--", fg=C['muted'])
            self.match_history.append(False)

        # Stability = inverse of short-term std dev
        recent = list(self.freq_history)[-10:]
        if len(recent) >= 4:
            std  = np.std(recent)
            stab = max(0, 100 - int(std * 5))
            sc   = C['success'] if stab > 80 else C['warning'] if stab > 50 else C['danger']
            self.free_stability_lbl.config(text=f"{stab}%", fg=sc)

        # Button highlights
        for name, btn in self.sargam_btns.items():
            stripped = name.rstrip("'")
            bg_def = C['light'] if name in self.MAIN_NOTES else C['komal']
            if now - self.last_match_time.get(stripped, 0.0) < self.note_hold_time:
                btn.config(bg=C['success'], fg='black')
            else:
                btn.config(bg=bg_def, fg=C['text'])

        self._draw_tuner(self.free_tuner, meter_cents)
        self._draw_graph()
        self.status_bar.config(
            text=f"Freq: {freq:.1f} Hz  |  Sa: {self.sa_base:.1f} Hz"
                 + (f"  |  ✓ {matched}" if matched else ""))

    # ═════════════════════════════════════════════════════════════════════
    #  GUIDED RIYAAZ ENGINE
    #  Implements the HEAR → SING → FEEDBACK pedagogical loop
    # ═════════════════════════════════════════════════════════════════════

    def _build_exercise_sequence(self):
        ex_name = self.selected_exercise.get()
        ex      = self.EXERCISES.get(ex_name, ['Sa'])
        if ex == '__random__':
            raga   = self.selected_raga.get()
            pool   = self.RAGAS.get(raga) or [n['name'] for n in self.indian_notes
                                               if n['name'] != "Sa'"]
            return [random.choice(pool) for _ in range(8)]
        return list(ex)

    def start_guided_session(self):
        # Auto-start mic if not already running
        if not self.running:
            try:
                self.stream = self.p.open(format=self.FORMAT, channels=self.CHANNELS,
                                          rate=self.RATE, input=True,
                                          frames_per_buffer=self.CHUNK)
                self.running = True
                threading.Thread(target=self._audio_capture, daemon=True).start()
                self._process_audio()
            except Exception as e:
                messagebox.showerror("Mic Error", str(e))
                return

        self.guided_sequence = self._build_exercise_sequence()
        self.guided_step     = 0
        self.guided_results  = []
        self.guided_active   = True

        self.guided_start_btn.config(state=tk.DISABLED)
        self.guided_stop_btn.config(state=tk.NORMAL)

        self._guided_next_step()

    def _guided_next_step(self):
        """Advance to the next note in the exercise sequence."""
        if not self.guided_active:
            return
        if self.guided_step >= len(self.guided_sequence):
            self._guided_finish()
            return

        note_name   = self.guided_sequence[self.guided_step]
        target_freq = self.get_note_freq(note_name)
        total       = len(self.guided_sequence)

        self.guided_target        = note_name
        self.guided_cents_buf     = []
        self.guided_listen        = False

        self.guided_target_lbl.config(text=note_name, fg=self.C['gold'])
        self.guided_target_hz.config(text=f"{target_freq:.1f} Hz")
        self.guided_phase_lbl.config(text="🎵  LISTEN...", fg=self.C['accent'])
        self.guided_countdown.config(text="")
        self.guided_result_lbl.config(text="")
        self.guided_singing_lbl.config(text="--", fg=self.C['text'])
        self.guided_progress.config(text=f"{self.guided_step+1} / {total}")

        # PHASE 1: Play the reference note (harmonium)
        self.play_note_tone(note_name)

        # PHASE 2: After tone finishes (~1.7s), switch to sing phase
        self.root.after(1750, self._guided_start_sing)

    def _guided_start_sing(self):
        if not self.guided_active:
            return
        self.guided_listen       = True
        self.guided_listen_start = time.time()
        self.guided_phase_lbl.config(text="🎤  NOW SING!", fg=self.C['success'])
        self._guided_tick()

    def _guided_tick(self):
        """Countdown timer during sing phase."""
        if not self.guided_active or not self.guided_listen:
            return
        elapsed   = time.time() - self.guided_listen_start
        remaining = self.note_duration_var.get() - elapsed
        if remaining <= 0:
            self._guided_end_sing()
            return
        self.guided_countdown.config(text=f"{remaining:.1f}s")
        self.root.after(100, self._guided_tick)

    def _guided_end_sing(self):
        """Evaluate the sing phase and record result."""
        self.guided_listen = False
        self.guided_countdown.config(text="")

        buf = self.guided_cents_buf
        note_name = self.guided_target

        if buf:
            # "hits" = frames where cents error was within tolerance
            hit_frames = [c for c in buf if c <= self.tolerance_cents]
            hit_pct    = len(hit_frames) / len(buf) * 100
            avg_cents  = float(np.mean(buf))

            hit = hit_pct >= 55   # majority of frames were on-note

            if hit_pct >= 80:
                txt = f"✅  Excellent!  {hit_pct:.0f}% on note  |  avg {avg_cents:.0f}¢ off"
                col = self.C['success']
            elif hit_pct >= 55:
                txt = f"✅  Good!  {hit_pct:.0f}% on note  |  avg {avg_cents:.0f}¢ off"
                col = self.C['success']
            elif hit_pct >= 30:
                txt = f"🟡  Getting close  {hit_pct:.0f}% on note  |  avg {avg_cents:.0f}¢ off"
                col = self.C['warning']
            else:
                txt = f"❌  Missed  {hit_pct:.0f}% on note  |  avg {avg_cents:.0f}¢ off"
                col = self.C['danger']
        else:
            hit     = False
            hit_pct = 0
            avg_cents = 0
            txt = "⚠️  No voice detected — reduce sensitivity or sing louder"
            col = self.C['warning']

        self.guided_result_lbl.config(text=txt, fg=col)
        self.guided_results.append({
            'note': note_name, 'hit': hit,
            'hit_pct': hit_pct, 'avg_cents': avg_cents
        })

        # Persist to session stats
        base = note_name.rstrip("'")
        if hit:
            self.note_stats[base]['hits'] += 1
        else:
            self.note_stats[base]['miss'] += 1

        self.guided_phase_lbl.config(text="")
        self._draw_guided_results()

        self.guided_step += 1
        self.root.after(2200, self._guided_next_step)

    def _guided_voice_update(self, freq, matched, meter_cents, cents_err):
        """Called from audio loop during the 'sing' window."""
        C = self.C
        if matched:
            base_match  = matched.rstrip("'₋")
            base_target = (self.guided_target or "").rstrip("'")
            correct     = (base_match == base_target)

            if correct:
                self.guided_singing_lbl.config(text=matched, fg=C['success'])
                self.guided_target_lbl.config(fg=C['success'])
                if cents_err is not None:
                    self.guided_cents_buf.append(float(cents_err))
            else:
                self.guided_singing_lbl.config(text=matched, fg=C['danger'])
                self.guided_target_lbl.config(fg=C['gold'])
                # Penalise: wrong note counts as max miss
                self.guided_cents_buf.append(float(self.tolerance_cents + 20))
        else:
            self.guided_singing_lbl.config(text="--", fg=C['muted'])

        self._draw_tuner(self.guided_tuner, meter_cents)

    def _guided_finish(self):
        total = len(self.guided_results)
        hits  = sum(1 for r in self.guided_results if r['hit'])
        self.guided_active = False
        self.guided_phase_lbl.config(
            text=f"🎉  Done!  {hits}/{total} notes hit", fg=self.C['success'])
        self.guided_target_lbl.config(text="--", fg=self.C['gold'])
        self.guided_start_btn.config(state=tk.NORMAL)
        self.guided_stop_btn.config(state=tk.DISABLED)
        self.status_bar.config(
            text=f"Session complete: {hits}/{total} notes hit — see Stats for details")

    def stop_guided_session(self):
        self.guided_active = False
        self.guided_listen = False
        self.guided_phase_lbl.config(text="Session stopped", fg=self.C['warning'])
        self.guided_start_btn.config(state=tk.NORMAL)
        self.guided_stop_btn.config(state=tk.DISABLED)

    # ═════════════════════════════════════════════════════════════════════
    #  DRAWING
    # ═════════════════════════════════════════════════════════════════════

    def _draw_tuner(self, canvas, cents):
        """Horizontal pitch meter: ±50 cents, color-coded zones."""
        c = canvas; c.delete("all")
        w = c.winfo_width(); h = c.winfo_height()
        if w < 10: return
        C = self.C; mid = w // 2

        # Colour zones
        for x0, x1, col in [
            (0,    w*.22, "#2a0005"), (w*.22,w*.38, "#1a1400"),
            (w*.38,w*.62, "#001800"), (w*.62,w*.78, "#1a1400"),
            (w*.78,w,     "#2a0005"),
        ]:
            c.create_rectangle(x0, 0, x1, h, fill=col, outline="")

        c.create_line(mid, 0, mid, h, fill=C['success'], width=2)
        for lbl, off in [("-50",-.5),("-25",-.25),("0",0),("+25",.25),("+50",.5)]:
            x = mid + off*w
            c.create_text(x, 8,  text=lbl, fill="#666", font=("Arial",7))
            c.create_line(x, 14, x, 20,   fill="#444", width=1)

        if cents is not None:
            cl    = max(-50, min(50, cents))
            nx    = mid + (cl/50)*(w*.5)
            color = (C['success']  if abs(cents) < 5
                     else C['warning'] if abs(cents) < 15
                     else C['danger'])
            c.create_rectangle(nx-5, 20, nx+5, h-5, fill=color, outline="")
            c.create_text(nx, h-11, text=f"{cents:+.0f}¢",
                          fill=color, font=("Arial",8,"bold"))

    def _draw_graph(self):
        c = self.graph_canvas; c.delete("all")
        if len(self.freq_history) < 2: return
        w = c.winfo_width(); h = c.winfo_height()
        if w < 10 or h < 10: return
        C = self.C

        freqs = list(self.freq_history)
        lo = min(freqs)-20; hi = max(freqs)+20; span = hi-lo
        if span < 1: return

        def fy(f): return h - h*(f-lo)/span

        # Sargam gridlines (dashed) at current Sa
        for n in self.indian_notes:
            for mult in (0.5, 1.0, 2.0):
                t = self.get_note_freq(n['name']) * mult
                if lo <= t <= hi:
                    y   = fy(t)
                    isa = n['name'] in ('Sa',"Sa'")
                    c.create_line(0, y, w, y,
                                  fill="#332200" if isa else "#18283a",
                                  width=2 if isa else 1, dash=(4,4))
                    suf = "₋" if mult == 0.5 else ("'" if mult == 2.0 else "")
                    c.create_text(w-4, y-2,
                                  text=n['name'].rstrip("'") + suf,
                                  anchor=tk.NE, fill="#2a4a66", font=("Arial",7))

        # Grid
        for i in range(5):
            y = h*i/4
            c.create_line(0, y, w, y, fill="#101020", width=1)
            c.create_text(4, y+2, text=f"{hi - span*i/4:.0f}",
                          anchor=tk.NW, fill="#3a3a5a", font=("Arial",7))

        # Frequency line with glow
        pts = []
        for i, f in enumerate(freqs):
            pts.extend([w*i/(len(freqs)-1), fy(f)])

        if len(pts) >= 4:
            for thick in (8,5,3):
                a   = thick/8
                col = f"#{int(0*a):02x}{int(180*a):02x}{int(255*a):02x}"
                c.create_line(pts, fill=col, width=thick, smooth=True)
            c.create_line(pts, fill=C['accent'], width=2, smooth=True)

            for i, f in enumerate(freqs):
                x = w*i/(len(freqs)-1); y = fy(f)
                try:    hit = bool(self.match_history[i])
                except: hit = False
                c.create_oval(x-2, y-2, x+2, y+2,
                              fill=C['success'] if hit else "#003040", outline="")

    def _draw_guided_results(self):
        c = self.results_canvas; c.delete("all")
        C = self.C
        w = c.winfo_width()
        if w < 10: return

        y = 8
        for r in self.guided_results:
            hit = r['hit']; hp = r['hit_pct']; ac = r['avg_cents']
            col  = C['success'] if hit else (C['warning'] if hp >= 30 else C['danger'])
            icon = "✅" if hit else ("🟡" if hp >= 30 else "❌")
            c.create_text(12, y+12,
                          text=f"{icon}  {r['note']:6s}   {hp:3.0f}% on note   avg {ac:+.0f}¢",
                          anchor=tk.NW, fill=col, font=("Arial",10,"bold"))
            bar_x = 260; bar_max = max(1, w-280)
            bar_w = int(hp/100 * bar_max)
            c.create_rectangle(bar_x, y+6, bar_x+bar_max, y+22,
                                fill="#1a1a30", outline="")
            if bar_w > 0:
                c.create_rectangle(bar_x, y+6, bar_x+bar_w, y+22,
                                   fill=col, outline="")
            y += 30

    def _draw_stats(self):
        c = self.stats_canvas; c.delete("all")
        C = self.C
        w = c.winfo_width(); h = c.winfo_height()
        if w < 10 or h < 10: return

        # Collect notes that have any activity
        note_names = [n['name'] for n in self.indian_notes if n['name'] != "Sa'"]
        active = [(nm, self.note_stats[nm])
                  for nm in note_names
                  if self.note_stats[nm]['hits'] + self.note_stats[nm]['miss'] > 0]

        if not active:
            c.create_text(w//2, h//2,
                text="No data yet.\n\nPractice in Free or Guided mode to see your accuracy here.",
                fill=C['muted'], font=("Arial",14), justify=tk.CENTER, anchor=tk.CENTER)
            return

        # ── Bar chart: accuracy per note ──────────────────────────────
        chart_h = max(80, h//2 - 50)
        mL=60; mR=20; mT=40; mB=50
        chart_w = w - mL - mR

        c.create_text(w//2, 16, text="ACCURACY PER NOTE  (%  of attempts you hit the note)",
                      fill=C['accent'], font=("Arial",11,"bold"), anchor=tk.CENTER)

        # Y-axis labels + gridlines
        for pct in [0,25,50,75,100]:
            y = mT + chart_h - (chart_h*pct/100)
            c.create_line(mL, y, mL+chart_w, y, fill="#1a1a30", dash=(3,3))
            c.create_text(mL-6, y, text=str(pct), fill=C['muted'],
                          font=("Arial",8), anchor=tk.E)

        bar_w = chart_w // (len(active)+1)
        for i, (nm, st) in enumerate(active):
            hits  = st['hits']; miss = st['miss']
            total = hits + miss
            pct   = hits/total*100 if total else 0
            x0    = mL + i*bar_w + 4
            x1    = x0 + bar_w - 8
            y_top = mT + chart_h - (chart_h*pct/100)
            y_bot = mT + chart_h
            col   = C['success'] if pct>=75 else C['warning'] if pct>=40 else C['danger']
            c.create_rectangle(x0, y_top, x1, y_bot, fill=col, outline="")
            c.create_text((x0+x1)//2, y_top-10, text=f"{pct:.0f}%",
                          fill=col, font=("Arial",7,"bold"))
            c.create_text((x0+x1)//2, y_bot+14, text=nm,
                          fill=C['text'], font=("Arial",8,"bold"))
            c.create_text((x0+x1)//2, y_bot+26, text=f"{total} tries",
                          fill=C['muted'], font=("Arial",7))

        # ── Avg cents deviation table ─────────────────────────────────
        ty = mT + chart_h + 55
        c.create_text(w//2, ty, text="AVERAGE CENTS OFF-PITCH PER NOTE  (0 = perfect)",
                      fill=C['accent'], font=("Arial",10,"bold"), anchor=tk.CENTER)
        ty += 22
        cw = max(60, chart_w // max(1,len(active)))
        for i, (nm, st) in enumerate(active):
            cl  = st.get('cents',[])
            avg = np.mean(cl) if cl else 0.0
            col = C['success'] if abs(avg)<5 else C['warning'] if abs(avg)<15 else C['danger']
            x   = mL + i*cw + cw//2
            c.create_text(x, ty,    text=nm,          fill=C['text'],  font=("Arial",8,"bold"))
            c.create_text(x, ty+16, text=f"{avg:+.1f}¢", fill=col, font=("Arial",9))

    def _clear_stats(self):
        if messagebox.askyesno("Clear Stats", "Clear all session statistics?"):
            self.note_stats.clear()
            self._draw_stats()

    # ═════════════════════════════════════════════════════════════════════
    #  CLEANUP
    # ═════════════════════════════════════════════════════════════════════

    def on_closing(self):
        self.running       = False
        self.metro_running = False
        self.drone_playing = False
        self.guided_active = False
        time.sleep(0.15)
        if self.stream:
            try: self.stream.stop_stream(); self.stream.close()
            except: pass
        try: self.p.terminate()
        except: pass
        self.root.destroy()


# ──────────────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    root = tk.Tk()
    app  = VocalRiyaaz(root)
    root.protocol("WM_DELETE_WINDOW", app.on_closing)
    try:
        root.mainloop()
    except KeyboardInterrupt:
        try: app.on_closing()
        except: pass
        sys.exit(0)
