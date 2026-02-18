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
#  VOCAL RIYAAZ v3  — "Ancient Raga × Modern Oscilloscope"
#
#  Design philosophy:
#    • Warm saffron/gold for musical elements (things you FEEL)
#    • Cold teal/cyan  for analytical elements (things you MEASURE)
#    • Deep space-black backgrounds
#    • One centrepiece visual per page — the Glow Circle
#    • Graph + pitch meter always visible in Guided Riyaaz
#
#  Bug fixes from v2:
#    • play_note_tone() accepts NOTE NAME → looks up freq live (no stale Hz)
#    • Auto-detect Sa removed entirely → replaced with Sa Finder (hear & choose)
#    • get_note_freq() is the single source of truth — never cache Hz values
# ─────────────────────────────────────────────────────────────────────────────


class VocalRiyaaz:

    # ── Scale & exercise data ──────────────────────────────────────────────
    RAGAS = {
        'All 12 Notes':                   None,
        'Bilawal   S R G M P D N':        ['Sa','Re','Ga','Ma','Pa','Dha','Ni'],
        'Yaman     S R G M# P D N':       ['Sa','Re','Ga','Ma#','Pa','Dha','Ni'],
        'Kafi      S R g M P D n':        ['Sa','Re','Ga♭','Ma','Pa','Dha','Ni♭'],
        'Bhairavi  S r g M P d n':        ['Sa','Re♭','Ga♭','Ma','Pa','Dha♭','Ni♭'],
        'Bhairav   S r G M P d N':        ['Sa','Re♭','Ga','Ma','Pa','Dha♭','Ni'],
        'Todi      S r g M# P d N':       ['Sa','Re♭','Ga♭','Ma#','Pa','Dha♭','Ni'],
        'Yaman Kalyan  S R G M# P D N':   ['Sa','Re','Ga','Ma#','Pa','Dha','Ni'],
        'Marwa     S r G M# D N':         ['Sa','Re♭','Ga','Ma#','Dha','Ni'],
    }
    EXERCISES = {
        'Hold Sa':              ['Sa'],
        'Sa – Re – Sa':         ['Sa','Re','Sa'],
        'Sa – Ga – Sa':         ['Sa','Ga','Sa'],
        'Sa – Pa – Sa':         ['Sa','Pa','Sa'],
        'Sa – Ni – Sa':         ['Sa','Ni','Sa'],
        'Aaroh (scale up)':     ['Sa','Re','Ga','Ma','Pa','Dha','Ni',"Sa'"],
        'Avaroh (scale down)':  ["Sa'",'Ni','Dha','Pa','Ma','Ga','Re','Sa'],
        'Full Saptaka (both)':  ['Sa','Re','Ga','Ma','Pa','Dha','Ni',"Sa'",
                                 'Ni','Dha','Pa','Ma','Ga','Re','Sa'],
        'All Komal notes':      ['Re♭','Ga♭','Ma#','Dha♭','Ni♭'],
        'Random (8 notes)':     '__random__',
    }

    def __init__(self, root):
        self.root = root
        self.root.title("Vocal Riyaaz")
        self.root.geometry("1360x920")
        self.root.configure(bg="#07070f")
        self.root.resizable(True, True)

        # ── Audio constants ────────────────────────────────────────────────
        self.CHUNK    = 4096
        self.FORMAT   = pyaudio.paFloat32
        self.CHANNELS = 1
        self.RATE     = 44100
        self.running  = False

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
        self.sa_base     = 220.0   # A3 default

        # ── Detection ─────────────────────────────────────────────────────
        self.tolerance_cents = 20
        self.freq_buffer     = deque(maxlen=7)
        self.freq_history    = deque(maxlen=150)
        self.match_history   = deque(maxlen=150)
        self.last_match_time = {}
        self.note_hold_time  = 0.8

        # ── Session stats ──────────────────────────────────────────────────
        self.note_stats = defaultdict(lambda: {'hits':0,'miss':0,'cents':[]})

        # ── Guided state ───────────────────────────────────────────────────
        self.guided_active       = False
        self.guided_target       = None
        self.guided_listen       = False
        self.guided_listen_start = 0.0
        self.guided_step         = 0
        self.guided_sequence     = []
        self.guided_results      = []
        self.guided_cents_buf    = []
        self.guided_glow_state   = 'idle'

        # ── Playback ───────────────────────────────────────────────────────
        self.tone_playing  = False
        self.drone_playing = False
        self.metro_running = False

        # ── Tk variables ───────────────────────────────────────────────────
        self.sensitivity_var   = tk.DoubleVar(value=0.012)
        self.tolerance_var     = tk.DoubleVar(value=20)
        self.metro_bpm         = tk.IntVar(value=60)
        self.beats_var         = tk.IntVar(value=4)
        self.sa_finder_freq    = tk.DoubleVar(value=220.0)
        self.selected_raga     = tk.StringVar(value='All 12 Notes')
        self.selected_exercise = tk.StringVar(value='Aaroh (scale up)')
        self.note_duration_var = tk.DoubleVar(value=3.0)
        self.current_page      = tk.StringVar(value='sa_setup')

        # ── PyAudio ───────────────────────────────────────────────────────
        self.p           = pyaudio.PyAudio()
        self.stream      = None
        self.audio_queue = queue.Queue(maxsize=10)

        # ── Widget registries ──────────────────────────────────────────────
        self.sargam_btns = {}
        self.nav_btns    = {}

        self._init_colors()
        self._build_ui()

    # ═══════════════════════════════════════════════════════════════════════
    #  COLOUR SYSTEM
    # ═══════════════════════════════════════════════════════════════════════

    def _init_colors(self):
        self.C = {
            # Backgrounds
            'bg':      '#07070f',
            'panel':   '#0c0c1a',
            'card':    '#0f0f22',
            'border':  '#1c1c38',
            'hover':   '#161630',
            # Musical (warm)
            'saffron': '#f5a623',
            'gold':    '#ffd54f',
            'amber':   '#ffb300',
            # Analytical (cool)
            'teal':    '#00b8d4',
            'cyan':    '#00e5ff',
            # Status
            'success': '#00c853',
            'warning': '#ffa000',
            'danger':  '#ff1744',
            # Text
            'text':    '#f0ebe3',
            'muted':   '#50507a',
            'label':   '#8888aa',
            # Special
            'komal':   '#1a0f3e',
            'sa_ring': '#f5a623',
        }

    # ═══════════════════════════════════════════════════════════════════════
    #  NOTE FREQUENCY — single source of truth
    # ═══════════════════════════════════════════════════════════════════════

    def get_note_freq(self, name):
        """Compute Hz from current sa_base on every call — never cached."""
        note = next((n for n in self.indian_notes if n['name'] == name), None)
        return self.sa_base * (2.0 ** (note['semitones'] / 12.0)) if note else 0.0

    def _western_name(self, freq):
        names = ['C','C#','D','D#','E','F','F#','G','G#','A','A#','B']
        if freq <= 0:
            return ''
        st  = 12 * np.log2(freq / 130.81)
        idx = int(round(st)) % 12
        oct_= 3 + int(round(st)) // 12
        return f"{names[idx]}{oct_}"

    def set_sa(self, freq):
        """Central point to change Sa. Refreshes everything."""
        self.sa_base = float(freq)
        self._refresh_sargam_buttons()
        try:
            self.sa_pill_lbl.config(text=f"{self.sa_base:.1f} Hz")
        except Exception:
            pass
        self.status_bar.config(text=f"✅  Sa set to {self.sa_base:.1f} Hz  ({self._western_name(self.sa_base)})")

    def _refresh_sargam_buttons(self):
        for name, btn in self.sargam_btns.items():
            freq = self.get_note_freq(name)
            btn.config(text=f"{name}\n{freq:.1f}")

    # ═══════════════════════════════════════════════════════════════════════
    #  HARMONIUM SYNTHESIS
    # ═══════════════════════════════════════════════════════════════════════

    def _harmonium_wave(self, frequency, duration=1.5, volume=0.55):
        n  = int(self.RATE * duration)
        t  = np.linspace(0, duration, n, endpoint=False)
        harmonics = [(1,1.0),(2,0.50),(3,0.25),(4,0.13),(5,0.07),(6,0.04)]
        wave = sum(a * np.sin(2*np.pi*frequency*h*t) for h,a in harmonics)
        wave /= np.max(np.abs(wave) + 1e-9)
        wave *= volume
        atk = int(0.04*self.RATE); dec = int(0.10*self.RATE); rel = int(0.14*self.RATE)
        env = np.ones(n)
        if atk:               env[:atk]        = np.linspace(0, 1, atk)
        if atk+dec < n:       env[atk:atk+dec] = np.linspace(1, 0.80, dec)
        if n > rel:           env[-rel:]        = np.linspace(0.80, 0, rel)
        return (wave * env).astype(np.float32)

    def play_note_tone(self, note_name_or_freq):
        """Accepts note NAME (looked up live) or raw Hz float."""
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
                out.write(wave.tobytes()); out.stop_stream(); out.close()
            except Exception as e:
                print(f"Tone err: {e}")
            finally:
                self.tone_playing = False
        threading.Thread(target=_play, daemon=True).start()

    # ── Drone ──────────────────────────────────────────────────────────────

    def toggle_drone(self):
        C = self.C
        if self.drone_playing:
            self.drone_playing = False
            self.drone_btn.config(text="🎵  Sa Drone", bg=C['border'], fg=C['text'])
        else:
            self.drone_playing = True
            self.drone_btn.config(text="🔇  Stop Drone", bg=C['success'], fg='black')
            threading.Thread(target=self._drone_loop, daemon=True).start()

    def _drone_loop(self):
        CHUNK = 2048
        try:
            out = self.p.open(format=pyaudio.paFloat32, channels=1,
                              rate=self.RATE, output=True, frames_per_buffer=CHUNK)
            while self.drone_playing:
                sa = self.sa_base
                t  = np.linspace(0, CHUNK/self.RATE, CHUNK, endpoint=False)
                w  = (0.40*np.sin(2*np.pi*sa*t)
                    + 0.20*np.sin(2*np.pi*sa*2*t)
                    + 0.18*np.sin(2*np.pi*sa*1.5*t)
                    + 0.06*np.sin(2*np.pi*sa*4*t))
                w /= np.max(np.abs(w)+1e-9)
                out.write((w*0.45).astype(np.float32).tobytes())
            out.stop_stream(); out.close()
        except Exception as e:
            print(f"Drone err: {e}")

    # ── Metronome ──────────────────────────────────────────────────────────

    def toggle_metronome(self):
        C = self.C
        if self.metro_running:
            self.metro_running = False
            self.metro_btn.config(text="▶  Metro", bg=C['border'], fg=C['text'])
        else:
            self.metro_running = True
            self.metro_btn.config(text="⏸  Metro", bg=C['amber'], fg='black')
            threading.Thread(target=self._metro_loop, daemon=True).start()

    def _metro_loop(self):
        def click(freq, dur=0.05, vol=0.75):
            t = np.linspace(0, dur, int(self.RATE*dur), endpoint=False)
            return (np.sin(2*np.pi*freq*t)*np.exp(-t*50)*vol).astype(np.float32)
        hi = click(1100, vol=0.85); lo = click(800, vol=0.60)
        beat = 0
        try:
            out = self.p.open(format=pyaudio.paFloat32, channels=1,
                              rate=self.RATE, output=True)
            while self.metro_running:
                out.write((hi if beat == 0 else lo).tobytes())
                beat = (beat+1) % self.beats_var.get()
                sleep = 60.0/self.metro_bpm.get() - 0.05
                if sleep > 0: time.sleep(sleep)
            out.stop_stream(); out.close()
        except Exception as e:
            print(f"Metro err: {e}")

    # ═══════════════════════════════════════════════════════════════════════
    #  YIN PITCH DETECTION
    # ═══════════════════════════════════════════════════════════════════════

    def detect_pitch_yin(self, audio_data):
        N       = len(audio_data)
        tau_max = min(N//2, int(self.RATE/50))
        tau_min = max(1,    int(self.RATE/1000))
        d  = np.zeros(tau_max)
        for tau in range(1, tau_max):
            diff = audio_data[:N-tau] - audio_data[tau:N]
            d[tau] = np.dot(diff, diff)
        dp = np.ones(tau_max); running = 0.0
        for tau in range(1, tau_max):
            running += d[tau]
            dp[tau]  = d[tau]*tau/running if running > 0 else 1.0
        tau_est = -1
        for tau in range(tau_min, tau_max):
            if dp[tau] < 0.15:
                while tau+1 < tau_max and dp[tau+1] < dp[tau]: tau += 1
                tau_est = tau; break
        if tau_est == -1:
            tau_est = tau_min + int(np.argmin(dp[tau_min:tau_max]))
            if dp[tau_est] > 0.5: return 0
        if 0 < tau_est < tau_max-1:
            s0,s1,s2 = dp[tau_est-1],dp[tau_est],dp[tau_est+1]
            tau_f = tau_est + (s2-s0)/(2*(2*s1-s0-s2)+1e-9)
        else:
            tau_f = float(tau_est)
        return self.RATE/tau_f if tau_f > 0 else 0

    def _smooth(self, freq):
        if freq > 0: self.freq_buffer.append(freq)
        return float(np.median(list(self.freq_buffer))) if len(self.freq_buffer) >= 3 else freq

    # ═══════════════════════════════════════════════════════════════════════
    #  NOTE MATCHING
    # ═══════════════════════════════════════════════════════════════════════

    def check_note_match(self, freq):
        if not freq or freq <= 0: return None, None
        raga   = self.selected_raga.get()
        active = self.RAGAS.get(raga)
        best_name, best_cents = None, float('inf')
        for mult in (0.5, 1.0, 2.0):
            for n in self.indian_notes:
                if n['name'] == "Sa'" and mult != 1.0: continue
                if active is not None:
                    base = n['name'].rstrip("'")
                    if base not in active and n['name'] != "Sa'": continue
                target = self.get_note_freq(n['name']) * mult
                if not (60 <= target <= 1200): continue
                cents = abs(1200 * np.log2(freq / target))
                if cents < best_cents:
                    best_cents = cents
                    base = n['name'].rstrip("'")
                    if mult == 0.5:   best_name = base + "₋"
                    elif mult == 2.0 and n['name'] != "Sa'": best_name = base + "'"
                    else:             best_name = n['name']
        return (best_name, best_cents) if best_cents <= self.tolerance_cents else (None, None)

    def _cents_from_nearest(self, freq):
        best = None; best_abs = float('inf')
        for n in self.indian_notes:
            for mult in (0.5, 1.0, 2.0):
                t = self.get_note_freq(n['name']) * mult
                if 60 <= t <= 1200:
                    c = 1200 * np.log2(freq / t)
                    if abs(c) < best_abs:
                        best_abs = abs(c); best = c
        return best if best is not None else 0.0

    # ═══════════════════════════════════════════════════════════════════════
    #  UI CONSTRUCTION
    # ═══════════════════════════════════════════════════════════════════════

    def _build_ui(self):
        C = self.C

        # ── Navigation bar ────────────────────────────────────────────────
        nav = tk.Frame(self.root, bg='#050510', height=52)
        nav.pack(fill=tk.X)
        nav.pack_propagate(False)

        logo = tk.Frame(nav, bg='#050510')
        logo.pack(side=tk.LEFT, padx=18, pady=8)
        tk.Label(logo, text="◉", font=("Georgia",18), fg=C['saffron'],
                 bg='#050510').pack(side=tk.LEFT, padx=(0,6))
        tk.Label(logo, text="VOCAL RIYAAZ", font=("Georgia",15,"bold"),
                 fg=C['text'], bg='#050510').pack(side=tk.LEFT)

        # Divider
        tk.Frame(nav, bg=C['border'], width=1).pack(side=tk.LEFT, fill=tk.Y,
                                                     pady=8, padx=12)

        tabs = [
            ('sa_setup', '①  Sa Setup'),
            ('free',     '②  Free Practice'),
            ('guided',   '③  Guided Riyaaz'),
            ('stats',    '④  Session Stats'),
        ]
        for pid, label in tabs:
            btn = tk.Button(nav, text=label, font=("Verdana",9,"bold"),
                            command=lambda p=pid: self._switch_page(p),
                            relief=tk.FLAT, cursor="hand2",
                            padx=14, pady=6, bd=0)
            btn.pack(side=tk.LEFT, padx=2, pady=8)
            self.nav_btns[pid] = btn

        # ── Persistent toolbar ────────────────────────────────────────────
        tb = tk.Frame(self.root, bg=C['panel'], height=46)
        tb.pack(fill=tk.X)
        tb.pack_propagate(False)

        # Sa pill
        sa_pill = tk.Frame(tb, bg=C['border'], padx=1, pady=1)
        sa_pill.pack(side=tk.LEFT, padx=12, pady=7)
        sa_inner = tk.Frame(sa_pill, bg=C['card'], padx=10, pady=4)
        sa_inner.pack()
        tk.Label(sa_inner, text="Sa", font=("Verdana",8), fg=C['muted'],
                 bg=C['card']).pack(side=tk.LEFT)
        self.sa_pill_lbl = tk.Label(sa_inner, text=f"{self.sa_base:.1f} Hz",
                                    font=("Courier New",13,"bold"),
                                    fg=C['saffron'], bg=C['card'])
        self.sa_pill_lbl.pack(side=tk.LEFT, padx=(6,0))

        # Raga
        tk.Label(tb, text="Raga:", font=("Verdana",8), fg=C['muted'],
                 bg=C['panel']).pack(side=tk.LEFT, padx=(14,4))
        raga_cb = ttk.Combobox(tb, textvariable=self.selected_raga,
                                values=list(self.RAGAS.keys()), width=20,
                                state='readonly', font=("Verdana",8))
        raga_cb.pack(side=tk.LEFT, pady=11)

        def _tb_btn(text, cmd, **kw):
            b = tk.Button(tb, text=text, command=cmd, font=("Verdana",8,"bold"),
                          relief=tk.FLAT, cursor="hand2", padx=10, pady=5, bd=0, **kw)
            b.pack(side=tk.LEFT, padx=6, pady=8)
            return b

        self.drone_btn = _tb_btn("🎵  Sa Drone", self.toggle_drone,
                                  bg=C['border'], fg=C['text'])
        self.metro_btn = _tb_btn("▶  Metro", self.toggle_metronome,
                                  bg=C['border'], fg=C['text'])

        self.metro_bpm.trace_add('write',
            lambda *_: self._bpm_lbl.config(text=f"{self.metro_bpm.get()} BPM"))
        self._bpm_lbl = tk.Label(tb, text="60 BPM", font=("Courier New",8),
                                  fg=C['muted'], bg=C['panel'])
        self._bpm_lbl.pack(side=tk.LEFT, padx=3)
        tk.Scale(tb, from_=40, to=200, resolution=1, orient=tk.HORIZONTAL,
                 variable=self.metro_bpm, bg=C['panel'], fg=C['text'],
                 highlightthickness=0, length=80, showvalue=False,
                 troughcolor='#1a1a35').pack(side=tk.LEFT)
        for b in [3,4,6,7,8]:
            tk.Radiobutton(tb, text=str(b), variable=self.beats_var, value=b,
                           bg=C['panel'], fg=C['label'],
                           selectcolor=C['card'], font=("Verdana",8),
                           activebackground=C['panel']).pack(side=tk.LEFT)

        # Thin gold separator under toolbar
        tk.Frame(self.root, bg=C['saffron'], height=1).pack(fill=tk.X)

        # ── Page host ─────────────────────────────────────────────────────
        self.page_host = tk.Frame(self.root, bg=C['bg'])
        self.page_host.pack(fill=tk.BOTH, expand=True)

        self._build_page_sa_setup()
        self._build_page_free()
        self._build_page_guided()
        self._build_page_stats()

        # ── Status bar ────────────────────────────────────────────────────
        self.status_bar = tk.Label(
            self.root, text="Welcome — start with Sa Setup to find your natural tonic",
            font=("Verdana",8), fg=C['label'], bg=C['panel'],
            anchor=tk.W, padx=12, relief=tk.FLAT, height=1)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        tk.Frame(self.root, bg=C['border'], height=1).pack(side=tk.BOTTOM, fill=tk.X)

        self._switch_page('sa_setup')

    # ═══════════════════════════════════════════════════════════════════════
    #  SA SETUP PAGE
    # ═══════════════════════════════════════════════════════════════════════

    def _build_page_sa_setup(self):
        C  = self.C
        pg = tk.Frame(self.page_host, bg=C['bg'])
        self.page_sa_setup = pg

        # Centred column layout
        col = tk.Frame(pg, bg=C['bg'])
        col.place(relx=0.5, rely=0.5, anchor=tk.CENTER)

        tk.Label(col, text="Find Your Sa", font=("Georgia",34,"bold"),
                 fg=C['saffron'], bg=C['bg']).pack(pady=(0,4))
        tk.Label(col,
            text="Sa is your personal tonic — the note your voice calls home.\n"
                 "Drag the slider to audition pitches. When one feels right, press Confirm.",
            font=("Verdana",10), fg=C['muted'], bg=C['bg'],
            justify=tk.CENTER).pack(pady=(0,24))

        # ── Slider card ─────────────────────────────────────────────────
        card_outer = tk.Frame(col, bg=C['border'], padx=1, pady=1)
        card_outer.pack(pady=8)
        card = tk.Frame(card_outer, bg=C['card'], padx=40, pady=28)
        card.pack()

        # Frequency + western name live display
        self._sa_setup_big = tk.Label(card, text="220.0 Hz",
                                      font=("Courier New",30,"bold"),
                                      fg=C['teal'], bg=C['card'])
        self._sa_setup_big.pack()
        self._sa_setup_note = tk.Label(card, text="A 3",
                                       font=("Georgia",16), fg=C['muted'], bg=C['card'])
        self._sa_setup_note.pack(pady=(0,14))

        def _slider_cb(val):
            f = float(val)
            self._sa_setup_big.config(text=f"{f:.1f} Hz")
            self._sa_setup_note.config(text=self._western_name(f))

        tk.Scale(card, from_=100, to=320, resolution=0.5,
                 orient=tk.HORIZONTAL, variable=self.sa_finder_freq,
                 bg=C['card'], fg=C['text'], highlightthickness=0,
                 length=580, showvalue=False, troughcolor=C['border'],
                 command=_slider_cb).pack()

        # Range labels
        lbl_row = tk.Frame(card, bg=C['card'])
        lbl_row.pack(fill=tk.X, pady=(2,14))
        tk.Label(lbl_row, text="100 Hz (Male low)", font=("Verdana",7),
                 fg=C['muted'], bg=C['card']).pack(side=tk.LEFT)
        tk.Label(lbl_row, text="320 Hz (Female high)", font=("Verdana",7),
                 fg=C['muted'], bg=C['card']).pack(side=tk.RIGHT)

        # Presets
        prow = tk.Frame(card, bg=C['card'])
        prow.pack(pady=(0,18))
        tk.Label(prow, text="Presets →", font=("Verdana",8),
                 fg=C['muted'], bg=C['card']).pack(side=tk.LEFT, padx=(0,8))
        for name, hz in [("C3 131",130.81),("D3 147",146.83),("E3 165",164.81),
                          ("F3 175",174.61),("G3 196",196.00),("A3 220",220.00),
                          ("B3 247",246.94),("C4 262",261.63)]:
            tk.Button(prow, text=name, cursor="hand2",
                      command=lambda h=hz: (self.sa_finder_freq.set(h), _slider_cb(h)),
                      bg=C['border'], fg=C['label'], font=("Verdana",8),
                      relief=tk.FLAT, padx=6, pady=3).pack(side=tk.LEFT, padx=2)

        # Buttons
        brow = tk.Frame(card, bg=C['card'])
        brow.pack()
        tk.Button(brow, text="🔊  Preview",
                  command=lambda: self.play_note_tone(self.sa_finder_freq.get()),
                  bg=C['border'], fg=C['text'], font=("Verdana",10,"bold"),
                  relief=tk.FLAT, cursor="hand2", padx=16, pady=9).pack(side=tk.LEFT, padx=8)

        confirm_fb = tk.Label(card, text="", font=("Verdana",10,"bold"),
                               fg=C['success'], bg=C['card'])

        def _confirm():
            self.set_sa(self.sa_finder_freq.get())
            confirm_fb.config(
                text=f"✅  Sa confirmed at {self.sa_base:.1f} Hz — head to Free Practice!")
            self.root.after(4000, lambda: confirm_fb.config(text=""))

        tk.Button(brow, text="✅  Confirm — This is My Sa",
                  command=_confirm,
                  bg=C['saffron'], fg='black', font=("Verdana",12,"bold"),
                  relief=tk.FLAT, cursor="hand2", padx=18, pady=9).pack(side=tk.LEFT, padx=8)
        confirm_fb.pack(pady=(12,0))

        # Tips
        tips_outer = tk.Frame(col, bg=C['border'], padx=1, pady=1)
        tips_outer.pack(pady=10, fill=tk.X)
        tips = tk.Frame(tips_outer, bg=C['panel'], padx=24, pady=14)
        tips.pack(fill=tk.X)
        tk.Label(tips, text="Tips for finding your Sa",
                 font=("Georgia",11,"bold"), fg=C['teal'], bg=C['panel']).pack(anchor=tk.W)
        for t in [
            "Male voices are usually comfortable between C3 – G3  (130 – 196 Hz)",
            "Female voices are usually comfortable between G3 – C4  (196 – 262 Hz)",
            "The right Sa feels settled — not strained, not too hollow",
            "If you use a harmonium, match the key you normally name as Sa",
        ]:
            tk.Label(tips, text=f"  ·  {t}", font=("Verdana",9), fg=C['muted'],
                     bg=C['panel'], anchor=tk.W).pack(anchor=tk.W, pady=1)

        tk.Button(col, text="→  Continue to Free Practice",
                  command=lambda: self._switch_page('free'),
                  bg=C['teal'], fg='black', font=("Verdana",11,"bold"),
                  relief=tk.FLAT, cursor="hand2", padx=18, pady=9).pack(pady=16)

    # ═══════════════════════════════════════════════════════════════════════
    #  FREE PRACTICE PAGE
    # ═══════════════════════════════════════════════════════════════════════

    def _build_page_free(self):
        C  = self.C
        pg = tk.Frame(self.page_host, bg=C['bg'])
        self.page_free = pg

        # ── Left sidebar ────────────────────────────────────────────────
        sidebar = tk.Frame(pg, bg=C['panel'], width=188)
        sidebar.pack(side=tk.LEFT, fill=tk.Y)
        sidebar.pack_propagate(False)
        tk.Frame(pg, bg=C['border'], width=1).pack(side=tk.LEFT, fill=tk.Y)

        def _sb_section(text):
            tk.Frame(sidebar, bg=C['border'], height=1).pack(fill=tk.X, padx=12, pady=(14,0))
            tk.Label(sidebar, text=text, font=("Verdana",8,"bold"),
                     fg=C['teal'], bg=C['panel']).pack(anchor=tk.W, padx=14, pady=(4,6))

        _sb_section("RECORDING")
        self.start_btn = tk.Button(sidebar, text="▶  START",
                                   command=self.start_analysis,
                                   bg=C['success'], fg='black',
                                   font=("Verdana",11,"bold"), relief=tk.FLAT,
                                   cursor="hand2", width=16, height=2)
        self.start_btn.pack(pady=3, padx=12)
        self.stop_btn  = tk.Button(sidebar, text="⏸  STOP",
                                   command=self.stop_analysis,
                                   bg=C['warning'], fg='black',
                                   font=("Verdana",11,"bold"), relief=tk.FLAT,
                                   cursor="hand2", width=16, height=2,
                                   state=tk.DISABLED)
        self.stop_btn.pack(pady=3, padx=12)

        _sb_section("SENSITIVITY")
        tk.Label(sidebar, text="Mic level", font=("Verdana",7), fg=C['muted'],
                 bg=C['panel']).pack(anchor=tk.W, padx=14)
        tk.Scale(sidebar, from_=0.001, to=0.10, resolution=0.001,
                 orient=tk.HORIZONTAL, variable=self.sensitivity_var,
                 bg=C['panel'], fg=C['text'], highlightthickness=0,
                 length=164, troughcolor=C['border'], showvalue=False).pack(padx=12)

        _sb_section("TOLERANCE")
        tk.Label(sidebar, text="Cents window", font=("Verdana",7), fg=C['muted'],
                 bg=C['panel']).pack(anchor=tk.W, padx=14)
        tk.Scale(sidebar, from_=5, to=50, resolution=1, orient=tk.HORIZONTAL,
                 variable=self.tolerance_var, bg=C['panel'], fg=C['text'],
                 highlightthickness=0, length=164, troughcolor=C['border'],
                 command=lambda v: setattr(self,'tolerance_cents',float(v))).pack(padx=12)

        _sb_section("HOW TO USE")
        tk.Label(sidebar,
            text="1. Click a note to hear it\n"
                 "2. Sing and match the pitch\n"
                 "3. Watch the graph + meter\n"
                 "4. Green = you nailed it",
            font=("Verdana",8), fg=C['muted'], bg=C['panel'],
            justify=tk.LEFT).pack(padx=14, pady=4)

        # ── Right main area ──────────────────────────────────────────────
        right = tk.Frame(pg, bg=C['bg'])
        right.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # Top row: glow circle + info cards
        top = tk.Frame(right, bg=C['bg'])
        top.pack(fill=tk.X, padx=14, pady=10)

        # Glow circle (what you're currently singing)
        glow_outer = tk.Frame(top, bg=C['border'], padx=1, pady=1)
        glow_outer.pack(side=tk.LEFT)
        self.free_glow = tk.Canvas(glow_outer, width=180, height=180,
                                   bg=C['card'], highlightthickness=0)
        self.free_glow.pack()
        self.free_glow.bind('<Configure>', lambda e: self._draw_glow(self.free_glow, '--', 'idle'))

        # Info column
        info = tk.Frame(top, bg=C['bg'])
        info.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=14)

        def _card(parent, label, initial="--", color_key='text'):
            outer = tk.Frame(parent, bg=C['border'], padx=1, pady=1)
            outer.pack(fill=tk.X, pady=3)
            inner = tk.Frame(outer, bg=C['card'], padx=14, pady=8)
            inner.pack(fill=tk.X)
            tk.Label(inner, text=label, font=("Verdana",8), fg=C['muted'],
                     bg=C['card']).pack(side=tk.LEFT)
            v = tk.Label(inner, text=initial, font=("Courier New",16,"bold"),
                         fg=C[color_key], bg=C['card'])
            v.pack(side=tk.RIGHT)
            return v

        self.free_freq_lbl  = _card(info, "FREQUENCY",  "--  Hz",      'teal')
        self.free_cents_lbl = _card(info, "CENTS  ±",   "--  ¢",       'text')
        self.free_stab_lbl  = _card(info, "STABILITY",  "--  %",       'text')
        self.free_raga_lbl  = _card(info, "RAGA MATCH", "--",           'saffron')

        # Pitch meter
        meter_lbl_row = tk.Frame(right, bg=C['bg'])
        meter_lbl_row.pack(fill=tk.X, padx=14, pady=(4,1))
        tk.Label(meter_lbl_row, text="◀  flat",
                 font=("Verdana",7), fg=C['muted'], bg=C['bg']).pack(side=tk.LEFT)
        tk.Label(meter_lbl_row, text="PITCH METER",
                 font=("Verdana",7,"bold"), fg=C['label'], bg=C['bg']).pack(side=tk.LEFT, expand=True)
        tk.Label(meter_lbl_row, text="sharp  ▶",
                 font=("Verdana",7), fg=C['muted'], bg=C['bg']).pack(side=tk.RIGHT)
        self.free_tuner = tk.Canvas(right, bg="#04040e", height=48,
                                    highlightthickness=0)
        self.free_tuner.pack(fill=tk.X, padx=14, pady=(0,6))

        # Sargam keyboard
        kb_head = tk.Frame(right, bg=C['bg'])
        kb_head.pack(fill=tk.X, padx=14, pady=(4,2))
        tk.Label(kb_head,
                 text="SARGAM KEYBOARD  —  click any note to hear it (harmonium tone)",
                 font=("Verdana",8,"bold"), fg=C['label'], bg=C['bg']).pack(side=tk.LEFT)

        row1 = tk.Frame(right, bg=C['bg'])
        row1.pack(fill=tk.X, padx=14, pady=2)
        row2 = tk.Frame(right, bg=C['bg'])
        row2.pack(fill=tk.X, padx=14, pady=2)

        for name in self.MAIN_NOTES:
            btn = tk.Button(row1, text=f"{name}\n--",
                            font=("Georgia",9,"bold"), fg=C['text'],
                            bg=C['border'], width=8, height=2,
                            relief=tk.FLAT, cursor="hand2",
                            command=lambda n=name: self.play_note_tone(n))
            btn.pack(side=tk.LEFT, padx=2)
            self.sargam_btns[name] = btn

        for name in self.KOMAL_NOTES:
            btn = tk.Button(row2, text=f"{name}\n--",
                            font=("Georgia",9,"bold"), fg=C['muted'],
                            bg=C['komal'], width=8, height=2,
                            relief=tk.FLAT, cursor="hand2",
                            command=lambda n=name: self.play_note_tone(n))
            btn.pack(side=tk.LEFT, padx=2)
            self.sargam_btns[name] = btn

        # Frequency history graph
        graph_card_outer = tk.Frame(right, bg=C['border'], padx=1, pady=1)
        graph_card_outer.pack(fill=tk.BOTH, expand=True, padx=14, pady=6)
        graph_card = tk.Frame(graph_card_outer, bg=C['card'])
        graph_card.pack(fill=tk.BOTH, expand=True)
        tk.Label(graph_card, text="PITCH HISTORY",
                 font=("Verdana",7,"bold"), fg=C['muted'], bg=C['card'],
                 anchor=tk.W).pack(anchor=tk.W, padx=10, pady=(5,0))
        self.free_graph = tk.Canvas(graph_card, bg="#03030c",
                                    highlightthickness=0)
        self.free_graph.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)

        self._refresh_sargam_buttons()

    # ═══════════════════════════════════════════════════════════════════════
    #  GUIDED RIYAAZ PAGE
    # ═══════════════════════════════════════════════════════════════════════

    def _build_page_guided(self):
        C  = self.C
        pg = tk.Frame(self.page_host, bg=C['bg'])
        self.page_guided = pg

        # ── Left sidebar ────────────────────────────────────────────────
        sidebar = tk.Frame(pg, bg=C['panel'], width=200)
        sidebar.pack(side=tk.LEFT, fill=tk.Y)
        sidebar.pack_propagate(False)
        tk.Frame(pg, bg=C['border'], width=1).pack(side=tk.LEFT, fill=tk.Y)

        def _sb_section(text):
            tk.Frame(sidebar, bg=C['border'], height=1).pack(fill=tk.X, padx=12, pady=(14,0))
            tk.Label(sidebar, text=text, font=("Verdana",8,"bold"),
                     fg=C['teal'], bg=C['panel']).pack(anchor=tk.W, padx=14, pady=(4,6))

        _sb_section("EXERCISE")
        tk.Label(sidebar, text="Sequence", font=("Verdana",7), fg=C['muted'],
                 bg=C['panel']).pack(anchor=tk.W, padx=14)
        ttk.Combobox(sidebar, textvariable=self.selected_exercise,
                     values=list(self.EXERCISES.keys()), width=21,
                     state='readonly', font=("Verdana",8)).pack(padx=12, pady=3)

        tk.Label(sidebar, text="Time per note (s)", font=("Verdana",7),
                 fg=C['muted'], bg=C['panel']).pack(anchor=tk.W, padx=14, pady=(8,0))
        tk.Scale(sidebar, from_=1.5, to=8.0, resolution=0.5,
                 orient=tk.HORIZONTAL, variable=self.note_duration_var,
                 bg=C['panel'], fg=C['text'], highlightthickness=0,
                 length=170, troughcolor=C['border']).pack(padx=12)

        tk.Label(sidebar, text="Mic sensitivity", font=("Verdana",7),
                 fg=C['muted'], bg=C['panel']).pack(anchor=tk.W, padx=14, pady=(8,0))
        tk.Scale(sidebar, from_=0.001, to=0.10, resolution=0.001,
                 orient=tk.HORIZONTAL, variable=self.sensitivity_var,
                 bg=C['panel'], fg=C['text'], highlightthickness=0,
                 length=170, troughcolor=C['border'], showvalue=False).pack(padx=12)

        _sb_section("SESSION")
        self.guided_start_btn = tk.Button(sidebar, text="▶  Start Session",
                                          command=self.start_guided_session,
                                          bg=C['success'], fg='black',
                                          font=("Verdana",10,"bold"), relief=tk.FLAT,
                                          cursor="hand2", width=17, height=2)
        self.guided_start_btn.pack(pady=4, padx=12)
        self.guided_stop_btn  = tk.Button(sidebar, text="⏹  Stop Session",
                                          command=self.stop_guided_session,
                                          bg=C['border'], fg=C['muted'],
                                          font=("Verdana",9,"bold"), relief=tk.FLAT,
                                          cursor="hand2", width=17, state=tk.DISABLED)
        self.guided_stop_btn.pack(pady=3, padx=12)

        _sb_section("HOW IT WORKS")
        tk.Label(sidebar,
            text="①  App plays the note\n"
                 "    on harmonium\n\n"
                 "②  'Now Sing!' prompt\n"
                 "    — match the note\n\n"
                 "③  Score saved to\n"
                 "    Session Stats",
            font=("Verdana",8), fg=C['muted'], bg=C['panel'],
            justify=tk.LEFT).pack(padx=14, pady=4)

        # ── Right main area ──────────────────────────────────────────────
        right = tk.Frame(pg, bg=C['bg'])
        right.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # ── HERO: glow circle + phase info ──────────────────────────────
        hero = tk.Frame(right, bg=C['bg'])
        hero.pack(fill=tk.X, padx=12, pady=10)

        # Target glow circle
        glow_border = tk.Frame(hero, bg=C['border'], padx=1, pady=1)
        glow_border.pack(side=tk.LEFT)
        self.guided_glow_canvas = tk.Canvas(glow_border, width=190, height=190,
                                            bg=C['card'], highlightthickness=0)
        self.guided_glow_canvas.pack()
        self.guided_glow_canvas.bind(
            '<Configure>',
            lambda e: self._draw_glow(self.guided_glow_canvas, '--', 'idle'))

        # Phase info panel
        info_panel = tk.Frame(hero, bg=C['bg'])
        info_panel.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=16)

        # Phase label + countdown
        phase_row = tk.Frame(info_panel, bg=C['bg'])
        phase_row.pack(fill=tk.X, pady=(4,0))
        self.guided_phase_lbl = tk.Label(phase_row, text="Press  ▶ Start Session",
                                         font=("Georgia",16,"bold"),
                                         fg=C['muted'], bg=C['bg'])
        self.guided_phase_lbl.pack(side=tk.LEFT)

        self.guided_countdown = tk.Label(info_panel, text="",
                                         font=("Courier New",38,"bold"),
                                         fg=C['text'], bg=C['bg'])
        self.guided_countdown.pack(anchor=tk.W, pady=(0,4))

        # Progress
        prog_row = tk.Frame(info_panel, bg=C['bg'])
        prog_row.pack(anchor=tk.W)
        tk.Label(prog_row, text="Progress:", font=("Verdana",9),
                 fg=C['muted'], bg=C['bg']).pack(side=tk.LEFT, padx=(0,6))
        self.guided_progress = tk.Label(prog_row, text="—",
                                        font=("Verdana",10,"bold"),
                                        fg=C['teal'], bg=C['bg'])
        self.guided_progress.pack(side=tk.LEFT)

        # You are singing
        sing_row = tk.Frame(info_panel, bg=C['bg'])
        sing_row.pack(anchor=tk.W, pady=(6,0))
        tk.Label(sing_row, text="You're singing:", font=("Verdana",9),
                 fg=C['muted'], bg=C['bg']).pack(side=tk.LEFT, padx=(0,8))
        self.guided_singing_lbl = tk.Label(sing_row, text="--",
                                           font=("Georgia",26,"bold"),
                                           fg=C['text'], bg=C['bg'])
        self.guided_singing_lbl.pack(side=tk.LEFT)

        self.guided_result_lbl = tk.Label(info_panel, text="",
                                          font=("Verdana",10,"bold"),
                                          fg=C['success'], bg=C['bg'],
                                          wraplength=480, justify=tk.LEFT)
        self.guided_result_lbl.pack(anchor=tk.W, pady=(6,0))

        # ── Pitch meter ─────────────────────────────────────────────────
        m_row = tk.Frame(right, bg=C['bg'])
        m_row.pack(fill=tk.X, padx=12, pady=(2,1))
        tk.Label(m_row, text="◀  flat", font=("Verdana",7),
                 fg=C['muted'], bg=C['bg']).pack(side=tk.LEFT)
        tk.Label(m_row, text="PITCH METER", font=("Verdana",7,"bold"),
                 fg=C['label'], bg=C['bg']).pack(side=tk.LEFT, expand=True)
        tk.Label(m_row, text="sharp  ▶", font=("Verdana",7),
                 fg=C['muted'], bg=C['bg']).pack(side=tk.RIGHT)
        self.guided_tuner = tk.Canvas(right, bg="#04040e", height=48,
                                      highlightthickness=0)
        self.guided_tuner.pack(fill=tk.X, padx=12, pady=(0,5))

        # ── Bottom: graph + results (side by side) ───────────────────────
        bottom = tk.Frame(right, bg=C['bg'])
        bottom.pack(fill=tk.BOTH, expand=True, padx=12, pady=(2,6))

        # Left: frequency graph
        graph_outer = tk.Frame(bottom, bg=C['border'], padx=1, pady=1)
        graph_outer.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0,5))
        graph_inner = tk.Frame(graph_outer, bg=C['card'])
        graph_inner.pack(fill=tk.BOTH, expand=True)
        tk.Label(graph_inner, text="YOUR PITCH HISTORY",
                 font=("Verdana",7,"bold"), fg=C['muted'], bg=C['card'],
                 anchor=tk.W).pack(anchor=tk.W, padx=8, pady=(5,0))
        self.guided_graph = tk.Canvas(graph_inner, bg="#03030c",
                                      highlightthickness=0)
        self.guided_graph.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # Right: results list
        results_outer = tk.Frame(bottom, bg=C['border'], padx=1, pady=1, width=300)
        results_outer.pack(side=tk.RIGHT, fill=tk.Y)
        results_outer.pack_propagate(False)
        results_inner = tk.Frame(results_outer, bg=C['card'])
        results_inner.pack(fill=tk.BOTH, expand=True)
        tk.Label(results_inner, text="NOTE RESULTS",
                 font=("Verdana",7,"bold"), fg=C['muted'], bg=C['card'],
                 anchor=tk.W).pack(anchor=tk.W, padx=8, pady=(5,0))
        self.results_canvas = tk.Canvas(results_inner, bg=C['card'],
                                        highlightthickness=0)
        self.results_canvas.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)

    # ═══════════════════════════════════════════════════════════════════════
    #  STATS PAGE
    # ═══════════════════════════════════════════════════════════════════════

    def _build_page_stats(self):
        C  = self.C
        pg = tk.Frame(self.page_host, bg=C['bg'])
        self.page_stats = pg

        head = tk.Frame(pg, bg=C['bg'])
        head.pack(fill=tk.X, padx=20, pady=(16,8))
        tk.Label(head, text="Session Statistics",
                 font=("Georgia",26,"bold"), fg=C['saffron'], bg=C['bg']).pack(side=tk.LEFT)
        tk.Button(head, text="🔄  Clear All", command=self._clear_stats,
                  bg=C['danger'], fg='white', font=("Verdana",9,"bold"),
                  relief=tk.FLAT, cursor="hand2", padx=10, pady=5).pack(side=tk.RIGHT)

        card_outer = tk.Frame(pg, bg=C['border'], padx=1, pady=1)
        card_outer.pack(fill=tk.BOTH, expand=True, padx=20, pady=(0,16))
        card = tk.Frame(card_outer, bg=C['card'])
        card.pack(fill=tk.BOTH, expand=True)
        self.stats_canvas = tk.Canvas(card, bg=C['card'], highlightthickness=0)
        self.stats_canvas.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        self.stats_canvas.bind('<Configure>', lambda _: self._draw_stats())

    # ═══════════════════════════════════════════════════════════════════════
    #  PAGE SWITCHER
    # ═══════════════════════════════════════════════════════════════════════

    def _switch_page(self, pid):
        C = self.C
        pages = {'sa_setup':self.page_sa_setup, 'free':self.page_free,
                 'guided':self.page_guided, 'stats':self.page_stats}
        for p in pages.values(): p.pack_forget()
        pages[pid].pack(fill=tk.BOTH, expand=True)
        self.current_page.set(pid)
        for name, btn in self.nav_btns.items():
            if name == pid:
                btn.config(bg=C['saffron'], fg='black', font=("Verdana",9,"bold"))
            else:
                btn.config(bg='#050510',    fg=C['muted'], font=("Verdana",9))
        if pid == 'stats':
            self._draw_stats()

    # ═══════════════════════════════════════════════════════════════════════
    #  DRAWING — Glow Circle
    # ═══════════════════════════════════════════════════════════════════════

    def _draw_glow(self, canvas, note_text, state, hz_text=""):
        """
        Centrepiece visual. Concentric rings create glow illusion.
        States: idle | listen | singing | hit | miss
        """
        C = self.C
        canvas.delete("all")
        w = canvas.winfo_width(); h = canvas.winfo_height()
        if w < 20 or h < 20:
            return
        cx, cy = w//2, h//2
        r = min(w, h)//2 - 4

        # Ring colours per state
        states_cfg = {
            'idle':    {'glow':['#0c0c20','#101028','#141432'],
                        'face':'#101028', 'ring':'#252545', 'text':C['muted']},
            'listen':  {'glow':['#041422','#06202e','#082a3a'],
                        'face':'#071c2e', 'ring':C['teal'],  'text':C['teal']},
            'singing': {'glow':['#1c1000','#261600','#301c00'],
                        'face':'#201200', 'ring':C['saffron'],'text':C['saffron']},
            'hit':     {'glow':['#001a08','#002814','#003520'],
                        'face':'#001e0c', 'ring':C['success'],'text':C['success']},
            'miss':    {'glow':['#1e0004','#280006','#320008'],
                        'face':'#1c0004', 'ring':C['danger'], 'text':C['danger']},
        }
        cfg = states_cfg.get(state, states_cfg['idle'])

        # Outer glow rings
        for i, col in enumerate(cfg['glow']):
            rr = r - i*6
            canvas.create_oval(cx-rr, cy-rr, cx+rr, cy+rr, fill=col, outline='')

        # Face circle
        fr = r - len(cfg['glow'])*6 - 2
        canvas.create_oval(cx-fr, cy-fr, cx+fr, cy+fr,
                           fill=cfg['face'], outline=cfg['ring'], width=2)

        # Note name
        fs  = 48 if len(note_text) <= 3 else 34
        off = 10 if hz_text else 0
        canvas.create_text(cx, cy - off,
                           text=note_text if note_text != '--' else '·',
                           font=("Georgia", fs, "bold"), fill=cfg['text'])
        if hz_text:
            canvas.create_text(cx, cy + fr - 20,
                               text=hz_text, font=("Courier New",8),
                               fill=cfg['ring'])

        # Label at bottom edge
        state_labels = {'listen':'LISTEN', 'singing':'SING NOW',
                        'hit':'✓  HIT', 'miss':'✗  MISS', 'idle':''}
        lbl = state_labels.get(state, '')
        if lbl:
            canvas.create_text(cx, h - 10, text=lbl,
                               font=("Verdana",7,"bold"), fill=cfg['ring'])

    # ── Pitch meter ────────────────────────────────────────────────────────

    def _draw_tuner(self, canvas, cents):
        C = self.C
        canvas.delete("all")
        w = canvas.winfo_width(); h = canvas.winfo_height()
        if w < 10: return
        mid = w // 2

        # Colour zones
        zones = [(0,w*.20,'#1e0003'),(w*.20,w*.38,'#1a1200'),
                 (w*.38,w*.62,'#001a06'),(w*.62,w*.80,'#1a1200'),
                 (w*.80,w,'#1e0003')]
        for x0,x1,col in zones:
            canvas.create_rectangle(x0,0,x1,h, fill=col, outline='')

        canvas.create_line(mid,0,mid,h, fill=C['success'], width=2)

        for lbl,off in [("−50",-.5),("−25",-.25),("0",0),("+25",.25),("+50",.5)]:
            x = mid + off*w
            canvas.create_text(x,8, text=lbl, fill='#444466', font=("Courier New",7))
            canvas.create_line(x,14,x,20, fill='#333355', width=1)

        if cents is not None:
            cl  = max(-50, min(50, cents))
            nx  = mid + (cl/50)*(w*.5)
            col = (C['success'] if abs(cents)<5 else
                   C['warning'] if abs(cents)<15 else C['danger'])
            canvas.create_rectangle(nx-4,18,nx+4,h-4, fill=col, outline='')
            canvas.create_text(nx, h-10, text=f"{cents:+.0f}¢",
                               fill=col, font=("Courier New",8,"bold"))

    # ── Frequency graph ────────────────────────────────────────────────────

    def _draw_graph(self, canvas):
        C = self.C
        canvas.delete("all")
        if len(self.freq_history) < 2: return
        w = canvas.winfo_width(); h = canvas.winfo_height()
        if w < 10 or h < 10: return

        freqs = list(self.freq_history)
        lo = min(freqs)-20; hi = max(freqs)+20; span = hi-lo
        if span < 1: return

        def fy(f): return h - h*(f-lo)/span

        # Sargam gridlines (dashed) — current Sa
        for n in self.indian_notes:
            for mult in (0.5, 1.0, 2.0):
                t = self.get_note_freq(n['name']) * mult
                if lo <= t <= hi:
                    y    = fy(t)
                    is_sa = n['name'] in ('Sa',"Sa'")
                    canvas.create_line(0,y,w,y,
                        fill='#28220a' if is_sa else '#141428',
                        width=2 if is_sa else 1, dash=(4,4))
                    suf = "₋" if mult==0.5 else ("'" if mult==2.0 else "")
                    canvas.create_text(w-4,y-2,
                        text=n['name'].rstrip("'")+suf,
                        anchor=tk.NE, fill='#2a3a28' if is_sa else '#1e2850',
                        font=("Courier New",7))

        # Horizontal grid
        for i in range(5):
            y = h*i/4
            canvas.create_line(0,y,w,y, fill='#0c0c18', width=1)
            canvas.create_text(4,y+2, text=f"{hi-span*i/4:.0f}",
                               anchor=tk.NW, fill='#28284a', font=("Courier New",7))

        # Frequency polyline with teal glow
        pts = [x for i,f in enumerate(freqs)
               for x in [w*i/(len(freqs)-1), fy(f)]]

        if len(pts) >= 4:
            for thick in (10,7,4,2):
                a   = thick/10
                col = f"#{int(0):02x}{int(170*a):02x}{int(200*a):02x}"
                canvas.create_line(pts, fill=col, width=thick, smooth=True)
            canvas.create_line(pts, fill=C['teal'], width=1.5, smooth=True)

            for i,f in enumerate(freqs):
                x = w*i/(len(freqs)-1); y = fy(f)
                try:    hit = bool(self.match_history[i])
                except: hit = False
                canvas.create_oval(x-2,y-2,x+2,y+2,
                    fill=C['success'] if hit else '#002030', outline='')

    # ── Guided results ─────────────────────────────────────────────────────

    def _draw_guided_results(self):
        C = self.C
        c = self.results_canvas; c.delete("all")
        w = c.winfo_width()
        if w < 10: return
        y = 6
        for r in self.guided_results:
            hp = r['hit_pct']; ac = r['avg_cents']
            col  = C['success'] if r['hit'] else (C['warning'] if hp>=30 else C['danger'])
            icon = "✅" if r['hit'] else ("🟡" if hp>=30 else "❌")
            c.create_text(6, y+10, anchor=tk.NW,
                text=f"{icon}  {r['note']:6s}",
                fill=col, font=("Georgia",10,"bold"))
            c.create_text(80, y+10, anchor=tk.NW,
                text=f"{hp:3.0f}%  {ac:+.0f}¢",
                fill=C['label'], font=("Courier New",9))
            bx = 165; bmax = max(1, w-175)
            bw = int(hp/100*bmax)
            c.create_rectangle(bx,y+4,bx+bmax,y+20, fill='#151530', outline='')
            if bw > 0:
                c.create_rectangle(bx,y+4,bx+bw,y+20, fill=col, outline='')
            y += 26

    # ── Stats bar chart ────────────────────────────────────────────────────

    def _draw_stats(self):
        C = self.C; c = self.stats_canvas; c.delete("all")
        w = c.winfo_width(); h = c.winfo_height()
        if w < 10 or h < 10: return

        note_names = [n['name'] for n in self.indian_notes if n['name'] != "Sa'"]
        active = [(nm, self.note_stats[nm]) for nm in note_names
                  if self.note_stats[nm]['hits']+self.note_stats[nm]['miss'] > 0]

        if not active:
            c.create_text(w//2, h//2,
                text="No data yet.\n\nPractice in Free or Guided mode,\nthen return here to see your progress.",
                fill=C['muted'], font=("Georgia",14), justify=tk.CENTER, anchor=tk.CENTER)
            return

        mL=50; mR=20; mT=50; mB=70
        chart_h = int(h*0.52) - mT

        c.create_text(w//2, 20,
            text="Accuracy per Note  (% of attempts within tolerance)",
            fill=C['teal'], font=("Georgia",13,"bold"), anchor=tk.CENTER)

        for pct in [0,25,50,75,100]:
            y = mT + chart_h - (chart_h*pct/100)
            c.create_line(mL,y,w-mR,y, fill='#1a1a35', dash=(3,3))
            c.create_text(mL-6,y, text=str(pct), fill=C['muted'],
                          font=("Courier New",8), anchor=tk.E)

        bw = (w-mL-mR)//(len(active)+1)
        for i,(nm,st) in enumerate(active):
            total = st['hits']+st['miss']
            pct   = st['hits']/total*100 if total else 0
            x0    = mL + i*bw + 4; x1 = x0+bw-8
            yt    = mT + chart_h - (chart_h*pct/100)
            yb    = mT + chart_h
            col   = C['success'] if pct>=75 else C['warning'] if pct>=40 else C['danger']
            # Glow bar
            c.create_rectangle(x0-2,yt-2,x1+2,yb+2, fill=col, outline='', stipple='gray25')
            c.create_rectangle(x0,yt,x1,yb, fill=col, outline='')
            c.create_text((x0+x1)//2,yt-12, text=f"{pct:.0f}%",
                          fill=col, font=("Verdana",7,"bold"))
            c.create_text((x0+x1)//2,yb+14, text=nm,
                          fill=C['text'], font=("Georgia",9,"bold"))
            c.create_text((x0+x1)//2,yb+28, text=f"{total}",
                          fill=C['muted'], font=("Courier New",7))

        # Cents table
        ty = mT + chart_h + 54
        c.create_text(w//2, ty,
            text="Average Cents Off-pitch  (0 = perfect, lower is better)",
            fill=C['saffron'], font=("Georgia",11,"bold"), anchor=tk.CENTER)
        ty += 22
        cw  = (w-mL-mR)//max(1,len(active))
        for i,(nm,st) in enumerate(active):
            cl  = st.get('cents',[]); avg = float(np.mean(cl)) if cl else 0.0
            col = C['success'] if abs(avg)<5 else C['warning'] if abs(avg)<15 else C['danger']
            x   = mL + i*cw + cw//2
            c.create_text(x,ty,    text=nm,           fill=C['text'],  font=("Georgia",9,"bold"))
            c.create_text(x,ty+16, text=f"{avg:+.1f}¢",fill=col, font=("Courier New",9))

    def _clear_stats(self):
        if messagebox.askyesno("Clear Stats","Clear all session statistics?"):
            self.note_stats.clear(); self._draw_stats()

    # ═══════════════════════════════════════════════════════════════════════
    #  AUDIO PIPELINE
    # ═══════════════════════════════════════════════════════════════════════

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
        self.running = False; self.guided_active = False; self.guided_listen = False
        if self.stream:
            self.stream.stop_stream(); self.stream.close(); self.stream = None
        try:
            self.start_btn.config(state=tk.NORMAL)
            self.stop_btn.config(state=tk.DISABLED)
        except Exception: pass
        self.status_bar.config(text="Stopped")

    def _audio_capture(self):
        while self.running:
            try:
                raw  = self.stream.read(self.CHUNK, exception_on_overflow=False)
                data = np.frombuffer(raw, dtype=np.float32)
                if self.audio_queue.full():
                    try: self.audio_queue.get_nowait()
                    except queue.Empty: pass
                self.audio_queue.put(data)
            except Exception as e:
                print(f"Capture: {e}")

    def _process_audio(self):
        if not self.running: return
        try:
            if not self.audio_queue.empty():
                data = self.audio_queue.get()
                rms  = float(np.sqrt(np.mean(data**2)))
                if rms > self.sensitivity_var.get():
                    raw   = self.detect_pitch_yin(data)
                    freq  = self._smooth(raw)
                    if 60 < freq < 1200:
                        self.freq_history.append(freq)
                        matched, cents_err = self.check_note_match(freq)
                        meter_cents        = self._cents_from_nearest(freq)
                        now = time.time()
                        if matched:
                            base = matched.rstrip("'₋")
                            self.note_stats[base]['hits'] += 1
                            if cents_err is not None:
                                self.note_stats[base]['cents'].append(float(cents_err))
                            self.last_match_time[base] = now

                        pg = self.current_page.get()
                        if pg == 'free':
                            self._free_update(freq, matched, meter_cents, now)
                        elif pg == 'guided':
                            self._guided_voice_update(freq, matched, meter_cents, cents_err)
                else:
                    # Silence
                    if self.current_page.get() == 'free':
                        self._draw_glow(self.free_glow, '--', 'idle')
        except Exception as e:
            print(f"Process: {e}")
        if self.running:
            self.root.after(50, self._process_audio)

    # ── Free practice update ───────────────────────────────────────────────

    def _free_update(self, freq, matched, meter_cents, now):
        C = self.C
        self.free_freq_lbl.config(text=f"{freq:.1f} Hz")

        if matched:
            glow_state = 'hit'
            self.match_history.append(True)
            clr = (C['success'] if abs(meter_cents)<5 else
                   C['warning'] if abs(meter_cents)<15 else C['danger'])
            self.free_cents_lbl.config(text=f"{meter_cents:+.0f}¢", fg=clr)
            self.free_raga_lbl.config(text=matched, fg=C['saffron'])
        else:
            glow_state = 'singing'
            self.match_history.append(False)
            self.free_cents_lbl.config(text="--¢", fg=C['muted'])
            self.free_raga_lbl.config(text="--", fg=C['muted'])

        note_display = matched if matched else "--"
        self._draw_glow(self.free_glow, note_display, glow_state,
                        hz_text=f"{freq:.1f} Hz")

        # Stability indicator
        recent = list(self.freq_history)[-10:]
        if len(recent) >= 4:
            std  = np.std(recent)
            stab = max(0, 100-int(std*5))
            sc   = C['success'] if stab>80 else C['warning'] if stab>50 else C['danger']
            self.free_stab_lbl.config(text=f"{stab}%", fg=sc)

        # Button highlights
        for name, btn in self.sargam_btns.items():
            stripped = name.rstrip("'")
            bg_def   = C['border'] if name in self.MAIN_NOTES else C['komal']
            if now - self.last_match_time.get(stripped, 0.0) < self.note_hold_time:
                btn.config(bg=C['success'], fg='black')
            else:
                btn.config(bg=bg_def, fg=C['text'] if name in self.MAIN_NOTES else C['muted'])

        self._draw_tuner(self.free_tuner, meter_cents)
        self._draw_graph(self.free_graph)
        self.status_bar.config(
            text=f"Freq: {freq:.1f} Hz  |  Sa: {self.sa_base:.1f} Hz"
                 + (f"  |  ✓  {matched}" if matched else ""))

    # ═══════════════════════════════════════════════════════════════════════
    #  GUIDED RIYAAZ ENGINE
    # ═══════════════════════════════════════════════════════════════════════

    def _build_exercise_sequence(self):
        ex = self.EXERCISES.get(self.selected_exercise.get(), ['Sa'])
        if ex == '__random__':
            raga = self.selected_raga.get()
            pool = self.RAGAS.get(raga) or [n['name'] for n in self.indian_notes
                                             if n['name'] != "Sa'"]
            return [random.choice(pool) for _ in range(8)]
        return list(ex)

    def start_guided_session(self):
        if not self.running:
            try:
                self.stream = self.p.open(format=self.FORMAT, channels=self.CHANNELS,
                                          rate=self.RATE, input=True,
                                          frames_per_buffer=self.CHUNK)
                self.running = True
                threading.Thread(target=self._audio_capture, daemon=True).start()
                self._process_audio()
            except Exception as e:
                messagebox.showerror("Mic Error", str(e)); return

        self.guided_sequence = self._build_exercise_sequence()
        self.guided_step     = 0
        self.guided_results  = []
        self.guided_active   = True
        self.guided_start_btn.config(state=tk.DISABLED)
        self.guided_stop_btn.config(state=tk.NORMAL, bg=self.C['warning'], fg='black')
        self._guided_next_step()

    def _guided_next_step(self):
        if not self.guided_active: return
        if self.guided_step >= len(self.guided_sequence):
            self._guided_finish(); return

        C             = self.C
        note_name     = self.guided_sequence[self.guided_step]
        target_freq   = self.get_note_freq(note_name)
        total         = len(self.guided_sequence)

        self.guided_target    = note_name
        self.guided_cents_buf = []
        self.guided_listen    = False
        self.guided_glow_state = 'listen'

        self._draw_glow(self.guided_glow_canvas, note_name, 'listen',
                        hz_text=f"{target_freq:.1f} Hz")
        self.guided_phase_lbl.config(text="🎵  LISTEN ...", fg=C['teal'])
        self.guided_countdown.config(text="")
        self.guided_result_lbl.config(text="")
        self.guided_singing_lbl.config(text="--", fg=C['muted'])
        self.guided_progress.config(text=f"{self.guided_step+1} / {total}")

        self.play_note_tone(note_name)
        self.root.after(1750, self._guided_start_sing)

    def _guided_start_sing(self):
        if not self.guided_active: return
        C = self.C
        self.guided_listen       = True
        self.guided_listen_start = time.time()
        self.guided_glow_state   = 'singing'
        self._draw_glow(self.guided_glow_canvas, self.guided_target, 'singing',
                        hz_text=f"{self.get_note_freq(self.guided_target):.1f} Hz")
        self.guided_phase_lbl.config(text="🎤  NOW SING!", fg=C['saffron'])
        self._guided_tick()

    def _guided_tick(self):
        if not self.guided_active or not self.guided_listen: return
        elapsed   = time.time() - self.guided_listen_start
        remaining = self.note_duration_var.get() - elapsed
        if remaining <= 0:
            self._guided_end_sing(); return
        self.guided_countdown.config(text=f"{remaining:.1f}s")
        self.root.after(100, self._guided_tick)

    def _guided_end_sing(self):
        C  = self.C
        self.guided_listen = False
        self.guided_countdown.config(text="")
        buf = self.guided_cents_buf

        if buf:
            hit_frames = [c for c in buf if c <= self.tolerance_cents]
            hit_pct    = len(hit_frames)/len(buf)*100
            avg_cents  = float(np.mean(buf))
            hit        = hit_pct >= 55
            if   hit_pct >= 80:
                txt = f"✅  Excellent!  {hit_pct:.0f}% on pitch  |  avg {avg_cents:.0f}¢ off"
                col = C['success']; gs = 'hit'
            elif hit_pct >= 55:
                txt = f"✅  Good  {hit_pct:.0f}% on pitch  |  avg {avg_cents:.0f}¢ off"
                col = C['success']; gs = 'hit'
            elif hit_pct >= 30:
                txt = f"🟡  Getting close  {hit_pct:.0f}% on pitch  |  avg {avg_cents:.0f}¢ off"
                col = C['warning']; gs = 'miss'
            else:
                txt = f"❌  Missed  {hit_pct:.0f}% on pitch  |  avg {avg_cents:.0f}¢ off"
                col = C['danger']; gs = 'miss'
        else:
            hit  = False; hit_pct = 0; avg_cents = 0; gs = 'miss'
            txt  = "⚠️  No voice detected — sing louder or adjust sensitivity"
            col  = C['warning']

        self._draw_glow(self.guided_glow_canvas, self.guided_target, gs,
                        hz_text=f"{self.get_note_freq(self.guided_target):.1f} Hz")
        self.guided_result_lbl.config(text=txt, fg=col)
        self.guided_phase_lbl.config(text="")

        base = self.guided_target.rstrip("'")
        if hit: self.note_stats[base]['hits'] += 1
        else:   self.note_stats[base]['miss'] += 1

        self.guided_results.append(
            {'note':self.guided_target,'hit':hit,'hit_pct':hit_pct,'avg_cents':avg_cents})
        self._draw_guided_results()

        self.guided_step += 1
        self.root.after(2000, self._guided_next_step)

    def _guided_voice_update(self, freq, matched, meter_cents, cents_err):
        """Called from audio loop during the singing window."""
        C = self.C
        if matched:
            base_match  = matched.rstrip("'₋")
            base_target = (self.guided_target or '').rstrip("'")
            correct     = base_match == base_target
            if correct:
                self.guided_singing_lbl.config(text=matched, fg=C['success'])
                if cents_err is not None:
                    self.guided_cents_buf.append(float(cents_err))
            else:
                self.guided_singing_lbl.config(text=matched, fg=C['danger'])
                self.guided_cents_buf.append(float(self.tolerance_cents + 20))
            self.match_history.append(correct)
        else:
            self.guided_singing_lbl.config(text="--", fg=C['muted'])
            self.match_history.append(False)

        self._draw_tuner(self.guided_tuner, meter_cents)
        self._draw_graph(self.guided_graph)   # ← Graph always visible in guided

    def _guided_finish(self):
        C     = self.C
        total = len(self.guided_results)
        hits  = sum(1 for r in self.guided_results if r['hit'])
        self.guided_active = False
        self._draw_glow(self.guided_glow_canvas, f"{hits}/{total}", 'hit'
                        if hits >= total//2 else 'miss')
        self.guided_phase_lbl.config(
            text=f"🎉  Complete!  {hits} / {total} notes hit",
            fg=C['success'] if hits >= total//2 else C['warning'])
        self.guided_countdown.config(text="")
        self.guided_start_btn.config(state=tk.NORMAL)
        self.guided_stop_btn.config(state=tk.DISABLED, bg=C['border'], fg=C['muted'])
        self.status_bar.config(
            text=f"Session complete — {hits}/{total} hit  |  See Stats for details")

    def stop_guided_session(self):
        C = self.C
        self.guided_active = False; self.guided_listen = False
        self.guided_phase_lbl.config(text="Session stopped", fg=C['warning'])
        self.guided_countdown.config(text="")
        self.guided_start_btn.config(state=tk.NORMAL)
        self.guided_stop_btn.config(state=tk.DISABLED, bg=C['border'], fg=C['muted'])

    # ═══════════════════════════════════════════════════════════════════════
    #  CLEANUP
    # ═══════════════════════════════════════════════════════════════════════

    def on_closing(self):
        self.running = False; self.metro_running = False
        self.drone_playing = False; self.guided_active = False
        time.sleep(0.15)
        if self.stream:
            try: self.stream.stop_stream(); self.stream.close()
            except Exception: pass
        try: self.p.terminate()
        except Exception: pass
        self.root.destroy()


# ─────────────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    root = tk.Tk()
    app  = VocalRiyaaz(root)
    root.protocol("WM_DELETE_WINDOW", app.on_closing)
    try:
        root.mainloop()
    except KeyboardInterrupt:
        try: app.on_closing()
        except Exception: pass
        sys.exit(0)
