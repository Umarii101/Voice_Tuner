import tkinter as tk
from tkinter import ttk, messagebox
import numpy as np
import pyaudio
import threading
import queue
import time
from scipy import signal
from collections import deque
import colorsys
import sys

class VocalPitchAnalyzer:
    def __init__(self, root):
        self.root = root
        self.root.title("Vocal Pitch Analyzer Pro")
        self.root.geometry("1200x800")
        self.root.configure(bg="#1a1a2e")
        
        # Audio parameters
        self.CHUNK = 4096
        self.FORMAT = pyaudio.paFloat32
        self.CHANNELS = 1
        self.RATE = 44100
        self.running = False
        self.calibrated = False
        self.calibration_offset = 0
        
        # Note definitions (A4 = 440 Hz standard)
        self.notes = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B']
        self.A4 = 440.0
        
        # Indian classical music notes (Sargam) - Using EQUAL TEMPERAMENT
        # This matches how most modern singers actually sing
        self.sa_base = 200.0  # Changed default to more common vocal range
        
        # Equal temperament semitone ratios (more practical for detection)
        self.indian_notes = [
            {'name': 'Sa', 'semitones': 0},    # Tonic
            {'name': 'Re♭', 'semitones': 1},   # Komal Re
            {'name': 'Re', 'semitones': 2},    # Shuddh Re
            {'name': 'Ga♭', 'semitones': 3},   # Komal Ga (sometimes called Re#)
            {'name': 'Ga', 'semitones': 4},    # Shuddh Ga
            {'name': 'Ma', 'semitones': 5},    # Shuddh Ma
            {'name': 'Ma#', 'semitones': 6},   # Tivra Ma
            {'name': 'Pa', 'semitones': 7},    # Pa
            {'name': 'Dha♭', 'semitones': 8},  # Komal Dha
            {'name': 'Dha', 'semitones': 9},   # Shuddh Dha
            {'name': 'Ni♭', 'semitones': 10},  # Komal Ni
            {'name': 'Ni', 'semitones': 11},   # Shuddh Ni
            {'name': 'Sa\'', 'semitones': 12}  # Upper Sa
        ]
        
        # Calculate frequencies for each note
        self.update_indian_note_frequencies()
        
        # TIGHTENED tolerance for note detection (in cents)
        self.indian_note_tolerance = 15  # Reduced from 25 to 15 cents
        self.active_indian_notes = set()
        self.note_hold_counter = {}
        
        # Helper for sargam names and hold behavior
        self.sargam_names = [n['name'] for n in self.indian_notes]
        self.last_match_time = {n: 0.0 for n in self.sargam_names}
        self.note_hold_time = 0.9
        
        # AUTO-SA DETECTION
        self.auto_sa_enabled = tk.BooleanVar(value=True)
        self.sa_detection_samples = deque(maxlen=50)  # Store recent frequencies
        self.sa_locked = False
        
        # Data storage
        self.freq_history = deque(maxlen=150)
        self.note_history = deque(maxlen=150)
        self.match_history = deque(maxlen=150)
        self.audio_queue = queue.Queue()
        
        # PyAudio setup
        self.p = pyaudio.PyAudio()
        self.stream = None
        
        self.setup_ui()
    
    def update_indian_note_frequencies(self):
        """Calculate frequencies using equal temperament"""
        for note in self.indian_notes:
            # Frequency = Sa * 2^(semitones/12)
            note['freq'] = self.sa_base * (2 ** (note['semitones'] / 12))
        
    def setup_ui(self):
        # Modern color scheme
        self.bg_dark = "#1a1a2e"
        self.bg_medium = "#16213e"
        self.bg_light = "#0f3460"
        self.accent = "#00d9ff"
        self.accent2 = "#ff00ff"
        self.text_color = "#ffffff"
        self.success = "#00ff88"
        self.warning = "#ffaa00"
        
        # Title
        title_frame = tk.Frame(self.root, bg=self.bg_dark)
        title_frame.pack(fill=tk.X, padx=20, pady=(20, 10))
        
        title = tk.Label(title_frame, text="🎤 VOCAL PITCH ANALYZER PRO", 
                        font=("Arial", 28, "bold"), fg=self.accent, bg=self.bg_dark)
        title.pack()
        
        subtitle = tk.Label(title_frame, text="Real-time Frequency & Sargam Detection", 
                           font=("Arial", 12), fg=self.text_color, bg=self.bg_dark)
        subtitle.pack()
        
        # Main container
        main_frame = tk.Frame(self.root, bg=self.bg_dark)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        # Left panel - Controls
        left_panel = tk.Frame(main_frame, bg=self.bg_medium, relief=tk.RAISED, bd=2)
        left_panel.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 10))
        
        # Control buttons
        controls_label = tk.Label(left_panel, text="CONTROLS", 
                                 font=("Arial", 14, "bold"), fg=self.accent, bg=self.bg_medium)
        controls_label.pack(pady=(20, 15))
        
        self.start_btn = tk.Button(left_panel, text="▶ START", command=self.start_analysis,
                                   bg=self.success, fg="black", font=("Arial", 12, "bold"),
                                   relief=tk.FLAT, cursor="hand2", width=15, height=2)
        self.start_btn.pack(pady=5, padx=20)
        
        self.stop_btn = tk.Button(left_panel, text="⏸ STOP", command=self.stop_analysis,
                                  bg=self.warning, fg="black", font=("Arial", 12, "bold"),
                                  relief=tk.FLAT, cursor="hand2", width=15, height=2, state=tk.DISABLED)
        self.stop_btn.pack(pady=5, padx=20)
        
        # Auto-detect Sa checkbox
        auto_sa_check = tk.Checkbutton(left_panel, text="🎯 Auto-Detect Sa", 
                                       variable=self.auto_sa_enabled,
                                       font=("Arial", 10, "bold"), fg=self.accent, 
                                       bg=self.bg_medium, selectcolor=self.bg_light,
                                       activebackground=self.bg_medium, activeforeground=self.accent)
        auto_sa_check.pack(pady=5, padx=20)
        
        # Lock Sa button
        self.lock_sa_btn = tk.Button(left_panel, text="🔒 Lock Sa", command=self.toggle_sa_lock,
                                     bg=self.accent2, fg="black", font=("Arial", 10, "bold"),
                                     relief=tk.FLAT, cursor="hand2", width=15)
        self.lock_sa_btn.pack(pady=5, padx=20)
        
        # Settings
        settings_label = tk.Label(left_panel, text="SETTINGS", 
                                 font=("Arial", 14, "bold"), fg=self.accent, bg=self.bg_medium)
        settings_label.pack(pady=(30, 15))
        
        # Sensitivity slider
        tk.Label(left_panel, text="Sensitivity", font=("Arial", 10), 
                fg=self.text_color, bg=self.bg_medium).pack()
        self.sensitivity_var = tk.DoubleVar(value=0.01)
        self.sensitivity_slider = tk.Scale(left_panel, from_=0.001, to=0.1, resolution=0.001,
                                          orient=tk.HORIZONTAL, variable=self.sensitivity_var,
                                          bg=self.bg_light, fg=self.text_color, 
                                          highlightthickness=0, length=150)
        self.sensitivity_slider.pack(pady=5, padx=20)

        # Tolerance slider
        tk.Label(left_panel, text="Note Tolerance (cents)", font=("Arial", 10),
                fg=self.text_color, bg=self.bg_medium).pack(pady=(10,0))
        self.tolerance_var = tk.DoubleVar(value=15)
        self.tolerance_slider = tk.Scale(left_panel, from_=5, to=50, resolution=1,
                                        orient=tk.HORIZONTAL, variable=self.tolerance_var,
                                        bg=self.bg_light, fg=self.text_color,
                                        highlightthickness=0, length=150,
                                        command=self.update_tolerance)
        self.tolerance_slider.pack(pady=5, padx=20)

        # Sa base control
        tk.Label(left_panel, text="Manual Sa (Hz)", font=("Arial", 10),
            fg=self.text_color, bg=self.bg_medium).pack(pady=(12, 0))
        self.sa_var = tk.DoubleVar(value=self.sa_base)
        self.sa_entry = tk.Entry(left_panel, textvariable=self.sa_var, width=10)
        self.sa_entry.pack(pady=5, padx=20)
        self.apply_sa_btn = tk.Button(left_panel, text="Apply Sa Manually", command=self.apply_sa_base,
                          bg=self.accent2, fg="black", font=("Arial", 10, "bold"))
        self.apply_sa_btn.pack(pady=5)
        
        # Info panel
        info_frame = tk.Frame(left_panel, bg=self.bg_light, relief=tk.SUNKEN, bd=1)
        info_frame.pack(pady=20, padx=20, fill=tk.X)
        
        tk.Label(info_frame, text="ℹ INFO", font=("Arial", 10, "bold"), 
                fg=self.accent, bg=self.bg_light).pack(pady=5)
        tk.Label(info_frame, text="1. Enable Auto-Detect Sa\n2. START and sing Sa\n3. Lock Sa once detected\n4. Sing other notes!", 
                font=("Arial", 9), fg=self.text_color, bg=self.bg_light, justify=tk.LEFT).pack(pady=5, padx=10)
        
        # Right panel - Display
        right_panel = tk.Frame(main_frame, bg=self.bg_medium)
        right_panel.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
        
        # Current note display (large)
        note_frame = tk.Frame(right_panel, bg=self.bg_dark, relief=tk.RAISED, bd=3)
        note_frame.pack(fill=tk.X, padx=10, pady=10)
        
        tk.Label(note_frame, text="DETECTED SARGAM", font=("Arial", 12), 
                fg=self.accent, bg=self.bg_dark).pack(pady=(10, 0))
        
        self.note_label = tk.Label(note_frame, text="--", font=("Arial", 72, "bold"),
                                   fg=self.success, bg=self.bg_dark)
        self.note_label.pack(pady=10)
        
        # Frequency display
        freq_frame = tk.Frame(right_panel, bg=self.bg_light, relief=tk.RAISED, bd=2)
        freq_frame.pack(fill=tk.X, padx=10, pady=5)
        
        tk.Label(freq_frame, text="FREQUENCY (Hz)", font=("Arial", 11), 
                fg=self.accent, bg=self.bg_light).pack(side=tk.LEFT, padx=20, pady=10)
        
        self.freq_label = tk.Label(freq_frame, text="0.00 Hz", font=("Arial", 28, "bold"),
                                   fg=self.text_color, bg=self.bg_light)
        self.freq_label.pack(side=tk.RIGHT, padx=20, pady=10)
        
        # Current Sa display
        sa_frame = tk.Frame(right_panel, bg=self.bg_light, relief=tk.RAISED, bd=2)
        sa_frame.pack(fill=tk.X, padx=10, pady=5)
        
        tk.Label(sa_frame, text="CURRENT Sa", font=("Arial", 11), 
                fg=self.accent, bg=self.bg_light).pack(side=tk.LEFT, padx=20, pady=10)
        
        self.sa_display = tk.Label(sa_frame, text=f"{self.sa_base:.2f} Hz", font=("Arial", 20, "bold"),
                                   fg=self.warning, bg=self.bg_light)
        self.sa_display.pack(side=tk.RIGHT, padx=20, pady=10)
        
        # Cents deviation
        cents_frame = tk.Frame(right_panel, bg=self.bg_light, relief=tk.RAISED, bd=2)
        cents_frame.pack(fill=tk.X, padx=10, pady=5)
        
        tk.Label(cents_frame, text="CENTS FROM NOTE", font=("Arial", 11), 
                fg=self.accent, bg=self.bg_light).pack(side=tk.LEFT, padx=20, pady=10)
        
        self.cents_label = tk.Label(cents_frame, text="0", font=("Arial", 24, "bold"),
                                    fg=self.text_color, bg=self.bg_light)
        self.cents_label.pack(side=tk.RIGHT, padx=20, pady=10)
        
        # Sargam (Indian notes) display - show 7 main notes
        sargam_frame = tk.Frame(right_panel, bg=self.bg_dark)
        sargam_frame.pack(fill=tk.X, padx=10, pady=(5, 0))
        tk.Label(sargam_frame, text="S A R G A M (Main Notes)", font=("Arial", 10, "bold"),
                 fg=self.accent, bg=self.bg_dark).pack(anchor=tk.W, padx=5)
        self.sargam_labels = {}
        
        # Show only main sargam notes (Sa, Re, Ga, Ma, Pa, Dha, Ni, Sa')
        main_notes = ['Sa', 'Re', 'Ga', 'Ma', 'Pa', 'Dha', 'Ni', 'Sa\'']
        notes_frame = tk.Frame(sargam_frame, bg=self.bg_dark)
        notes_frame.pack(fill=tk.X, padx=5, pady=(4,8))
        
        for note_name in main_notes:
            note_info = next((n for n in self.indian_notes if n['name'] == note_name), None)
            if note_info:
                lbl = tk.Label(notes_frame, text=f"{note_info['name']}\n{note_info['freq']:.1f}Hz", 
                              font=("Arial", 10, "bold"),
                              fg=self.text_color, bg=self.bg_dark, width=10, height=2, relief=tk.FLAT)
                lbl.pack(side=tk.LEFT, padx=3)
                self.sargam_labels[note_info['name']] = lbl
        
        # Graph canvas
        graph_frame = tk.Frame(right_panel, bg=self.bg_dark, relief=tk.SUNKEN, bd=2)
        graph_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        tk.Label(graph_frame, text="FREQUENCY HISTORY", font=("Arial", 12), 
                fg=self.accent, bg=self.bg_dark).pack(pady=5)
        
        self.canvas = tk.Canvas(graph_frame, bg="#0a0a15", highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Status bar
        self.status_bar = tk.Label(self.root, text="Ready to start - Enable Auto-Detect Sa and sing!", 
                                   font=("Arial", 9), fg=self.text_color, 
                                   bg=self.bg_light, anchor=tk.W, relief=tk.SUNKEN)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)
    
    def update_tolerance(self, val):
        """Update tolerance when slider changes"""
        self.indian_note_tolerance = float(val)
    
    def toggle_sa_lock(self):
        """Lock or unlock Sa detection"""
        self.sa_locked = not self.sa_locked
        if self.sa_locked:
            self.lock_sa_btn.config(text="🔓 Unlock Sa", bg=self.success)
            self.sa_display.config(fg=self.success)
            self.status_bar.config(text=f"Sa locked at {self.sa_base:.2f} Hz - Now sing other notes!")
        else:
            self.lock_sa_btn.config(text="🔒 Lock Sa", bg=self.accent2)
            self.sa_display.config(fg=self.warning)
            self.status_bar.config(text="Sa unlocked - Auto-detection active")
    
    def auto_detect_sa(self, freq):
        """Automatically detect and set Sa based on sung frequency"""
        if not self.auto_sa_enabled.get() or self.sa_locked:
            return
        
        # Add to detection samples
        self.sa_detection_samples.append(freq)
        
        # Need enough samples for reliable detection
        if len(self.sa_detection_samples) < 20:
            return
        
        # Find most common frequency cluster (likely Sa if singer is holding it)
        samples = list(self.sa_detection_samples)
        median_freq = np.median(samples)
        
        # Check if frequencies are stable (singer holding a note)
        std_dev = np.std(samples[-10:])  # Check last 10 samples
        
        if std_dev < 3.0:  # Stable note being held
            # Round to nearest sensible Sa (semitone of common bases)
            # Common Sa values: C3=130, C#3=138, D3=146, etc.
            # Find nearest semitone to median
            c3 = 130.81  # C3 reference
            semitones_from_c3 = 12 * np.log2(median_freq / c3)
            nearest_semitone = round(semitones_from_c3)
            detected_sa = c3 * (2 ** (nearest_semitone / 12))
            
            # Only update if significantly different (more than 10 Hz)
            if abs(detected_sa - self.sa_base) > 10:
                self.sa_base = detected_sa
                self.sa_var.set(detected_sa)
                self.update_indian_note_frequencies()
                self.update_sargam_display()
                self.sa_display.config(text=f"{self.sa_base:.2f} Hz")
        
    def freq_to_note(self, freq):
        """Convert frequency to note name and cents deviation"""
        if freq < 20:
            return "--", 0, 0
        
        # Calculate the number of half steps from A4
        half_steps = 12 * np.log2(freq / self.A4)
        note_number = int(round(half_steps)) % 12
        octave = int(np.floor(np.log2(freq / self.A4 * 16)))
        
        note = self.notes[note_number]
        
        # Calculate cents deviation from the nearest note
        nearest_note_freq = self.A4 * (2 ** (round(half_steps) / 12))
        cents = 1200 * np.log2(freq / nearest_note_freq)
        
        return f"{note}{octave}", cents, nearest_note_freq
        
    def detect_pitch(self, audio_data):
        """Detect pitch using autocorrelation method"""
        # Apply window
        windowed = audio_data * np.hanning(len(audio_data))
        
        # Autocorrelation
        correlation = np.correlate(windowed, windowed, mode='full')
        correlation = correlation[len(correlation)//2:]
        
        # Find the first peak after the zero lag
        diff = np.diff(correlation)
        start = np.where(diff > 0)[0]
        if len(start) == 0:
            return 0
        start = start[0]
        
        peak = np.argmax(correlation[start:]) + start
        
        if peak == 0:
            return 0
            
        # Parabolic interpolation for better accuracy
        if peak < len(correlation) - 1:
            y0, y1, y2 = correlation[peak-1:peak+2]
            offset = 0.5 * (y0 - y2) / (y0 - 2*y1 + y2)
            peak = peak + offset
        
        frequency = self.RATE / peak
        
        return frequency
        
    def audio_callback(self):
        """Continuous audio capture"""
        while self.running:
            try:
                data = self.stream.read(self.CHUNK, exception_on_overflow=False)
                audio_data = np.frombuffer(data, dtype=np.float32)
                self.audio_queue.put(audio_data)
            except Exception as e:
                print(f"Audio error: {e}")
                
    def process_audio(self):
        """Process audio data and update UI"""
        if not self.running:
            return
            
        try:
            if not self.audio_queue.empty():
                audio_data = self.audio_queue.get()
                
                # Check if signal is strong enough
                rms = np.sqrt(np.mean(audio_data**2))
                if rms > self.sensitivity_var.get():
                    freq = self.detect_pitch(audio_data)
                    
                    if 80 < freq < 1000:  # Valid vocal range
                        # Auto-detect Sa if enabled
                        self.auto_detect_sa(freq)
                        
                        self.freq_history.append(freq)
                        note, cents, target_freq = self.freq_to_note(freq)
                        self.note_history.append(note)
                        
                        # Update labels
                        self.freq_label.config(text=f"{freq:.2f} Hz")
                        
                        # Check Indian note matches
                        matched_sargam = self.check_indian_notes(freq)
                        now = time.time()
                        
                        if matched_sargam:
                            self.note_label.config(text=matched_sargam, fg=self.success)
                            self.last_match_time[matched_sargam] = now
                            self.match_history.append(True)
                            
                            # Calculate cents from matched note
                            matched_note_info = next((n for n in self.indian_notes if n['name'] == matched_sargam), None)
                            if matched_note_info:
                                cents_from_sargam = 1200 * np.log2(freq / matched_note_info['freq'])
                                self.cents_label.config(text=f"{cents_from_sargam:+.0f}")
                                
                                if abs(cents_from_sargam) < 5:
                                    self.cents_label.config(fg=self.success)
                                elif abs(cents_from_sargam) < 15:
                                    self.cents_label.config(fg=self.warning)
                                else:
                                    self.cents_label.config(fg="#ff4444")
                        else:
                            self.note_label.config(text="--", fg=self.text_color)
                            self.cents_label.config(text="--")
                            self.match_history.append(False)
                        
                        # Update sargam labels color based on recent matches
                        for sargam_name in self.sargam_labels.keys():
                            lbl = self.sargam_labels[sargam_name]
                            if now - self.last_match_time.get(sargam_name, 0.0) < self.note_hold_time:
                                lbl.config(fg=self.success, font=("Arial", 10, "bold"))
                            else:
                                lbl.config(fg=self.text_color, font=("Arial", 10, "normal"))
                        
                        status_text = f"Freq: {freq:.2f} Hz | Sa: {self.sa_base:.2f} Hz"
                        if matched_sargam:
                            status_text += f" | Note: {matched_sargam}"
                        self.status_bar.config(text=status_text)
                        
                        # Update graph
                        self.draw_graph()
        except Exception as e:
            print(f"Processing error: {e}")
        
        if self.running:
            self.root.after(50, self.process_audio)
            
    def draw_graph(self):
        """Draw frequency history graph"""
        self.canvas.delete("all")
        
        if len(self.freq_history) < 2:
            return
            
        width = self.canvas.winfo_width()
        height = self.canvas.winfo_height()
        
        if width < 10 or height < 10:
            return
        
        # Get frequency range
        freqs = list(self.freq_history)
        min_freq = min(freqs) - 20
        max_freq = max(freqs) + 20
        freq_range = max_freq - min_freq
        
        if freq_range < 1:
            return
        
        # Draw grid lines
        for i in range(5):
            y = height * i / 4
            self.canvas.create_line(0, y, width, y, fill="#1a1a2e", width=1)
            freq_val = max_freq - (freq_range * i / 4)
            self.canvas.create_text(5, y, text=f"{freq_val:.0f}", anchor=tk.NW, 
                                   fill="#666666", font=("Arial", 8))
        
        # Draw frequency line with gradient
        points = []
        for i, freq in enumerate(freqs):
            x = width * i / (len(freqs) - 1)
            y = height - (height * (freq - min_freq) / freq_range)
            points.extend([x, y])
        
        if len(points) >= 4:
            # Draw line with glow effect
            for offset in [4, 3, 2, 1]:
                alpha = offset / 4
                color_val = int(255 * alpha)
                color = f"#{color_val:02x}{200:02x}{255:02x}"
                self.canvas.create_line(points, fill=color, width=offset*2, smooth=True)
            
            self.canvas.create_line(points, fill=self.accent, width=2, smooth=True)
            
            # Draw points, color green if matched recently
            num_pts = len(freqs)
            for i in range(num_pts):
                x = width * i / (num_pts - 1)
                y = height - (height * (freqs[i] - min_freq) / freq_range)
                matched = False
                try:
                    matched = bool(self.match_history[i])
                except Exception:
                    matched = False
                if matched:
                    fill = self.success
                    outline = "#88ffcc"
                else:
                    fill = "#004c66"
                    outline = self.accent
                self.canvas.create_oval(x-3, y-3, x+3, y+3, fill=fill, outline=outline)
        
        # Draw center line
        center_y = height / 2
        self.canvas.create_line(0, center_y, width, center_y, fill="#ff00ff", width=1, dash=(5, 5))

    def apply_sa_base(self):
        """Apply new Sa base frequency manually"""
        try:
            val = float(self.sa_var.get())
            if val <= 0 or val < 80 or val > 500:
                raise ValueError('Sa must be between 80-500 Hz')
            self.sa_base = val
            self.update_indian_note_frequencies()
            self.update_sargam_display()
            self.sa_display.config(text=f"{self.sa_base:.2f} Hz")
            self.sa_locked = True
            self.toggle_sa_lock()  # Lock it after manual setting
            messagebox.showinfo('Sa Updated', f'Sa manually set to {self.sa_base:.2f} Hz and locked')
        except Exception as e:
            messagebox.showerror('Invalid value', f'Please enter a valid Sa frequency (80-500 Hz).\n{e}')
    
    def update_sargam_display(self):
        """Update the displayed frequencies in sargam labels"""
        for note_name, lbl in self.sargam_labels.items():
            note_info = next((n for n in self.indian_notes if n['name'] == note_name), None)
            if note_info:
                lbl.config(text=f"{note_info['name']}\n{note_info['freq']:.1f}Hz")

    def check_indian_notes(self, freq):
        """Return the closest Indian note ONLY if within tolerance, otherwise None"""
        if freq is None or freq <= 0:
            return None

        closest_note = None
        closest_cents = float('inf')

        # Include octave variations (lower and upper octaves)
        # Check notes in current octave, one below, and one above
        for octave_mult in [0.5, 1.0, 2.0]:  # Lower octave, current, upper octave
            for n in self.indian_notes:
                target = n['freq'] * octave_mult
                
                # Skip if target is out of reasonable vocal range
                if target < 80 or target > 1000:
                    continue
                
                cents = abs(1200 * np.log2(freq / target))

                if cents < closest_cents:
                    closest_cents = cents
                    if octave_mult == 0.5:
                        closest_note = n['name'].replace("'", "") + "₋"  # Lower octave marker
                    elif octave_mult == 2.0 and n['name'] != "Sa'":
                        closest_note = n['name'] + "'"  # Upper octave marker
                    else:
                        closest_note = n['name']

        # CRITICAL: Return None if not within tolerance
        if closest_cents > self.indian_note_tolerance:
            return None
        
        return closest_note
        
    def start_analysis(self):
        """Start audio analysis"""
        try:
            self.stream = self.p.open(format=self.FORMAT,
                                     channels=self.CHANNELS,
                                     rate=self.RATE,
                                     input=True,
                                     frames_per_buffer=self.CHUNK)
            
            self.running = True
            self.start_btn.config(state=tk.DISABLED)
            self.stop_btn.config(state=tk.NORMAL)
            
            if self.auto_sa_enabled.get() and not self.sa_locked:
                self.status_bar.config(text="Listening... Sing and hold 'Sa' to auto-detect!")
            else:
                self.status_bar.config(text="Listening... Start singing!")
            
            # Start audio thread
            audio_thread = threading.Thread(target=self.audio_callback, daemon=True)
            audio_thread.start()
            
            # Start processing
            self.process_audio()
            
        except Exception as e:
            messagebox.showerror("Error", f"Could not start audio input:\n{str(e)}")
            
    def stop_analysis(self):
        """Stop audio analysis"""
        self.running = False
        if self.stream:
            self.stream.stop_stream()
            self.stream.close()
        self.start_btn.config(state=tk.NORMAL)
        self.stop_btn.config(state=tk.DISABLED)
        self.status_bar.config(text="Stopped")
        
    def on_closing(self):
        """Clean up on exit"""
        self.running = False
        if self.stream:
            self.stream.stop_stream()
            self.stream.close()
        self.p.terminate()
        self.root.destroy()

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