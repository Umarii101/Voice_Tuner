import tkinter as tk
from tkinter import ttk, messagebox
import numpy as np
import pyaudio
import threading
import queue
import time
from scipy import signal
from scipy.fft import rfft, rfftfreq
from collections import deque
import sys

class ModernSargamStudio:
    def __init__(self, root):
        self.root = root
        self.root.title("Sargam Learning Studio")
        self.root.geometry("1400x900")
        
        # Modern color palette
        self.colors = {
            'bg_primary': '#0a0e27',
            'bg_secondary': '#151932',
            'bg_tertiary': '#1e2444',
            'accent_primary': '#00f5ff',
            'accent_secondary': '#b721ff',
            'success': '#00ff9d',
            'warning': '#ffd700',
            'error': '#ff4757',
            'text_primary': '#ffffff',
            'text_secondary': '#8892b0',
            'graph_bg': '#0d1117',
            'graph_grid': '#1f2937'
        }
        
        self.root.configure(bg=self.colors['bg_primary'])
        
        # Audio parameters
        self.CHUNK = 4096
        self.FORMAT = pyaudio.paFloat32
        self.CHANNELS = 1
        self.RATE = 44100
        self.running = False
        
        # Enhanced pitch detection parameters
        self.min_confidence = 0.15  # Minimum confidence for pitch detection
        self.pitch_smoothing = 5  # Number of samples for smoothing
        self.note_stability_threshold = 3  # Frames a note must be stable to register
        
        # Sargam configuration - Using Sa = 261.63 Hz (Middle C) as default
        self.sa_base = 261.63
        self.sargam_notes = [
            {'name': 'Sa', 'ratio': 1.0, 'color': '#ff6b6b'},
            {'name': 'Re komal', 'ratio': 256/243, 'color': '#feca57'},
            {'name': 'Re', 'ratio': 9/8, 'color': '#48dbfb'},
            {'name': 'Ga komal', 'ratio': 32/27, 'color': '#00d2d3'},
            {'name': 'Ga', 'ratio': 5/4, 'color': '#1dd1a1'},
            {'name': 'Ma', 'ratio': 4/3, 'color': '#10ac84'},
            {'name': 'Ma tivra', 'ratio': 45/32, 'color': '#54a0ff'},
            {'name': 'Pa', 'ratio': 3/2, 'color': '#5f27cd'},
            {'name': 'Dha komal', 'ratio': 128/81, 'color': '#c23616'},
            {'name': 'Dha', 'ratio': 5/3, 'color': '#e056fd'},
            {'name': 'Ni komal', 'ratio': 16/9, 'color': '#ee5a6f'},
            {'name': 'Ni', 'ratio': 15/8, 'color': '#f368e0'},
        ]
        self.update_sargam_frequencies()
        
        # Detection tolerance (in cents)
        self.cents_tolerance = 30
        
        # Data storage
        self.pitch_buffer = deque(maxlen=self.pitch_smoothing)
        self.confidence_buffer = deque(maxlen=self.pitch_smoothing)
        self.freq_history = deque(maxlen=200)
        self.note_stability_counter = {}
        self.current_detected_note = None
        self.last_stable_note = None
        self.note_hit_times = {n['name']: 0 for n in self.sargam_notes}
        
        # Audio queue
        self.audio_queue = queue.Queue(maxsize=10)
        
        # PyAudio setup
        self.p = pyaudio.PyAudio()
        self.stream = None
        
        # Build UI
        self.setup_modern_ui()
        
        # Apply custom styles
        self.setup_styles()
        
    def update_sargam_frequencies(self):
        """Update all sargam frequencies based on Sa"""
        for note in self.sargam_notes:
            note['freq'] = self.sa_base * note['ratio']
    
    def setup_styles(self):
        """Setup ttk styles for modern look"""
        style = ttk.Style()
        style.theme_use('clam')
        
        # Configure button style
        style.configure('Modern.TButton',
                       background=self.colors['accent_primary'],
                       foreground='black',
                       borderwidth=0,
                       focuscolor='none',
                       font=('Segoe UI', 11, 'bold'))
        
        style.map('Modern.TButton',
                 background=[('active', self.colors['accent_secondary'])])
        
    def setup_modern_ui(self):
        """Create modern UI layout"""
        # Header
        self.create_header()
        
        # Main content area
        main_container = tk.Frame(self.root, bg=self.colors['bg_primary'])
        main_container.pack(fill=tk.BOTH, expand=True, padx=20, pady=(0, 20))
        
        # Left panel - Controls
        left_panel = tk.Frame(main_container, bg=self.colors['bg_secondary'], 
                             width=320, relief=tk.FLAT, bd=0)
        left_panel.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 15))
        left_panel.pack_propagate(False)
        
        self.create_control_panel(left_panel)
        
        # Right panel - Visualization
        right_panel = tk.Frame(main_container, bg=self.colors['bg_secondary'])
        right_panel.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        self.create_visualization_panel(right_panel)
        
        # Status bar
        self.create_status_bar()
        
    def create_header(self):
        """Create header section"""
        header = tk.Frame(self.root, bg=self.colors['bg_secondary'], height=100)
        header.pack(fill=tk.X, padx=20, pady=(20, 15))
        
        # Title with gradient effect simulation
        title_frame = tk.Frame(header, bg=self.colors['bg_secondary'])
        title_frame.pack(expand=True)
        
        tk.Label(title_frame, text="🎵 SARGAM", 
                font=('Segoe UI', 36, 'bold'),
                fg=self.colors['accent_primary'],
                bg=self.colors['bg_secondary']).pack()
        
        tk.Label(title_frame, text="Learning Studio", 
                font=('Segoe UI', 16),
                fg=self.colors['text_secondary'],
                bg=self.colors['bg_secondary']).pack()
        
    def create_control_panel(self, parent):
        """Create control panel"""
        # Control buttons section
        control_section = tk.Frame(parent, bg=self.colors['bg_secondary'])
        control_section.pack(fill=tk.X, padx=20, pady=20)
        
        tk.Label(control_section, text="CONTROLS",
                font=('Segoe UI', 12, 'bold'),
                fg=self.colors['accent_primary'],
                bg=self.colors['bg_secondary']).pack(anchor=tk.W, pady=(0, 15))
        
        # Start button
        self.start_btn = tk.Button(control_section, text="▶  START LISTENING",
                                   command=self.start_analysis,
                                   bg=self.colors['success'],
                                   fg='black',
                                   font=('Segoe UI', 11, 'bold'),
                                   relief=tk.FLAT,
                                   cursor='hand2',
                                   height=2)
        self.start_btn.pack(fill=tk.X, pady=5)
        
        # Stop button
        self.stop_btn = tk.Button(control_section, text="⏸  STOP",
                                  command=self.stop_analysis,
                                  bg=self.colors['error'],
                                  fg='white',
                                  font=('Segoe UI', 11, 'bold'),
                                  relief=tk.FLAT,
                                  cursor='hand2',
                                  height=2,
                                  state=tk.DISABLED)
        self.stop_btn.pack(fill=tk.X, pady=5)
        
        # Settings section
        settings_section = tk.Frame(parent, bg=self.colors['bg_tertiary'])
        settings_section.pack(fill=tk.X, padx=20, pady=20)
        
        tk.Label(settings_section, text="SETTINGS",
                font=('Segoe UI', 12, 'bold'),
                fg=self.colors['accent_primary'],
                bg=self.colors['bg_tertiary']).pack(anchor=tk.W, padx=15, pady=(15, 10))
        
        # Sa base frequency
        sa_frame = tk.Frame(settings_section, bg=self.colors['bg_tertiary'])
        sa_frame.pack(fill=tk.X, padx=15, pady=10)
        
        tk.Label(sa_frame, text="Base Sa (Hz):",
                font=('Segoe UI', 10),
                fg=self.colors['text_secondary'],
                bg=self.colors['bg_tertiary']).pack(anchor=tk.W)
        
        entry_frame = tk.Frame(sa_frame, bg=self.colors['bg_tertiary'])
        entry_frame.pack(fill=tk.X, pady=5)
        
        self.sa_var = tk.StringVar(value=str(self.sa_base))
        sa_entry = tk.Entry(entry_frame, textvariable=self.sa_var,
                           font=('Segoe UI', 11),
                           bg=self.colors['bg_primary'],
                           fg=self.colors['text_primary'],
                           insertbackground=self.colors['accent_primary'],
                           relief=tk.FLAT,
                           justify=tk.CENTER)
        sa_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, ipady=8)
        
        tk.Button(entry_frame, text="Apply",
                 command=self.apply_sa_base,
                 bg=self.colors['accent_secondary'],
                 fg='white',
                 font=('Segoe UI', 9, 'bold'),
                 relief=tk.FLAT,
                 cursor='hand2',
                 padx=15).pack(side=tk.LEFT, padx=(5, 0))
        
        # Sensitivity
        sens_frame = tk.Frame(settings_section, bg=self.colors['bg_tertiary'])
        sens_frame.pack(fill=tk.X, padx=15, pady=10)
        
        tk.Label(sens_frame, text="Sensitivity:",
                font=('Segoe UI', 10),
                fg=self.colors['text_secondary'],
                bg=self.colors['bg_tertiary']).pack(anchor=tk.W)
        
        self.sensitivity_var = tk.DoubleVar(value=self.min_confidence)
        self.sensitivity_scale = tk.Scale(sens_frame,
                                         from_=0.05, to=0.5,
                                         resolution=0.01,
                                         orient=tk.HORIZONTAL,
                                         variable=self.sensitivity_var,
                                         bg=self.colors['bg_tertiary'],
                                         fg=self.colors['text_primary'],
                                         highlightthickness=0,
                                         troughcolor=self.colors['bg_primary'],
                                         activebackground=self.colors['accent_primary'],
                                         command=self.update_sensitivity)
        self.sensitivity_scale.pack(fill=tk.X, pady=5)
        
        # Tolerance
        tol_frame = tk.Frame(settings_section, bg=self.colors['bg_tertiary'])
        tol_frame.pack(fill=tk.X, padx=15, pady=(10, 15))
        
        tk.Label(tol_frame, text="Note Tolerance (cents):",
                font=('Segoe UI', 10),
                fg=self.colors['text_secondary'],
                bg=self.colors['bg_tertiary']).pack(anchor=tk.W)
        
        self.tolerance_var = tk.DoubleVar(value=self.cents_tolerance)
        self.tolerance_scale = tk.Scale(tol_frame,
                                       from_=10, to=50,
                                       resolution=5,
                                       orient=tk.HORIZONTAL,
                                       variable=self.tolerance_var,
                                       bg=self.colors['bg_tertiary'],
                                       fg=self.colors['text_primary'],
                                       highlightthickness=0,
                                       troughcolor=self.colors['bg_primary'],
                                       activebackground=self.colors['accent_primary'],
                                       command=self.update_tolerance)
        self.tolerance_scale.pack(fill=tk.X, pady=5)
        
        # Info section
        info_section = tk.Frame(parent, bg=self.colors['bg_tertiary'])
        info_section.pack(fill=tk.X, padx=20, pady=20)
        
        tk.Label(info_section, text="ℹ  TIPS",
                font=('Segoe UI', 11, 'bold'),
                fg=self.colors['accent_primary'],
                bg=self.colors['bg_tertiary']).pack(anchor=tk.W, padx=15, pady=(15, 10))
        
        tips = [
            "• Sing clearly and steadily",
            "• Avoid background noise",
            "• Hold notes for 1-2 seconds",
            "• Adjust Sa to match your range",
            "• Lower sensitivity if too reactive"
        ]
        
        for tip in tips:
            tk.Label(info_section, text=tip,
                    font=('Segoe UI', 9),
                    fg=self.colors['text_secondary'],
                    bg=self.colors['bg_tertiary'],
                    justify=tk.LEFT).pack(anchor=tk.W, padx=15, pady=2)
        
        tk.Label(info_section, text="",
                bg=self.colors['bg_tertiary']).pack(pady=5)
        
    def create_visualization_panel(self, parent):
        """Create visualization panel"""
        # Current note display
        note_display = tk.Frame(parent, bg=self.colors['bg_tertiary'], height=180)
        note_display.pack(fill=tk.X, padx=15, pady=15)
        note_display.pack_propagate(False)
        
        tk.Label(note_display, text="DETECTED NOTE",
                font=('Segoe UI', 11),
                fg=self.colors['text_secondary'],
                bg=self.colors['bg_tertiary']).pack(pady=(15, 5))
        
        self.note_display_label = tk.Label(note_display, text="--",
                                          font=('Segoe UI', 56, 'bold'),
                                          fg=self.colors['accent_primary'],
                                          bg=self.colors['bg_tertiary'])
        self.note_display_label.pack(pady=10)
        
        # Frequency and cents display
        info_row = tk.Frame(note_display, bg=self.colors['bg_tertiary'])
        info_row.pack(fill=tk.X, padx=20)
        
        freq_frame = tk.Frame(info_row, bg=self.colors['bg_primary'])
        freq_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
        
        tk.Label(freq_frame, text="Frequency",
                font=('Segoe UI', 9),
                fg=self.colors['text_secondary'],
                bg=self.colors['bg_primary']).pack(pady=(8, 0))
        
        self.freq_value_label = tk.Label(freq_frame, text="0 Hz",
                                         font=('Segoe UI', 16, 'bold'),
                                         fg=self.colors['text_primary'],
                                         bg=self.colors['bg_primary'])
        self.freq_value_label.pack(pady=(0, 8))
        
        cents_frame = tk.Frame(info_row, bg=self.colors['bg_primary'])
        cents_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
        
        tk.Label(cents_frame, text="Cents Off",
                font=('Segoe UI', 9),
                fg=self.colors['text_secondary'],
                bg=self.colors['bg_primary']).pack(pady=(8, 0))
        
        self.cents_value_label = tk.Label(cents_frame, text="0",
                                          font=('Segoe UI', 16, 'bold'),
                                          fg=self.colors['text_primary'],
                                          bg=self.colors['bg_primary'])
        self.cents_value_label.pack(pady=(0, 8))
        
        # Sargam note grid
        sargam_container = tk.Frame(parent, bg=self.colors['bg_tertiary'])
        sargam_container.pack(fill=tk.X, padx=15, pady=(0, 15))
        
        tk.Label(sargam_container, text="SARGAM NOTES",
                font=('Segoe UI', 11),
                fg=self.colors['text_secondary'],
                bg=self.colors['bg_tertiary']).pack(anchor=tk.W, padx=15, pady=(15, 10))
        
        # Create grid
        self.sargam_labels = {}
        notes_grid = tk.Frame(sargam_container, bg=self.colors['bg_tertiary'])
        notes_grid.pack(fill=tk.X, padx=15, pady=(0, 15))
        
        # 4 notes per row
        for i, note in enumerate(self.sargam_notes):
            row = i // 4
            col = i % 4
            
            note_frame = tk.Frame(notes_grid, bg=self.colors['bg_primary'],
                                 relief=tk.FLAT, bd=0)
            note_frame.grid(row=row, column=col, padx=5, pady=5, sticky='ew')
            
            name_label = tk.Label(note_frame, text=note['name'],
                                 font=('Segoe UI', 11, 'bold'),
                                 fg=self.colors['text_primary'],
                                 bg=self.colors['bg_primary'])
            name_label.pack(pady=(10, 2))
            
            freq_label = tk.Label(note_frame, text=f"{note['freq']:.1f} Hz",
                                 font=('Segoe UI', 9),
                                 fg=self.colors['text_secondary'],
                                 bg=self.colors['bg_primary'])
            freq_label.pack(pady=(0, 10))
            
            self.sargam_labels[note['name']] = {
                'frame': note_frame,
                'name': name_label,
                'freq': freq_label,
                'color': note['color']
            }
        
        for col in range(4):
            notes_grid.columnconfigure(col, weight=1)
        
        # Graph
        graph_container = tk.Frame(parent, bg=self.colors['bg_tertiary'])
        graph_container.pack(fill=tk.BOTH, expand=True, padx=15, pady=(0, 15))
        
        tk.Label(graph_container, text="PITCH HISTORY",
                font=('Segoe UI', 11),
                fg=self.colors['text_secondary'],
                bg=self.colors['bg_tertiary']).pack(anchor=tk.W, padx=15, pady=(15, 5))
        
        self.canvas = tk.Canvas(graph_container,
                               bg=self.colors['graph_bg'],
                               highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True, padx=15, pady=(0, 15))
        
    def create_status_bar(self):
        """Create status bar"""
        self.status_bar = tk.Label(self.root, text="Ready • Adjust settings and press START",
                                  font=('Segoe UI', 9),
                                  fg=self.colors['text_secondary'],
                                  bg=self.colors['bg_secondary'],
                                  anchor=tk.W,
                                  padx=10,
                                  pady=8)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X, padx=20, pady=(0, 20))
        
    def update_sensitivity(self, val):
        """Update sensitivity"""
        self.min_confidence = float(val)
        
    def update_tolerance(self, val):
        """Update tolerance"""
        self.cents_tolerance = float(val)
        
    def apply_sa_base(self):
        """Apply new Sa base frequency"""
        try:
            new_sa = float(self.sa_var.get())
            if new_sa < 100 or new_sa > 500:
                raise ValueError("Sa frequency must be between 100-500 Hz")
            
            self.sa_base = new_sa
            self.update_sargam_frequencies()
            
            # Update UI
            for note in self.sargam_notes:
                label = self.sargam_labels[note['name']]
                label['freq'].config(text=f"{note['freq']:.1f} Hz")
            
            self.status_bar.config(text=f"✓ Sa base updated to {self.sa_base:.1f} Hz")
            
        except ValueError as e:
            messagebox.showerror("Invalid Input", str(e))
            self.sa_var.set(str(self.sa_base))
    
    def detect_pitch_yin(self, audio_data):
        """
        YIN algorithm for pitch detection - more accurate than autocorrelation
        Returns (frequency, confidence)
        """
        # Ensure we have enough data
        if len(audio_data) < self.CHUNK // 2:
            return 0, 0
        
        # Step 1: Calculate difference function
        tau_max = len(audio_data) // 2
        diff = np.zeros(tau_max)
        
        for tau in range(1, tau_max):
            for i in range(tau_max):
                delta = audio_data[i] - audio_data[i + tau]
                diff[tau] += delta * delta
        
        # Step 2: Cumulative mean normalized difference
        cmndf = np.ones(tau_max)
        cmndf[0] = 1
        
        cumsum = 0
        for tau in range(1, tau_max):
            cumsum += diff[tau]
            if cumsum != 0:
                cmndf[tau] = diff[tau] * tau / cumsum
            else:
                cmndf[tau] = 1
        
        # Step 3: Absolute threshold
        threshold = 0.1
        tau = 1
        
        while tau < tau_max:
            if cmndf[tau] < threshold:
                while tau + 1 < tau_max and cmndf[tau + 1] < cmndf[tau]:
                    tau += 1
                break
            tau += 1
        
        if tau >= tau_max - 1:
            return 0, 0
        
        # Step 4: Parabolic interpolation
        if tau > 0 and tau < tau_max - 1:
            s0 = cmndf[tau - 1]
            s1 = cmndf[tau]
            s2 = cmndf[tau + 1]
            
            adjustment = (s2 - s0) / (2 * (2 * s1 - s2 - s0))
            tau_best = tau + adjustment
        else:
            tau_best = tau
        
        frequency = self.RATE / tau_best
        confidence = 1 - cmndf[tau]
        
        return frequency, confidence
    
    def detect_pitch_fft(self, audio_data):
        """
        FFT-based pitch detection as fallback
        Returns (frequency, confidence)
        """
        # Apply window
        windowed = audio_data * np.hanning(len(audio_data))
        
        # Compute FFT
        fft_data = rfft(windowed)
        fft_freqs = rfftfreq(len(windowed), 1/self.RATE)
        
        # Get magnitude
        magnitude = np.abs(fft_data)
        
        # Find peak in vocal range (80-1000 Hz)
        vocal_range = (fft_freqs >= 80) & (fft_freqs <= 1000)
        if not np.any(vocal_range):
            return 0, 0
        
        vocal_magnitudes = magnitude[vocal_range]
        vocal_freqs = fft_freqs[vocal_range]
        
        if len(vocal_magnitudes) == 0:
            return 0, 0
        
        peak_idx = np.argmax(vocal_magnitudes)
        frequency = vocal_freqs[peak_idx]
        
        # Calculate confidence based on peak prominence
        mean_mag = np.mean(vocal_magnitudes)
        peak_mag = vocal_magnitudes[peak_idx]
        
        if mean_mag > 0:
            confidence = min(1.0, (peak_mag - mean_mag) / mean_mag * 0.1)
        else:
            confidence = 0
        
        return frequency, confidence
    
    def find_closest_sargam(self, freq):
        """
        Find the closest sargam note to the given frequency
        Returns (note_name, cents_off, target_freq) or None
        """
        if freq < 50 or freq > 2000:
            return None
        
        min_cents = float('inf')
        closest_note = None
        
        for note in self.sargam_notes:
            target_freq = note['freq']
            cents = 1200 * np.log2(freq / target_freq)
            
            if abs(cents) < abs(min_cents):
                min_cents = cents
                closest_note = note
        
        if closest_note and abs(min_cents) <= self.cents_tolerance:
            return closest_note['name'], min_cents, closest_note['freq']
        
        return None
    
    def audio_callback(self):
        """Continuous audio capture"""
        while self.running:
            try:
                data = self.stream.read(self.CHUNK, exception_on_overflow=False)
                audio_data = np.frombuffer(data, dtype=np.float32)
                
                # Only add to queue if not full (prevent lag)
                if not self.audio_queue.full():
                    self.audio_queue.put(audio_data)
                    
            except Exception as e:
                print(f"Audio error: {e}")
                break
    
    def process_audio(self):
        """Process audio and update UI"""
        if not self.running:
            return
        
        try:
            if not self.audio_queue.empty():
                audio_data = self.audio_queue.get()
                
                # Check signal strength
                rms = np.sqrt(np.mean(audio_data**2))
                
                if rms > 0.001:  # Minimum signal threshold
                    # Try YIN first (more accurate)
                    freq, confidence = self.detect_pitch_yin(audio_data)
                    
                    # If YIN confidence is low, try FFT
                    if confidence < 0.5:
                        freq_fft, conf_fft = self.detect_pitch_fft(audio_data)
                        if conf_fft > confidence:
                            freq, confidence = freq_fft, conf_fft
                    
                    # Add to buffers for smoothing
                    if confidence >= self.min_confidence and 80 < freq < 1000:
                        self.pitch_buffer.append(freq)
                        self.confidence_buffer.append(confidence)
                        
                        # Use median for smoothing (robust to outliers)
                        if len(self.pitch_buffer) >= 3:
                            smooth_freq = np.median(list(self.pitch_buffer))
                            smooth_conf = np.mean(list(self.confidence_buffer))
                            
                            self.freq_history.append(smooth_freq)
                            
                            # Update frequency display
                            self.freq_value_label.config(text=f"{smooth_freq:.1f} Hz")
                            
                            # Find matching sargam
                            match = self.find_closest_sargam(smooth_freq)
                            
                            if match:
                                note_name, cents_off, target_freq = match
                                
                                # Update note stability counter
                                if note_name not in self.note_stability_counter:
                                    self.note_stability_counter[note_name] = 0
                                
                                self.note_stability_counter[note_name] += 1
                                
                                # Clear other counters
                                for key in list(self.note_stability_counter.keys()):
                                    if key != note_name:
                                        self.note_stability_counter[key] = max(0, self.note_stability_counter[key] - 1)
                                
                                # Only register note if stable
                                if self.note_stability_counter[note_name] >= self.note_stability_threshold:
                                    self.current_detected_note = note_name
                                    self.last_stable_note = note_name
                                    self.note_hit_times[note_name] = time.time()
                                    
                                    # Update display
                                    self.note_display_label.config(text=note_name)
                                    self.cents_value_label.config(text=f"{cents_off:+.0f}")
                                    
                                    # Color code cents
                                    if abs(cents_off) < 10:
                                        self.cents_value_label.config(fg=self.colors['success'])
                                    elif abs(cents_off) < 20:
                                        self.cents_value_label.config(fg=self.colors['warning'])
                                    else:
                                        self.cents_value_label.config(fg=self.colors['error'])
                            else:
                                self.current_detected_note = None
                                self.note_display_label.config(text="--")
                                self.cents_value_label.config(text="0")
                    else:
                        # No clear pitch detected
                        if len(self.freq_history) > 0:
                            self.freq_history.append(self.freq