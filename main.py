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
        
        # Indian classical music notes (Sargam) - Based on Sa = 130 Hz
        self.sa_base = 130.0
        self.indian_notes = [
            {'name': 'Sa', 'ratio': 1/1, 'freq': 130.00},
            {'name': 'Re', 'ratio': 9/8, 'freq': 146.25},
            {'name': 'Ga', 'ratio': 5/4, 'freq': 162.50},
            {'name': 'Ma', 'ratio': 4/3, 'freq': 173.33},
            {'name': 'Pa', 'ratio': 3/2, 'freq': 195.00},
            {'name': 'Dha', 'ratio': 5/3, 'freq': 216.67},
            {'name': 'Ni', 'ratio': 15/8, 'freq': 243.75},
            {'name': 'Sa\'', 'ratio': 2/1, 'freq': 260.00}
        ]
        
        # Tolerance for note detection (in cents)
        self.indian_note_tolerance = 25  # cents
        self.active_indian_notes = set()
        self.note_hold_counter = {}  # Track how long each note is held
        # Helper for sargam names and hold behavior
        self.sargam_names = [n['name'] for n in self.indian_notes]
        self.last_match_time = {n: 0.0 for n in self.sargam_names}
        self.note_hold_time = 0.9  # seconds to keep a note highlighted after being hit
        
        # Data storage
        self.freq_history = deque(maxlen=150)
        self.note_history = deque(maxlen=150)
        self.match_history = deque(maxlen=150)
        self.audio_queue = queue.Queue()
        
        # PyAudio setup
        self.p = pyaudio.PyAudio()
        self.stream = None
        
        self.setup_ui()
        
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
        
        subtitle = tk.Label(title_frame, text="Real-time Frequency & Note Detection", 
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
        
        self.calibrate_btn = tk.Button(left_panel, text="🎯 CALIBRATE", command=self.calibrate,
                                       bg=self.accent, fg="black", font=("Arial", 12, "bold"),
                                       relief=tk.FLAT, cursor="hand2", width=15, height=2)
        self.calibrate_btn.pack(pady=5, padx=20)
        
        # Calibration status
        self.calib_status = tk.Label(left_panel, text="⚠ Not Calibrated", 
                                    font=("Arial", 10), fg=self.warning, bg=self.bg_medium)
        self.calib_status.pack(pady=10)
        
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

        # Sa base control
        tk.Label(left_panel, text="Base Sa Frequency (Hz)", font=("Arial", 10),
            fg=self.text_color, bg=self.bg_medium).pack(pady=(12, 0))
        self.sa_var = tk.DoubleVar(value=self.sa_base)
        self.sa_entry = tk.Entry(left_panel, textvariable=self.sa_var, width=10)
        self.sa_entry.pack(pady=5, padx=20)
        self.apply_sa_btn = tk.Button(left_panel, text="Apply Sa Base", command=self.apply_sa_base,
                          bg=self.accent2, fg="black", font=("Arial", 10, "bold"))
        self.apply_sa_btn.pack(pady=5)
        
        # Info panel
        info_frame = tk.Frame(left_panel, bg=self.bg_light, relief=tk.SUNKEN, bd=1)
        info_frame.pack(pady=20, padx=20, fill=tk.X)
        
        tk.Label(info_frame, text="ℹ INFO", font=("Arial", 10, "bold"), 
                fg=self.accent, bg=self.bg_light).pack(pady=5)
        tk.Label(info_frame, text="1. Click START\n2. Sing a note\n3. Watch real-time analysis\n4. Calibrate for accuracy", 
                font=("Arial", 9), fg=self.text_color, bg=self.bg_light, justify=tk.LEFT).pack(pady=5, padx=10)
        
        # Right panel - Display
        right_panel = tk.Frame(main_frame, bg=self.bg_medium)
        right_panel.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
        
        # Current note display (large)
        note_frame = tk.Frame(right_panel, bg=self.bg_dark, relief=tk.RAISED, bd=3)
        note_frame.pack(fill=tk.X, padx=10, pady=10)
        
        tk.Label(note_frame, text="DETECTED NOTE", font=("Arial", 12), 
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
        
        # Cents deviation
        cents_frame = tk.Frame(right_panel, bg=self.bg_light, relief=tk.RAISED, bd=2)
        cents_frame.pack(fill=tk.X, padx=10, pady=5)
        
        tk.Label(cents_frame, text="CENTS FROM NOTE", font=("Arial", 11), 
                fg=self.accent, bg=self.bg_light).pack(side=tk.LEFT, padx=20, pady=10)
        
        self.cents_label = tk.Label(cents_frame, text="0", font=("Arial", 24, "bold"),
                                    fg=self.text_color, bg=self.bg_light)
        self.cents_label.pack(side=tk.RIGHT, padx=20, pady=10)
        
        # Sargam (Indian notes) display
        sargam_frame = tk.Frame(right_panel, bg=self.bg_dark)
        sargam_frame.pack(fill=tk.X, padx=10, pady=(5, 0))
        tk.Label(sargam_frame, text="S A R G A M", font=("Arial", 10, "bold"),
                 fg=self.accent, bg=self.bg_dark).pack(anchor=tk.W, padx=5)
        self.sargam_labels = {}
        notes_frame = tk.Frame(sargam_frame, bg=self.bg_dark)
        notes_frame.pack(fill=tk.X, padx=5, pady=(4,8))
        for n in self.indian_notes:
            lbl = tk.Label(notes_frame, text=f"{n['name']}\n{n['freq']:.2f} Hz", font=("Arial", 10, "bold"),
                           fg=self.text_color, bg=self.bg_dark, width=12, height=2, relief=tk.FLAT)
            lbl.pack(side=tk.LEFT, padx=4)
            self.sargam_labels[n['name']] = lbl
        
        # Graph canvas
        graph_frame = tk.Frame(right_panel, bg=self.bg_dark, relief=tk.SUNKEN, bd=2)
        graph_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        tk.Label(graph_frame, text="FREQUENCY HISTORY", font=("Arial", 12), 
                fg=self.accent, bg=self.bg_dark).pack(pady=5)
        
        self.canvas = tk.Canvas(graph_frame, bg="#0a0a15", highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Status bar
        self.status_bar = tk.Label(self.root, text="Ready to start", 
                                   font=("Arial", 9), fg=self.text_color, 
                                   bg=self.bg_light, anchor=tk.W, relief=tk.SUNKEN)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
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
        
        # Apply calibration offset
        frequency += self.calibration_offset
        
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
                    
                    if 50 < freq < 2000:  # Valid vocal range
                        self.freq_history.append(freq)
                        note, cents, target_freq = self.freq_to_note(freq)
                        self.note_history.append(note)
                        
                        # Update labels
                        self.freq_label.config(text=f"{freq:.2f} Hz")
                        self.note_label.config(text=note)
                        self.cents_label.config(text=f"{cents:+.0f}")
                        
                        # Color code cents deviation
                        if abs(cents) < 10:
                            self.cents_label.config(fg=self.success)
                        elif abs(cents) < 25:
                            self.cents_label.config(fg=self.warning)
                        else:
                            self.cents_label.config(fg="#ff4444")
                        
                        self.status_bar.config(text=f"Analyzing... Note: {note} | Frequency: {freq:.2f} Hz | Cents: {cents:+.1f}")
                        # Check Indian note matches and update match history
                        matched = self.check_indian_notes(freq)
                        now = time.time()
                        if matched:
                            # record last match time for hold behavior
                            self.last_match_time[matched] = now
                            self.match_history.append(True)
                        else:
                            self.match_history.append(False)

                        # update sargam labels color based on recent matches
                        for n in self.sargam_names:
                            lbl = self.sargam_labels.get(n)
                            if lbl is None:
                                continue
                            if now - self.last_match_time.get(n, 0.0) < self.note_hold_time:
                                lbl.config(fg=self.success)
                            else:
                                lbl.config(fg=self.text_color)

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
        """Apply new Sa base frequency and update displayed sargam frequencies"""
        try:
            val = float(self.sa_var.get())
            if val <= 0:
                raise ValueError('Sa must be > 0')
            self.sa_base = val
            # update indian notes frequencies
            for n in self.indian_notes:
                n['freq'] = self.sa_base * n['ratio']
            # update labels
            for n in self.indian_notes:
                lbl = self.sargam_labels.get(n['name'])
                if lbl:
                    lbl.config(text=f"{n['name']}\n{n['freq']:.2f} Hz")
            messagebox.showinfo('Sa Updated', f'Sa base set to {self.sa_base:.2f} Hz')
        except Exception as e:
            messagebox.showerror('Invalid value', f'Please enter a valid Sa frequency.\n{e}')

    def check_indian_notes(self, freq: float):
        """Return the name of an Indian note if freq is within tolerance, else None."""
        if freq is None or freq <= 0:
            return None
        for n in self.indian_notes:
            target = n['freq']
            # cents difference
            cents = 1200 * np.log2(freq / target)
            if abs(cents) <= self.indian_note_tolerance:
                return n['name']
        return None
        
    def calibrate(self):
        """Calibrate the analyzer"""
        if not self.running:
            messagebox.showwarning("Calibration", "Please start the analyzer first, then sing a reference note (e.g., A4 = 440 Hz).")
            return
        
        dialog = tk.Toplevel(self.root)
        dialog.title("Calibration")
        dialog.geometry("400x250")
        dialog.configure(bg=self.bg_medium)
        dialog.transient(self.root)
        dialog.grab_set()
        
        tk.Label(dialog, text="🎯 CALIBRATION", font=("Arial", 16, "bold"),
                fg=self.accent, bg=self.bg_medium).pack(pady=20)
        
        tk.Label(dialog, text="Sing a reference note (e.g., A4 = 440 Hz)\nfor 3 seconds", 
                font=("Arial", 11), fg=self.text_color, bg=self.bg_medium).pack(pady=10)
        
        freq_display = tk.Label(dialog, text="Measuring...", font=("Arial", 14, "bold"),
                               fg=self.success, bg=self.bg_medium)
        freq_display.pack(pady=10)
        
        def measure():
            samples = []
            for _ in range(30):  # 3 seconds worth of samples
                if not self.audio_queue.empty():
                    audio_data = self.audio_queue.get()
                    rms = np.sqrt(np.mean(audio_data**2))
                    if rms > self.sensitivity_var.get():
                        freq = self.detect_pitch(audio_data)
                        if 50 < freq < 2000:
                            samples.append(freq)
                dialog.after(100)
            
            if samples:
                avg_freq = np.median(samples)
                freq_display.config(text=f"Measured: {avg_freq:.2f} Hz")
                
                # Ask for reference frequency
                ref_frame = tk.Frame(dialog, bg=self.bg_medium)
                ref_frame.pack(pady=10)
                
                tk.Label(ref_frame, text="Reference frequency:", 
                        fg=self.text_color, bg=self.bg_medium).pack(side=tk.LEFT, padx=5)
                ref_entry = tk.Entry(ref_frame, width=10)
                ref_entry.insert(0, "440")
                ref_entry.pack(side=tk.LEFT, padx=5)
                
                def apply_calibration():
                    try:
                        ref_freq = float(ref_entry.get())
                        self.calibration_offset = ref_freq - avg_freq
                        self.calibrated = True
                        self.calib_status.config(text="✓ Calibrated", fg=self.success)
                        messagebox.showinfo("Success", f"Calibration applied!\nOffset: {self.calibration_offset:+.2f} Hz")
                        dialog.destroy()
                    except ValueError:
                        messagebox.showerror("Error", "Invalid frequency value")
                
                tk.Button(dialog, text="Apply", command=apply_calibration,
                         bg=self.success, fg="black", font=("Arial", 10, "bold")).pack(pady=10)
        
        dialog.after(100, measure)
        
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
        # User pressed Ctrl+C in terminal — ensure audio is closed cleanly
        try:
            app.on_closing()
        except Exception:
            pass
        sys.exit(0)