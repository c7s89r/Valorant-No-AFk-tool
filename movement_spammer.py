"""
nzv's macro  —  nzv @c7s89r
============================
Uses Windows RegisterHotKey (ctypes) for instant hotkey response in any game.
S -> W -> A -> D  — all equal hold times
"""

import tkinter as tk
from tkinter import font as tkfont
import threading
import time
import math
import ctypes
import ctypes.wintypes

user32 = ctypes.windll.user32

# ── COMPLETE Windows Virtual Key map ─────────────────────────────────────────
VK_MAP = {
    # letters
    **{c: ord(c.upper()) for c in "abcdefghijklmnopqrstuvwxyz"},

    # top row numbers
    "0": 0x30, "1": 0x31, "2": 0x32, "3": 0x33, "4": 0x34,
    "5": 0x35, "6": 0x36, "7": 0x37, "8": 0x38, "9": 0x39,

    # f1-f24
    **{f"f{i}": 0x6F + i for i in range(1, 25)},

    # numpad digits
    **{f"num {i}": 0x60 + i for i in range(10)},
    # numpad alternate names
    **{f"numpad {i}": 0x60 + i for i in range(10)},

    # numpad operators
    "num *":        0x6A, "numpad *":    0x6A,
    "num +":        0x6B, "numpad +":    0x6B,
    "num -":        0x6D, "numpad -":    0x6D,
    "num .":        0x6E, "numpad .":    0x6E,
    "num /":        0x6F, "numpad /":    0x6F,
    "num lock":     0x90,

    # arrow keys
    "left":         0x25,
    "up":           0x26,
    "right":        0x27,
    "down":         0x28,

    # navigation cluster
    "home":         0x24,
    "end":          0x23,
    "page up":      0x21, "prior": 0x21,
    "page down":    0x22, "next":  0x22,
    "insert":       0x2D,
    "delete":       0x2E,

    # modifier keys (can be used as hotkey)
    "shift":        0x10,
    "ctrl":         0x11, "control": 0x11,
    "alt":          0x12,
    "left shift":   0xA0,
    "right shift":  0xA1,
    "left ctrl":    0xA2,
    "right ctrl":   0xA3,
    "left alt":     0xA4,
    "right alt":    0xA5,
    "left windows": 0x5B, "win": 0x5B,
    "right windows":0x5C,
    "apps":         0x5D,  # menu key

    # lock keys
    "caps lock":    0x14,
    "num lock":     0x90,
    "scroll lock":  0x91,

    # whitespace / control
    "backspace":    0x08,
    "tab":          0x09,
    "enter":        0x0D, "return": 0x0D,
    "escape":       0x1B, "esc": 0x1B,
    "space":        0x20,

    # system keys
    "print screen": 0x2C, "prtsc": 0x2C, "snapshot": 0x2C,
    "pause":        0x13,
    "break":        0x03,

    # punctuation / symbols (US layout)
    ";":            0xBA, "semicolon": 0xBA,
    "=":            0xBB, "equals": 0xBB,
    ",":            0xBC, "comma": 0xBC,
    "-":            0xBD, "minus": 0xBD,
    ".":            0xBE, "period": 0xBE,
    "/":            0xBF, "slash": 0xBF,
    "`":            0xC0, "grave": 0xC0, "backtick": 0xC0,
    "[":            0xDB,
    "\\":           0xDC, "backslash": 0xDC,
    "]":            0xDD,
    "'":            0xDE, "apostrophe": 0xDE, "quote": 0xDE,

    # media keys
    "volume mute":  0xAD,
    "volume down":  0xAE,
    "volume up":    0xAF,
    "media next":   0xB0,
    "media prev":   0xB1,
    "media stop":   0xB2,
    "media play":   0xB3, "media play/pause": 0xB3,

    # browser keys
    "browser back":    0xA6,
    "browser forward": 0xA7,
    "browser refresh": 0xA8,
    "browser stop":    0xA9,
    "browser search":  0xAA,
    "browser favorites": 0xAB,
    "browser home":    0xAC,
}

MOD_NOREPEAT = 0x4000
HOTKEY_ID    = 1

try:
    import pyautogui
    pyautogui.FAILSAFE = False
    LIBS_OK = True
except ImportError:
    LIBS_OK = False

try:
    import keyboard as _keyboard_lib
    KEYBOARD_LIB = True
except ImportError:
    KEYBOARD_LIB = False

HOLD    = 0.55
PATTERN = [("s", HOLD), ("w", HOLD), ("a", HOLD), ("d", HOLD)]

BG      = "#0a0a0f"
BG2     = "#111118"
BG3     = "#1a1a24"
ACCENT  = "#7c3aed"
ACCENT2 = "#a855f7"
GREEN   = "#22d3a0"
DIM     = "#3a3a4a"
WHITE   = "#e8e8f0"
MUTED   = "#55556a"


class MovementSpammer:
    def __init__(self, root):
        self.root = root
        self.root.title("nzv's macro")
        self.root.resizable(False, False)
        self.root.attributes("-topmost", True)
        self.root.configure(bg=BG)
        self.root.geometry("360x490")

        self.active           = False
        self.hotkey_vk        = None
        self.hotkey_name      = None
        self.listening        = False
        self.spam_thread      = None
        self._stop_event      = threading.Event()
        self._hotkey_thread   = None
        self._hotkey_stop     = threading.Event()

        self._orb_phase       = 0.0
        self._scan_y          = 0
        self._current_key_idx = -1
        self._key_flash       = [0.0, 0.0, 0.0, 0.0]
        self._title_offset    = 20
        self._title_done      = False
        self._credits_alpha   = 0.0

        self._build_ui()
        self._animate()
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    def _build_ui(self):
        tf  = tkfont.Font(family="Consolas", size=16, weight="bold")
        sf  = tkfont.Font(family="Consolas", size=8)
        bf  = tkfont.Font(family="Consolas", size=10, weight="bold")
        kf  = tkfont.Font(family="Consolas", size=20, weight="bold")
        stf = tkfont.Font(family="Consolas", size=11, weight="bold")
        cf  = tkfont.Font(family="Consolas", size=7)

        # header canvas
        self.header_canvas = tk.Canvas(self.root, width=360, height=80,
                                       bg=BG2, highlightthickness=0)
        self.header_canvas.pack(fill="x")
        self._scan_line = self.header_canvas.create_rectangle(
            0, 0, 360, 2, fill="#2a1a4a", outline="")
        self._title_txt = self.header_canvas.create_text(
            180, 100, text="nzv's macro", font=tf, fill=ACCENT2, anchor="center")
        self.header_canvas.create_text(
            180, 65, text="S  ->  W  ->  A  ->  D",
            font=sf, fill=DIM, anchor="center")

        # WASD visualiser
        vis_frame = tk.Frame(self.root, bg=BG)
        vis_frame.pack(fill="x", padx=20, pady=(12, 0))
        tk.Label(vis_frame, text="PATTERN", font=sf, fg=MUTED, bg=BG).pack(anchor="w")
        self.wasd_canvas = tk.Canvas(vis_frame, width=320, height=60,
                                     bg=BG, highlightthickness=0)
        self.wasd_canvas.pack(pady=(4, 0))
        self._wasd_boxes, self._wasd_labels = [], []
        for i, (lbl, x) in enumerate(zip(["S","W","A","D"], [30,110,190,270])):
            b = self.wasd_canvas.create_rectangle(x-28,8,x+28,52, fill=BG3, outline=DIM, width=1)
            t2 = self.wasd_canvas.create_text(x, 30, text=lbl, font=kf, fill=MUTED)
            self._wasd_boxes.append(b)
            self._wasd_labels.append(t2)

        tk.Frame(self.root, bg=BG3, height=1).pack(fill="x", padx=20, pady=10)

        # hotkey section
        hk_frame = tk.Frame(self.root, bg=BG)
        hk_frame.pack(fill="x", padx=20)
        tk.Label(hk_frame, text="TOGGLE HOTKEY", font=sf, fg=MUTED, bg=BG).pack(anchor="w")
        hk_row = tk.Frame(hk_frame, bg=BG)
        hk_row.pack(fill="x", pady=(6, 0))

        self.key_var = tk.StringVar(value="--")
        self.key_lbl = tk.Label(hk_row, textvariable=self.key_var,
                                font=kf, fg=WHITE, bg=BG3, width=6,
                                relief="flat", pady=10,
                                highlightbackground=DIM, highlightthickness=1)
        self.key_lbl.pack(side="left")

        self.set_btn = tk.Button(hk_row, text="SET KEY",
                                 font=bf, fg=BG, bg=ACCENT2,
                                 activebackground=ACCENT, activeforeground=WHITE,
                                 relief="flat", padx=14, pady=10,
                                 cursor="hand2", command=self._start_listening)
        self.set_btn.pack(side="left", padx=(10, 0))

        self.hint_var = tk.StringVar(value="")
        self.hint_lbl = tk.Label(hk_frame, textvariable=self.hint_var,
                                 font=sf, fg="#998800", bg=BG)
        self.hint_lbl.pack(anchor="w", pady=(5, 0))

        badge_frame = tk.Frame(self.root, bg=BG)
        badge_frame.pack(fill="x", padx=20, pady=(2, 0))
        tk.Label(badge_frame, text="  system-level hook  |  instant response in any game",
                 font=sf, fg="#1a3a1a", bg=BG).pack(anchor="w")

        tk.Frame(self.root, bg=BG3, height=1).pack(fill="x", padx=20, pady=10)

        # status orb
        st_frame = tk.Frame(self.root, bg=BG)
        st_frame.pack(fill="x", padx=20)
        self.orb_canvas = tk.Canvas(st_frame, width=18, height=18,
                                    bg=BG, highlightthickness=0)
        self.orb_canvas.pack(side="left")
        self._orb = self.orb_canvas.create_oval(2, 2, 16, 16, fill=DIM, outline="")
        self.status_var = tk.StringVar(value="IDLE")
        self.status_lbl = tk.Label(st_frame, textvariable=self.status_var,
                                   font=stf, fg=MUTED, bg=BG)
        self.status_lbl.pack(side="left", padx=(6, 0))

        if not LIBS_OK:
            tk.Label(self.root, text="  pip install pyautogui",
                     font=sf, fg="#ff5555", bg=BG).pack(pady=4)

        # credits
        credits_frame = tk.Frame(self.root, bg=BG)
        credits_frame.pack(side="bottom", fill="x", pady=(0, 10))
        self._credits_lbl = tk.Label(
            credits_frame, text="made by  nzv  @c7s89r",
            font=tkfont.Font(family="Consolas", size=8, slant="italic"),
            fg=BG, bg=BG)
        self._credits_lbl.pack()
        self._credits_dot = tk.Label(credits_frame, text=". . .",
                                     font=cf, fg=BG, bg=BG)
        self._credits_dot.pack()

    def _animate(self):
        t = time.time()

        self._scan_y = (self._scan_y + 2) % 80
        self.header_canvas.coords(self._scan_line, 0, self._scan_y, 360, self._scan_y+2)

        if not self._title_done:
            self._title_offset = max(40, self._title_offset - 2)
            self.header_canvas.coords(self._title_txt, 180, self._title_offset)
            if self._title_offset <= 40:
                self._title_done = True

        s = int(180 + 70 * math.sin(t * 2.1))
        self.header_canvas.itemconfig(self._title_txt, fill="#{:02x}{:02x}{:02x}".format(
            min(255, 120+s//3), min(255, 60+s//6), min(255, s)))

        self._orb_phase += 0.08
        if self.active:
            v = int(180 + 75 * math.sin(self._orb_phase * 3))
            oc = "#{:02x}{:02x}{:02x}".format(min(255,v//4), min(255,v), min(255,v//2))
        else:
            v = int(80 + 30 * math.sin(self._orb_phase))
            oc = "#{:02x}{:02x}{:02x}".format(v//3, v//3, v//2)
        self.orb_canvas.itemconfig(self._orb, fill=oc)

        for i in range(4):
            self._key_flash[i] = max(0.0, self._key_flash[i] - 0.08)
            if self.active and self._current_key_idx == i:
                self._key_flash[i] = min(1.0, self._key_flash[i] + 0.25)
            f = self._key_flash[i]
            self.wasd_canvas.itemconfig(self._wasd_boxes[i], fill="#{:02x}{:02x}{:02x}".format(
                int(0x1a+f*(0x7c-0x1a)), int(0x1a+f*(0x3a-0x1a)), int(0x24+f*(0xed-0x24))))
            self.wasd_canvas.itemconfig(self._wasd_labels[i], fill="#{:02x}{:02x}{:02x}".format(
                int(0x55+f*(0xe8-0x55)), int(0x55+f*(0xa0-0x55)), int(0x6a+f*(0xff-0x6a))))

        self._credits_alpha = min(1.0, self._credits_alpha + 0.012)
        cr = int(self._credits_alpha * 0x55)
        self._credits_lbl.config(fg="#{:02x}{:02x}{:02x}".format(cr, cr, int(min(255, cr*1.2))))
        da = int(self._credits_alpha * 0x30)
        self._credits_dot.config(fg="#{:02x}{:02x}{:02x}".format(da, da, da+0x10))

        if self.listening:
            p = int(180 + 75 * math.sin(t * 5))
            self.hint_lbl.config(fg="#{:02x}{:02x}00".format(p, p//2))

        self.root.after(30, self._animate)

    def _start_listening(self):
        if not LIBS_OK:
            self.hint_var.set("  install pyautogui first!")
            return
        if self.listening:
            return
        self._unregister_hotkey()
        self.listening = True
        self.hint_var.set("  press any key ...")
        self.key_var.set("?")
        self.set_btn.config(state="disabled", bg=DIM, fg=MUTED)
        threading.Thread(target=self._capture_key, daemon=True).start()

    def _capture_key(self):
        """
        Use the keyboard lib to read the keypress name,
        then look it up in VK_MAP. If not found, fall back
        to the raw scan code -> VK via MapVirtualKey so
        literally every key on the keyboard works.
        """
        key_name = None
        raw_vk   = None

        if KEYBOARD_LIB:
            try:
                event = _keyboard_lib.read_event(suppress=False)
                while event.event_type != "down":
                    event = _keyboard_lib.read_event(suppress=False)
                key_name = event.name.lower()
                # keyboard lib exposes the scan code; convert to VK as fallback
                sc = getattr(event, 'scan_code', None)
                if sc:
                    raw_vk = user32.MapVirtualKeyW(sc, 1)  # MAPVK_VSC_TO_VK=1
            except Exception:
                pass
        else:
            self.root.after(0, self._hint_fallback)
            return

        self.root.after(0, self._apply_key, key_name, raw_vk)

    def _hint_fallback(self):
        self.hint_var.set("  install 'keyboard' lib for key capture")
        self.listening = False
        self.set_btn.config(state="normal", bg=ACCENT2, fg=BG)

    def _apply_key(self, key_name, raw_vk=None):
        self.listening = False
        self.set_btn.config(state="normal", bg=ACCENT2, fg=BG)

        if not key_name and not raw_vk:
            self.hint_var.set("failed -- try again")
            self.key_var.set("--")
            return

        # 1) try named map
        vk = VK_MAP.get(key_name) if key_name else None

        # 2) fallback: MapVirtualKey from scan code (catches every key)
        if vk is None and raw_vk:
            vk = raw_vk

        # 3) last resort: ord() for single printable chars
        if vk is None and key_name and len(key_name) == 1:
            vk = user32.VkKeyScanW(ord(key_name)) & 0xFF

        if not vk:
            self.hint_var.set(f"couldn't map '{key_name}' -- try another")
            self.key_var.set("?")
            return

        self.hotkey_vk   = vk
        self.hotkey_name = key_name or f"vk{vk:#04x}"
        display = (key_name or f"VK{vk:#04x}").upper()
        # truncate long names for display
        if len(display) > 7:
            display = display[:6] + "."
        self.key_var.set(display)
        self.hint_var.set(f"press  {(key_name or '').upper()}  to toggle on/off")
        self._register_hotkey(vk)

    def _register_hotkey(self, vk):
        self._hotkey_stop.clear()
        self._hotkey_thread = threading.Thread(
            target=self._hotkey_message_pump, args=(vk,), daemon=True)
        self._hotkey_thread.start()

    def _unregister_hotkey(self):
        self._hotkey_stop.set()
        if self._hotkey_thread and self._hotkey_thread.is_alive():
            try:
                user32.PostThreadMessageW(
                    ctypes.c_uint(self._hotkey_thread.ident), 0x0012, 0, 0)
            except Exception:
                pass

    def _hotkey_message_pump(self, vk):
        hwnd = None
        ok = user32.RegisterHotKey(hwnd, HOTKEY_ID, MOD_NOREPEAT, vk)
        if not ok:
            self.root.after(0, lambda: self.hint_var.set(
                "key already in use by system -- try another"))
            return

        msg = ctypes.wintypes.MSG()
        while not self._hotkey_stop.is_set():
            ret = user32.PeekMessageW(ctypes.byref(msg), hwnd, 0, 0, 1)
            if ret:
                if msg.message == 0x0312:    # WM_HOTKEY
                    self.root.after(0, self._toggle)
                elif msg.message == 0x0012:  # WM_QUIT
                    break
            else:
                time.sleep(0.005)

        user32.UnregisterHotKey(hwnd, HOTKEY_ID)

    def _toggle(self):
        if self.active:
            self._stop()
        else:
            self._start()

    def _start(self):
        if self.active:
            return
        self.active = True
        self._stop_event.clear()
        self._set_status_on()
        self.spam_thread = threading.Thread(target=self._spam_loop, daemon=True)
        self.spam_thread.start()

    def _stop(self):
        self.active = False
        self._stop_event.set()
        self._current_key_idx = -1
        self._set_status_off()

    def _set_status_on(self):
        self.status_var.set("ACTIVE")
        self.status_lbl.config(fg=GREEN)

    def _set_status_off(self):
        self.status_var.set("IDLE")
        self.status_lbl.config(fg=MUTED)

    def _spam_loop(self):
        while not self._stop_event.is_set():
            for idx, (key, hold) in enumerate(PATTERN):
                if self._stop_event.is_set():
                    break
                self._current_key_idx = idx
                pyautogui.keyDown(key)
                elapsed, chunk = 0.0, 0.03
                while elapsed < hold:
                    if self._stop_event.is_set():
                        pyautogui.keyUp(key)
                        self._current_key_idx = -1
                        return
                    time.sleep(chunk)
                    elapsed += chunk
                pyautogui.keyUp(key)
        self._current_key_idx = -1

    def _on_close(self):
        self._unregister_hotkey()
        self._stop()
        self.root.destroy()


if __name__ == "__main__":
    root = tk.Tk()
    app  = MovementSpammer(root)
    root.mainloop()