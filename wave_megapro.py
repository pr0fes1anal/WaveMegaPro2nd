#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
WAVE MEGAPRO — 2D аркада на Python + Pygame.

Волна летит вперёд по узкому коридору. Пока зажата клавиша — она поднимается
вверх под углом 45°, отпустил — опускается вниз. Нужно дойти до финиша,
не задев стены, блоки и шипы. Пройденный уровень открывает следующий.

Управление в игре:
    ПРОБЕЛ / ВВЕРХ / W / ЛКМ — удерживать: вверх, отпустить: вниз
    R   — начать попытку заново
    Esc — пауза / выход в меню
    M   — вкл/выкл звук      F11 — полный экран
    -/= или колёсико мыши — громкость музыки (также ползунок в меню, магазине и на паузе)
В меню: S или кнопка «Магазин» — выбор иконки волны, цвет 1, цвет 2 и цвет трейла.

Запуск:  pip install pygame   ->   python wave_megapro.py

Музыка синтезируется самой игрой (внешние файлы не нужны). При желании можно
положить свои треки в папку music/ рядом с игрой: menu.ogg, level1.ogg ... level6.ogg
(поддерживаются также .mp3 и .wav) — они заменят встроенную музыку.
"""
import base64
import bisect
import colorsys
import io
import json
import math
import os
import random
import sys
from array import array

import pygame

# ──────────────────────────────────────────────────────────────────────────────
#  Константы
# ──────────────────────────────────────────────────────────────────────────────
W, H = 960, 540
FPS = 60
STEP = 1.0 / 120.0            # фиксированный шаг физики
PLAYER_X = 250                # экранная позиция волны
CEIL0, FLOOR0 = 45, 495       # границы обычного коридора
CY = (CEIL0 + FLOOR0) / 2
TAIL_LEN = 560                # длина шлейфа в пикселях
BASE_DIR = os.path.dirname(os.path.abspath(__file__))

LEVELS = [
    dict(name="Первые волны",     diff=0.00, speed=380, sections=7,  bpm=118, scale="minor",    root=57, prog=[0, 5, 2, 6]),
    dict(name="Неоновый тоннель", diff=0.20, speed=410, sections=8,  bpm=124, scale="dorian",   root=55, prog=[0, 3, 5, 4]),
    dict(name="Пульс города",     diff=0.40, speed=440, sections=9,  bpm=130, scale="minor",    root=52, prog=[0, 6, 5, 6]),
    dict(name="Раскалённое ядро", diff=0.60, speed=470, sections=10, bpm=138, scale="phrygian", root=50, prog=[0, 1, 0, 6]),
    dict(name="Квантовый шторм",  diff=0.80, speed=495, sections=11, bpm=144, scale="harmonic", root=53, prog=[0, 5, 3, 4]),
    dict(name="МЕГА-ПРО",         diff=1.00, speed=520, sections=12, bpm=152, scale="phrygian", root=48, prog=[0, 1, 5, 4]),
]

PALETTES = [
    dict(top=(14, 22, 56), bot=(34, 18, 76), acc=(0, 230, 255),   wall=(9, 13, 32),  spike=(255, 70, 110)),
    dict(top=(8, 40, 36),  bot=(8, 20, 40),  acc=(70, 255, 160),  wall=(6, 22, 26),  spike=(255, 200, 60)),
    dict(top=(40, 14, 60), bot=(14, 10, 40), acc=(255, 90, 220),  wall=(20, 8, 34),  spike=(120, 230, 255)),
    dict(top=(56, 20, 16), bot=(24, 10, 30), acc=(255, 150, 50),  wall=(30, 10, 12), spike=(255, 255, 255)),
    dict(top=(10, 24, 60), bot=(40, 10, 40), acc=(120, 160, 255), wall=(8, 10, 32),  spike=(255, 80, 80)),
    dict(top=(44, 6, 18),  bot=(8, 4, 16),   acc=(255, 60, 90),   wall=(24, 4, 10),  spike=(255, 235, 120)),
]

SCALES = {
    "minor":    [0, 2, 3, 5, 7, 8, 10],
    "dorian":   [0, 2, 3, 5, 7, 9, 10],
    "phrygian": [0, 1, 3, 5, 7, 8, 10],
    "harmonic": [0, 2, 3, 5, 7, 8, 11],
}
MENU_SPEC = dict(bpm=104, scale="minor", root=53, prog=[0, 5, 3, 4], seed=99)


# ──────────────────────────────────────────────────────────────────────────────
#  Вспомогательные функции
# ──────────────────────────────────────────────────────────────────────────────
def clamp(v, a, b):
    return a if v < a else b if v > b else v


def lerp(a, b, t):
    return a + (b - a) * t


def mix(c1, c2, t):
    t = clamp(t, 0.0, 1.0)
    return (int(c1[0] + (c2[0] - c1[0]) * t),
            int(c1[1] + (c2[1] - c1[1]) * t),
            int(c1[2] + (c2[2] - c1[2]) * t))


def rect_poly(x, y, w, h):
    return [(x, y), (x + w, y), (x + w, y + h), (x, y + h)]


def sat_collide(a, b):
    """Точное пересечение двух выпуклых многоугольников (теорема о разделяющей оси)."""
    for poly in (a, b):
        n = len(poly)
        for i in range(n):
            x1, y1 = poly[i]
            x2, y2 = poly[(i + 1) % n]
            nx, ny = y1 - y2, x2 - x1
            mn_a = mx_a = a[0][0] * nx + a[0][1] * ny
            for px, py in a[1:]:
                v = px * nx + py * ny
                if v < mn_a:
                    mn_a = v
                elif v > mx_a:
                    mx_a = v
            mn_b = mx_b = b[0][0] * nx + b[0][1] * ny
            for px, py in b[1:]:
                v = px * nx + py * ny
                if v < mn_b:
                    mn_b = v
                elif v > mx_b:
                    mx_b = v
            if mx_a <= mn_b or mx_b <= mn_a:
                return False
    return True


_WAVE = [(18.0, 0.0), (-11.0, -11.0), (-11.0, 11.0)]
_WAVE_ROT = {}
for _d, _ang in ((-1, -45.0), (1, 45.0)):
    _c, _s = math.cos(math.radians(_ang)), math.sin(math.radians(_ang))
    _WAVE_ROT[_d] = [(px * _c - py * _s, px * _s + py * _c) for px, py in _WAVE]


def wave_poly(x, y, d, scale=1.0):
    """Треугольник волны, повёрнутый на ±45° (d=-1 — вверх, d=1 — вниз)."""
    return [(x + px * scale, y + py * scale) for px, py in _WAVE_ROT[d]]


def make_gradient(top, bot):
    surf = pygame.Surface((W, H))
    for y in range(H):
        pygame.draw.line(surf, mix(top, bot, y / H), (0, y), (W, y))
    return surf


_fonts = {}


def get_font(size, bold=True):
    key = (size, bold)
    if key not in _fonts:
        font = None
        for name in ("segoeui", "arial", "dejavusans", "liberationsans", "notosans", "freesans", "helvetica"):
            path = pygame.font.match_font(name, bold=bold)
            if path:
                font = pygame.font.Font(path, size)
                break
        _fonts[key] = font or pygame.font.Font(None, int(size * 1.2))
    return _fonts[key]


def draw_text(surf, s, size, color, pos, anchor="topleft", bold=True, shadow=(0, 0, 0)):
    f = get_font(size, bold)
    img = f.render(s, True, color)
    r = img.get_rect(**{anchor: pos})
    if shadow:
        surf.blit(f.render(s, True, shadow), r.move(2, 2))
    surf.blit(img, r)
    return r


# ──────────────────────────────────────────────────────────────────────────────
#  Сохранение прогресса
# ──────────────────────────────────────────────────────────────────────────────
class Save:
    def __init__(self):
        self.path = os.path.join(BASE_DIR, "wave_megapro_save.json")
        self.data = {"levels": {}}
        try:
            with open(self.path, "r", encoding="utf-8") as fh:
                self.data = json.load(fh)
        except Exception:
            pass
        self.data.setdefault("levels", {})

    def lv(self, i):
        return self.data["levels"].setdefault(
            str(i), {"best": 0.0, "attempts": 0, "done": False, "best_time": None})

    def unlocked(self, i):
        return i == 0 or self.lv(i - 1)["done"]

    def write(self):
        try:
            with open(self.path, "w", encoding="utf-8") as fh:
                json.dump(self.data, fh, ensure_ascii=False, indent=2)
        except Exception:
            pass


# ──────────────────────────────────────────────────────────────────────────────
#  Уровень: генерация коридора, блоков и шипов + точные коллизии
# ──────────────────────────────────────────────────────────────────────────────
class Level:
    def __init__(self, idx):
        self.idx = idx
        self.cfg = LEVELS[idx]
        self.pal = PALETTES[idx]
        self.d = self.cfg["diff"]
        self.speed = self.cfg["speed"]
        self.rng = random.Random(7000 + idx * 131)
        self.pts = [(-1500.0, CEIL0, FLOOR0), (0.0, CEIL0, FLOOR0)]   # (x, потолок, пол)
        self.obst = []                                              # (minx, maxx, poly, kind)
        self._build()
        self._index()
        self.bg = make_gradient(self.pal["top"], self.pal["bot"])

    # --- построение геометрии ---
    def straight(self, length):
        x, c, f = self.pts[-1]
        self.pts.append((x + length, c, f))

    def morph(self, c, f, slope=0.55):
        x, c0, f0 = self.pts[-1]
        dist = max(abs(c - c0), abs(f - f0))
        if dist >= 1:
            self.pts.append((x + dist / slope, c, f))

    def add(self, kind, poly):
        xs = [p[0] for p in poly]
        self.obst.append((min(xs), max(xs), poly, kind))

    def _build(self):
        rng = self.rng
        self.straight(900)
        prev = None
        for i in range(self.cfg["sections"]):
            kinds = ["open", "tunnel", "gates"]
            if prev in kinds:
                kinds.remove(prev)
            kind = "open" if i == 0 else rng.choice(kinds)
            prev = kind
            getattr(self, "sec_" + kind)()
        self.morph(CEIL0, FLOOR0)
        self.straight(700)
        self.end_x = self.pts[-1][0]
        self.straight(1800)

    def sec_open(self):
        d, rng = self.d, self.rng
        G = lerp(410, 250, d) * rng.uniform(0.96, 1.04)
        L = rng.uniform(1300, 2000)
        c0, f0 = self.pts[-1][1], self.pts[-1][2]
        cy = clamp((c0 + f0) / 2 + rng.uniform(-40, 40), CEIL0 + G / 2, FLOOR0 - G / 2)
        c, f = cy - G / 2, cy + G / 2
        self.morph(c, f)
        sx = self.pts[-1][0]
        self.straight(L)
        minband = lerp(175, 100, d)
        s_lo, s_hi = lerp(230, 130, d), lerp(380, 220, d)
        kinds = ["sf", "sc", "pf", "pc", "fl"]
        weights = [3, 3, 1 + 2 * d, 1 + 2 * d, 0.6 + 1.5 * d]
        x = sx + 420
        last_major = False
        while x < sx + L - 330:
            kind = rng.choices(kinds, weights)[0]
            major = kind in ("pf", "pc", "fl")
            if kind in ("sf", "sc"):
                n = rng.randint(1, 2 + int(2 * d))
                h = min(rng.uniform(38, 70), G - minband)
                width = n * 34
                for k in range(n):
                    cx = x + 17 + 34 * k
                    if kind == "sf":
                        self.add("spike", [(cx - 17, f), (cx + 17, f), (cx, f - h)])
                    else:
                        self.add("spike", [(cx - 17, c), (cx + 17, c), (cx, c + h)])
            elif kind in ("pf", "pc"):
                width = rng.choice([44, 66, 88])
                h = rng.uniform(G * 0.35, G - minband)
                y0 = f - h if kind == "pf" else c
                self.add("block", rect_poly(x, y0, width, h))
            else:
                s = rng.choice([48, 64, 80])
                width = s
                free = G - s
                lo_gap = max(70.0, minband * 0.6)
                top = free / 2 if free < 2 * lo_gap else rng.uniform(lo_gap, free - lo_gap)
                self.add("block", rect_poly(x, c + top, s, s))
            gap = rng.uniform(s_lo, s_hi)
            if major or last_major:
                gap = max(gap, G * 0.9)
            last_major = major
            x += width + gap

    def sec_gates(self):
        d, rng = self.d, self.rng
        self.morph(CEIL0, FLOOR0)
        wg = lerp(250, 130, d) * rng.uniform(0.95, 1.08)
        gw = 48
        n = rng.randint(5, 8)
        sx = self.pts[-1][0]
        x = sx + 480
        lo, hi = CEIL0 + wg / 2 + 25, FLOOR0 - wg / 2 - 25
        y = rng.uniform(lo, hi)
        gates = []
        for _ in range(n):
            gates.append((x, y))
            ny = clamp(y + rng.choice((-1, 1)) * rng.uniform(70, 230), lo, hi)
            if abs(ny - y) < 40:
                ny = clamp(y + (120 if y < CY else -120), lo, hi)
            spacing = max(0.0, abs(ny - y) - 0.6 * wg) + lerp(190, 125, d)
            x += gw + spacing
            y = ny
        self.straight(x + 300 - sx)
        for gx, gy in gates:
            top_h = (gy - wg / 2) - (CEIL0 - 2)
            self.add("block", rect_poly(gx, CEIL0 - 2, gw, top_h))
            self.add("block", rect_poly(gx, gy + wg / 2, gw, (FLOOR0 + 2) - (gy + wg / 2)))

    def sec_tunnel(self):
        d, rng = self.d, self.rng
        G = lerp(250, 108, d) * rng.uniform(0.96, 1.06)
        smin, smax = lerp(200, 90, d), lerp(340, 190, d)
        L = rng.uniform(1700, 2600)
        c, f = self.pts[-1][1], self.pts[-1][2]
        lo, hi = CEIL0 + G / 2 + 5, FLOOR0 - G / 2 - 5
        y = clamp((c + f) / 2, lo, hi)
        self.morph(y - G / 2, y + G / 2)
        x0 = x = self.pts[-1][0]
        direction = rng.choice((-1, 1))
        while x - x0 < L:
            seg = rng.uniform(smin, smax)
            room = (y - lo) if direction < 0 else (hi - y)
            if room < 40:
                direction = -direction
                room = (y - lo) if direction < 0 else (hi - y)
            seg = min(seg, room)
            y += direction * seg
            x += seg
            self.pts.append((x, y - G / 2, y + G / 2))
            direction = -direction

    # --- индексы для быстрых коллизий ---
    def _index(self):
        self.wall_x = [p[0] for p in self.pts]
        self.walls = []
        for i in range(len(self.pts) - 1):
            x0, c0, f0 = self.pts[i]
            x1, c1, f1 = self.pts[i + 1]
            cq = [(x0, -3000), (x1, -3000), (x1, c1), (x0, c0)]
            fq = [(x0, f0), (x1, f1), (x1, 3000), (x0, 3000)]
            self.walls.append((max(c0, c1), min(f0, f1), cq, fq))
        self.obst.sort(key=lambda o: o[0])
        self.o_minx = [o[0] for o in self.obst]
        self.o_maxw = max((o[1] - o[0] for o in self.obst), default=0)

    def collides(self, poly):
        xs = [p[0] for p in poly]
        ys = [p[1] for p in poly]
        mnx, mxx, mny, mxy = min(xs), max(xs), min(ys), max(ys)
        i0 = max(0, bisect.bisect_right(self.wall_x, mnx) - 1)
        i1 = min(len(self.walls) - 1, bisect.bisect_right(self.wall_x, mxx) - 1)
        for i in range(i0, i1 + 1):
            c_max, f_min, cq, fq = self.walls[i]
            if mny > c_max and mxy < f_min:
                continue
            if sat_collide(poly, cq) or sat_collide(poly, fq):
                return True
        lo = bisect.bisect_left(self.o_minx, mnx - self.o_maxw)
        hi = bisect.bisect_right(self.o_minx, mxx)
        for j in range(lo, hi):
            o_min, o_max, opoly, _ = self.obst[j]
            if o_max < mnx:
                continue
            oy = [p[1] for p in opoly]
            if max(oy) < mny or min(oy) > mxy:
                continue
            if sat_collide(poly, opoly):
                return True
        return False


# ──────────────────────────────────────────────────────────────────────────────
#  Синтез звука (музыка и эффекты генерируются в коде)
# ──────────────────────────────────────────────────────────────────────────────
def tone(sr, freq, dur, wave="square", duty=0.5, decay=2.0, attack=0.004):
    n = max(1, int(sr * dur))
    out = [0.0] * n
    ph, inc = 0.0, freq / sr
    att = max(1, int(sr * attack))
    for i in range(n):
        ph += inc
        p = ph - int(ph)
        if wave == "square":
            s = 1.0 if p < duty else -1.0
        elif wave == "tri":
            s = 4.0 * abs(p - 0.5) - 1.0
        else:
            s = 2.0 * p - 1.0
        env = (1.0 - i / n) ** decay
        if i < att:
            env *= i / att
        out[i] = s * env
    return out


def noise_burst(sr, dur, decay=2.0, seed=1):
    r = random.Random(seed)
    n = int(sr * dur)
    return [r.uniform(-1, 1) * (1 - i / n) ** decay for i in range(n)]


def kick_drum(sr):
    n = int(sr * 0.16)
    out, ph = [], 0.0
    for i in range(n):
        ph += (45 + 130 * math.exp(-(i / sr) * 28)) / sr
        out.append(math.sin(2 * math.pi * ph) * (1 - i / n) ** 1.6)
    return out


def make_music(sr, spec):
    rng = random.Random(spec.get("seed", spec["bpm"]))
    bpm = spec["bpm"]
    step = 60.0 / bpm / 4
    step_n = step * sr
    steps = 8 * 16
    total = int(steps * step_n)
    buf = [0.0] * total
    scale, root, prog = SCALES[spec["scale"]], spec["root"], spec["prog"]
    cache = {}

    def freq(deg, octv=0):
        m = root + scale[deg % 7] + 12 * (deg // 7) + 12 * octv
        return 440.0 * 2 ** ((m - 69) / 12.0)

    def get(wave, f, dur, decay, duty=0.5):
        key = (wave, round(f, 2), round(dur, 3), decay, duty)
        if key not in cache:
            cache[key] = tone(sr, f, dur, wave, duty, decay)
        return cache[key]

    def put(start, samples, vol):
        end = min(total, start + len(samples))
        if end > start:
            buf[start:end] = [a + b * vol for a, b in zip(buf[start:end], samples)]

    kick = kick_drum(sr)
    snare = noise_burst(sr, 0.13, 2.0, 2)
    hat = noise_burst(sr, 0.04, 2.5, 3)
    arp_pat = [0, 1, 2, 3, 2, 1, 2, 3]
    lead_pats = [[rng.choice([None, None, 0, 2, 4, 7, 4, 9]) for _ in range(8)] for _ in range(2)]

    for s in range(steps):
        bar, st = divmod(s, 16)
        chord = prog[(bar // 2) % len(prog)]
        t0 = int(s * step_n)
        if st % 4 == 0:
            put(t0, kick, 0.55)
        if st in (4, 12):
            put(t0, snare, 0.30)
        if st % 2 == 0:
            put(t0, hat, 0.12 if st % 4 else 0.18)
        if st % 2 == 0:
            octv = -2 if (st % 8) < 6 else -1
            put(t0, get("square", freq(chord, octv), step * 1.8, 1.0, 0.35), 0.36)
        tones = (chord, chord + 2, chord + 4, chord + 7)
        put(t0, get("square", freq(tones[arp_pat[st % 8] % 4], 1), step * 1.6, 2.2, 0.25), 0.15)
        if bar >= 1 and st % 2 == 0:
            off = lead_pats[(bar // 4) % 2][st // 2]
            if off is not None:
                put(t0, get("tri", freq(chord + off, 1), step * 3, 0.8), 0.28)
    return buf


class Audio:
    def __init__(self, volume=0.8):
        self.enabled = False
        self.muted = False
        self.volume = volume
        self.music = {}
        self.sfx = {}
        self.ext_playing = False
        try:
            if not pygame.mixer.get_init():
                pygame.mixer.init()
            self.rate, _, self.ch = pygame.mixer.get_init()
            pygame.mixer.set_num_channels(8)
            self.chan = pygame.mixer.Channel(0)
            self.enabled = True
        except pygame.error:
            return
        self._make_sfx()

    def _sound(self, buf, peak=0.85):
        m = max(1e-9, max(abs(v) for v in buf))
        k = peak * 32767 / m
        data = array("h", [int(v * k) for v in buf])
        if self.ch == 2:
            data2 = array("h", [0]) * (2 * len(data))
            data2[0::2] = data
            data2[1::2] = data
            data = data2
        return pygame.mixer.Sound(buffer=data.tobytes())

    def _make_sfx(self):
        sr = self.rate
        # крушение: шум + падающий тон
        n = int(sr * 0.45)
        r = random.Random(4)
        out, ph = [], 0.0
        for i in range(n):
            ph += (420 * math.exp(-(i / sr) * 7) + 50) / sr
            sq = 1.0 if (ph - int(ph)) < 0.5 else -1.0
            out.append((sq * 0.5 + r.uniform(-1, 1) * 0.7) * (1 - i / n) ** 1.5)
        self.sfx["death"] = self._sound(out)
        # победа: восходящее арпеджио
        win = [0.0] * int(sr * 1.0)
        for k, m in enumerate((72, 76, 79, 84, 88)):
            f = 440 * 2 ** ((m - 69) / 12)
            smp = tone(sr, f, 0.35, "square", 0.5, 1.4)
            st = int(k * 0.11 * sr)
            for i, v in enumerate(smp):
                if st + i < len(win):
                    win[st + i] += v * 0.5
        self.sfx["win"] = self._sound(win)
        self.sfx["click"] = self._sound(tone(sr, 880, 0.06, "square", 0.5, 1.0))
        self.sfx["deny"] = self._sound(tone(sr, 130, 0.14, "square", 0.5, 0.8))
        for s in self.sfx.values():
            s.set_volume(0.55)

    def play_sfx(self, name):
        if self.enabled and not self.muted and name in self.sfx:
            self.sfx[name].play()

    def _external(self, key):
        name = "menu" if key == "menu" else "level%d" % (key + 1)
        for ext in (".ogg", ".mp3", ".wav"):
            p = os.path.join(BASE_DIR, "music", name + ext)
            if os.path.isfile(p):
                return p
        return None

    def play_music(self, key):
        """key: 'menu' или номер уровня."""
        if not self.enabled:
            return
        self.stop_music()
        ext = self._external(key)
        if ext:
            try:
                pygame.mixer.music.load(ext)
                pygame.mixer.music.play(-1)
                self.ext_playing = True
                self.apply_volume()
                return
            except pygame.error:
                pass
        if key not in self.music:
            spec = MENU_SPEC if key == "menu" else LEVELS[key]
            snd = self._sound(make_music(self.rate, spec), 0.8)
            snd.set_volume(0.7)
            self.music[key] = snd
        self.chan.play(self.music[key], loops=-1)
        self.apply_volume()

    def stop_music(self):
        if not self.enabled:
            return
        self.chan.stop()
        if self.ext_playing:
            pygame.mixer.music.stop()
            self.ext_playing = False

    def pause(self):
        if self.enabled:
            self.chan.pause()
            if self.ext_playing:
                pygame.mixer.music.pause()

    def resume(self):
        if self.enabled:
            self.chan.unpause()
            if self.ext_playing:
                pygame.mixer.music.unpause()

    def apply_volume(self):
        if not self.enabled:
            return
        v = 0.0 if self.muted else self.volume
        self.chan.set_volume(v)
        if self.ext_playing:
            pygame.mixer.music.set_volume(v)

    def set_volume(self, v):
        self.volume = clamp(v, 0.0, 1.0)
        if self.volume > 0:
            self.muted = False
        self.apply_volume()

    def toggle_mute(self):
        self.muted = not self.muted
        self.apply_volume()


# ──────────────────────────────────────────────────────────────────────────────
#  Иконки волны (слои из спрайтов), анимация наклона, шлейф
# ──────────────────────────────────────────────────────────────────────────────
SKIN_NAMES = ["Стрела", "Кольцо", "Модуль", "Пламя", "Кристалл"]
DEFAULT_WAVE = dict(skin=0, c1=[0, 230, 255], c2=[255, 255, 255], trail=[0, 230, 255])
SLOTS = ("c1", "c2", "trail")
SLOT_NAMES = ("Цвет 1", "Цвет 2", "Трейл")
PRESETS = [(255, 255, 255), (255, 70, 90), (255, 150, 50), (255, 230, 60),
           (110, 255, 120), (0, 255, 170), (0, 230, 255), (70, 130, 255),
           (160, 90, 255), (255, 90, 220), (150, 160, 180), (30, 30, 50)]
SPRITE_LEN, SPRITE_THK = 40.0, 30.0     # размер иконки в игре (пиксели)


class Skins:
    """Иконки хранятся слоями: цвет 1, цвет 2, блик и чёрный контур.
    Слои перекрашиваются «на лету» в любые два цвета."""

    def __init__(self):
        self.layers = []
        self.cache = {}
        for b64 in SKIN_DATA:
            img = pygame.image.load(io.BytesIO(base64.b64decode(b64)), "skin.png")
            w, h = img.get_size()
            l1, l2, ov, bk = (pygame.Surface((w, h), pygame.SRCALPHA) for _ in range(4))
            for y in range(h):
                for x in range(w):
                    r, g, b, _a = img.get_at((x, y))
                    if r:
                        l1.set_at((x, y), (255, 255, 255, r))
                    if g:
                        l2.set_at((x, y), (255, 255, 255, g))
                    if b >= 128:
                        bk.set_at((x, y), (0, 0, 0, min(255, (b - 128) * 255 // 127)))
                    elif b:
                        ov.set_at((x, y), (255, 255, 255, min(255, b * 255 // 127)))
            self.layers.append(tuple(t.convert_alpha() for t in (l1, l2, ov, bk)))

    def tinted(self, i, c1, c2):
        key = (i, tuple(c1), tuple(c2))
        surf = self.cache.get(key)
        if surf is None:
            if len(self.cache) > 80:
                self.cache.clear()
            l1, l2, ov, bk = self.layers[i]
            surf = pygame.Surface(l1.get_size(), pygame.SRCALPHA)
            for layer, col in ((l2, c2), (l1, c1)):
                t = layer.copy()
                t.fill((col[0], col[1], col[2], 255), special_flags=pygame.BLEND_RGBA_MULT)
                surf.blit(t, (0, 0))
            surf.blit(ov, (0, 0))
            surf.blit(bk, (0, 0))
            self.cache[key] = surf
        return surf

    def scale(self, i):
        w, h = self.layers[i][0].get_size()
        return min(SPRITE_LEN / w, SPRITE_THK / h)


class WaveAnim:
    """Плавный наклон иконки: пружина с небольшим «перелётом» + пульс при повороте."""

    def __init__(self):
        self.reset(1)

    def reset(self, d):
        self.va = 45.0 if d < 0 else -45.0
        self.vel = 0.0
        self.pulse = 0.0

    def turn(self):
        self.pulse = 1.0

    def update(self, dt, d):
        target = 45.0 if d < 0 else -45.0
        n = int(dt / (1 / 240)) + 1
        h = dt / n
        for _ in range(n):
            self.vel += ((target - self.va) * 950.0 - self.vel * 42.0) * h
            self.va += self.vel * h
        self.pulse = max(0.0, self.pulse - dt * 5.5)

    def scale(self):
        return 1.0 + 0.25 * self.pulse * self.pulse


STATIC_ANIM = WaveAnim()
STATIC_ANIM.va = 0.0


def render_trail(surf, pts, head_x, cam, color, base):
    """Шлейф траектории: свечение + яркое ядро, затухает к хвосту."""
    pieces = []
    for i in range(1, len(pts)):
        (x0, y0), (x1, y1) = pts[i - 1], pts[i]
        n = max(1, int(abs(x1 - x0) // 24) + 1)
        for k in range(n):
            ax, bx = lerp(x0, x1, k / n), lerp(x0, x1, (k + 1) / n)
            ay, by = lerp(y0, y1, k / n), lerp(y0, y1, (k + 1) / n)
            age = (head_x - bx) / TAIL_LEN
            if age < 1:
                pieces.append((ax - cam, ay, bx - cam, by, 1 - age))
    for ax, ay, bx, by, f in pieces:
        w = max(2, int(2 + 7 * f))
        pygame.draw.line(surf, mix(base, color, f * 0.45), (ax, ay), (bx, by), w + 6)
    for ax, ay, bx, by, f in pieces:
        w = max(2, int(2 + 7 * f))
        c = mix(mix(base, color, f), (255, 255, 255), 0.5 if f > 0.75 else 0.0)
        pygame.draw.line(surf, c, (ax, ay), (bx, by), w)
        pygame.draw.circle(surf, c, (int(bx), int(by)), max(1, w // 2))


# ──────────────────────────────────────────────────────────────────────────────
#  Игра
# ──────────────────────────────────────────────────────────────────────────────
class Game:
    def __init__(self):
        pygame.mixer.pre_init(22050, -16, 1, 512)
        pygame.init()
        pygame.display.set_caption("Wave MegaPro")
        try:
            self.screen = pygame.display.set_mode((W, H), pygame.SCALED | pygame.RESIZABLE)
        except Exception:
            self.screen = pygame.display.set_mode((W, H))
        self.clock = pygame.time.Clock()
        self.save = Save()
        self.state = "menu"
        self.time = 0.0
        self.buttons = []
        self.levels = {}
        self.menu_bg = make_gradient((12, 14, 40), (30, 12, 56))
        self.overlay = pygame.Surface((W, H), pygame.SRCALPHA)
        self.latch = False
        self.particles = []
        self.confetti = []
        self.flash = 0.0
        self.new_unlock = None

        self.skins = Skins()
        self.cfg = self.save.data.setdefault("wave", {})
        for k, v in DEFAULT_WAVE.items():
            self.cfg.setdefault(k, list(v) if isinstance(v, list) else v)
        if not 0 <= self.cfg["skin"] < len(SKIN_NAMES):
            self.cfg["skin"] = 0
        self.anim, self.pv_anim, self.pv_dir = WaveAnim(), WaveAnim(), 1
        self.drag, self.vol_rect, self.vol_popup, self.dt = None, None, 0.0, 0.0
        self.slot, self.hsv, self.hex_text, self.hex_focus = 0, (0.5, 1.0, 1.0), "", False
        self._sv = (-1, None)
        self._hue = self.make_hue()
        self.load_hsv()

        self.loading("Генерация музыки…")
        self.audio = Audio(float(self.save.data.get("volume", 0.8)))
        self.sel = 0
        for i in range(len(LEVELS)):
            if self.save.unlocked(i):
                self.sel = i
        self.audio.play_music("menu")

    # --- служебное ---
    def loading(self, msg):
        self.screen.blit(self.menu_bg, (0, 0))
        draw_text(self.screen, "WAVE MEGAPRO", 64, (0, 230, 255), (W // 2, H // 2 - 30), "center")
        draw_text(self.screen, msg, 24, (200, 210, 240), (W // 2, H // 2 + 40), "center", False)
        pygame.display.flip()
        pygame.event.pump()

    def get_level(self, idx):
        if idx not in self.levels:
            self.levels[idx] = Level(idx)
        return self.levels[idx]

    def quit(self):
        self.save.write()
        pygame.quit()
        sys.exit()

    # --- запуск уровня и попыток ---
    def start_level(self, idx):
        self.loading("Загрузка уровня «%s»…" % LEVELS[idx]["name"])
        self.level_idx = idx
        self.level = self.get_level(idx)
        self.pal = self.level.pal
        self.audio.play_music(idx)  # генерируется при первом запуске
        self.new_unlock = None
        self.reset_attempt()

    def reset_attempt(self):
        self.px, self.py, self.dir = 0.0, CY, 1
        self.anim.reset(1)
        self.trail = [(0.0, CY)]
        self.particles = []
        self.confetti = []
        self.acc = 0.0
        self.t = 0.0
        self.flash = 0.0
        self.state = "play"
        rec = self.save.lv(self.level_idx)
        rec["attempts"] += 1
        self.attempt = rec["attempts"]
        self.save.write()
        self.audio.play_music(self.level_idx)

    def progress(self):
        return clamp(self.px / self.level.end_x * 100.0, 0.0, 100.0)

    def die(self):
        rec = self.save.lv(self.level_idx)
        self.pct_died = self.progress()
        rec["best"] = max(rec["best"], round(self.pct_died, 1))
        self.save.write()
        rng = random.Random()
        for _ in range(46):
            a = rng.uniform(0, math.tau)
            sp = rng.uniform(80, 420)
            self.particles.append([self.px, self.py, math.cos(a) * sp, math.sin(a) * sp,
                                   rng.uniform(0.5, 1.1), 1.1, rng.choice([(255, 255, 255), self.cfg_c("c1"), self.cfg_c("c2"), self.cfg_c("trail")]),
                                   rng.uniform(3, 7)])
        self.audio.stop_music()
        self.audio.play_sfx("death")
        self.flash = 0.6
        self.state = "dead"
        self.dead_t = 0.0

    def finish(self):
        self.state = "finish"
        self.fin_t = 0.0
        self.audio.play_sfx("win")

    def win(self):
        rec = self.save.lv(self.level_idx)
        rec["best"] = 100.0
        first = not rec["done"]
        rec["done"] = True
        if rec["best_time"] is None or self.t < rec["best_time"]:
            rec["best_time"] = round(self.t, 2)
        nxt = self.level_idx + 1
        self.new_unlock = nxt if first and nxt < len(LEVELS) else None
        self.save.write()
        rng = random.Random()
        for _ in range(140):
            self.confetti.append([rng.uniform(0, W), rng.uniform(-H, 0), rng.uniform(-60, 60), rng.uniform(80, 260),
                                  rng.choice([self.pal["acc"], self.pal["spike"], (255, 255, 255), (255, 220, 80)]),
                                  rng.uniform(4, 9)])
        self.state = "win"

    # --- физика ---
    def hold_now(self):
        keys = pygame.key.get_pressed()
        h = keys[pygame.K_SPACE] or keys[pygame.K_UP] or keys[pygame.K_w] or pygame.mouse.get_pressed()[0]
        return bool(h) or self.latch

    def physics_step(self, auto=False):
        v = self.level.speed
        if auto:
            d = -1 if self.py > CY else 1
        else:
            d = -1 if self.hold_now() else 1
        self.latch = False
        if d != self.dir:
            self.trail.append((self.px, self.py))
            self.dir = d
            self.anim.turn()
            tc = self.cfg_c("trail")
            for _ in range(3):
                a = random.uniform(0, math.tau)
                sp = random.uniform(40, 170)
                self.particles.append([self.px, self.py, math.cos(a) * sp, math.sin(a) * sp, 0.35, 0.35, tc, 4])
        self.px += v * STEP
        self.py += d * v * STEP
        if not auto:
            if self.level.collides(wave_poly(self.px, self.py, d)):
                self.die()
                return
            if self.px >= self.level.end_x:
                self.finish()

    def update(self, dt):
        self.time += dt
        self.dt = dt
        self.vol_popup = max(0.0, self.vol_popup - dt)
        st = self.state
        if st in ("play", "finish", "win"):
            self.anim.update(dt, self.dir)
        if st in ("play", "finish", "dead", "win", "pause"):
            for p in self.particles:
                p[0] += p[2] * dt
                p[1] += p[3] * dt
                p[3] += 600 * dt
                p[4] -= dt
            self.particles = [p for p in self.particles if p[4] > 0]
            self.flash = max(0.0, self.flash - dt * 1.6)
        if st == "play":
            self.t += dt
            self.acc += dt
            while self.acc >= STEP and self.state == "play":
                self.acc -= STEP
                self.physics_step()
        elif st == "finish":
            self.t += 0.0
            self.acc += dt
            self.fin_t += dt
            while self.acc >= STEP:
                self.acc -= STEP
                self.physics_step(auto=True)
            if self.fin_t > 1.3:
                self.win()
        elif st == "dead":
            self.dead_t += dt
            if self.dead_t > 0.9:
                self.reset_attempt()
        elif st == "win":
            for c in self.confetti:
                c[0] += c[2] * dt
                c[1] += c[3] * dt
                if c[1] > H + 20:
                    c[1] = -20
                    c[0] = random.uniform(0, W)

    # --- события ---
    def handle(self, e):
        if e.type == pygame.QUIT:
            self.quit()
        typing = self.state == "shop" and self.hex_focus
        if e.type == pygame.KEYDOWN:
            if e.key == pygame.K_F11:
                pygame.display.toggle_fullscreen()
                return
            if not typing:
                if e.key == pygame.K_m:
                    self.audio.toggle_mute()
                    return
                if e.key in (pygame.K_MINUS, pygame.K_KP_MINUS):
                    self.change_volume(-0.05)
                    return
                if e.key in (pygame.K_EQUALS, pygame.K_PLUS, pygame.K_KP_PLUS):
                    self.change_volume(0.05)
                    return
        if e.type == pygame.MOUSEWHEEL:
            self.change_volume(0.05 * e.y)
            return
        if e.type == pygame.MOUSEBUTTONDOWN and e.button == 1 and self.vol_rect is not None \
                and self.vol_rect.inflate(24, 28).collidepoint(e.pos):
            self.drag = "vol"
            self.set_vol_x(e.pos[0])
            return
        if e.type == pygame.MOUSEMOTION and self.drag == "vol":
            self.set_vol_x(e.pos[0])
            return
        if e.type == pygame.MOUSEMOTION and self.drag in ("sv", "hue"):
            self.shop_drag(e.pos)
            return
        if e.type == pygame.MOUSEBUTTONUP and e.button == 1 and self.drag:
            self.drag = None
            self.save.write()
            return
        getattr(self, "on_" + self.state, lambda ev: None)(e)

    def click_button(self, e):
        if e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
            for rect, action in self.buttons:
                if rect.collidepoint(e.pos):
                    self.audio.play_sfx("click")
                    getattr(self, "act_" + action)()
                    return True
        return False

    def on_menu(self, e):
        n = len(LEVELS)
        if self.click_button(e):
            return
        if e.type == pygame.KEYDOWN:
            if e.key == pygame.K_ESCAPE:
                self.quit()
            elif e.key == pygame.K_RIGHT:
                self.sel = (self.sel + 1) % n
            elif e.key == pygame.K_LEFT:
                self.sel = (self.sel - 1) % n
            elif e.key == pygame.K_DOWN:
                self.sel = (self.sel + 3) % n
            elif e.key == pygame.K_UP:
                self.sel = (self.sel - 3) % n
            elif e.key == pygame.K_s:
                self.act_shop()
            elif e.key in (pygame.K_RETURN, pygame.K_SPACE, pygame.K_KP_ENTER):
                self.try_start(self.sel)
        elif e.type == pygame.MOUSEMOTION:
            for i in range(n):
                if self.card_rect(i).collidepoint(e.pos):
                    self.sel = i
        elif e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
            for i in range(n):
                if self.card_rect(i).collidepoint(e.pos):
                    self.sel = i
                    self.try_start(i)

    def try_start(self, i):
        if self.save.unlocked(i):
            self.audio.play_sfx("click")
            self.start_level(i)
        else:
            self.audio.play_sfx("deny")

    def on_play(self, e):
        if e.type == pygame.KEYDOWN:
            if e.key in (pygame.K_SPACE, pygame.K_UP, pygame.K_w):
                self.latch = True
            elif e.key == pygame.K_r:
                self.reset_attempt()
            elif e.key in (pygame.K_ESCAPE, pygame.K_p):
                self.state = "pause"
                self.audio.pause()
        elif e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
            self.latch = True

    def on_dead(self, e):
        if e.type == pygame.KEYDOWN:
            if e.key == pygame.K_ESCAPE:
                self.act_menu()
            elif e.key == pygame.K_r:
                self.reset_attempt()

    def on_finish(self, e):
        pass

    def on_pause(self, e):
        if self.click_button(e):
            return
        if e.type == pygame.KEYDOWN:
            if e.key in (pygame.K_ESCAPE, pygame.K_p, pygame.K_RETURN):
                self.act_resume()
            elif e.key == pygame.K_q:
                self.act_menu()
            elif e.key == pygame.K_r:
                self.act_restart()

    def on_win(self, e):
        if self.click_button(e):
            return
        if e.type == pygame.KEYDOWN:
            if e.key == pygame.K_r:
                self.act_restart()
            elif e.key in (pygame.K_RETURN, pygame.K_n, pygame.K_KP_ENTER):
                self.act_next()
            elif e.key == pygame.K_ESCAPE:
                self.act_menu()

    # --- действия кнопок ---
    def act_resume(self):
        self.state = "play"
        self.audio.resume()

    def act_restart(self):
        self.reset_attempt()

    def act_menu(self):
        self.audio.play_music("menu")
        self.state = "menu"
        self.sel = self.level_idx if hasattr(self, "level_idx") else self.sel
        self.particles = []

    def act_next(self):
        nxt = self.level_idx + 1
        if nxt < len(LEVELS) and self.save.unlocked(nxt):
            self.start_level(nxt)
        else:
            self.act_menu()

    # ──────────────────────────────────────────────────────────────────────────
    #  Отрисовка
    # ──────────────────────────────────────────────────────────────────────────
    def card_rect(self, i):
        col, row = i % 3, i // 3
        return pygame.Rect(50 + col * 295, 200 + row * 148, 270, 130)

    def draw_button(self, rect, label, color, hover):
        s = self.screen
        pygame.draw.rect(s, mix((20, 24, 50), color, 0.35 if hover else 0.18), rect, border_radius=12)
        pygame.draw.rect(s, color, rect, 2, border_radius=12)
        draw_text(s, label, 24, (255, 255, 255), rect.center, "center")

    def draw_menu(self):
        s = self.screen
        s.blit(self.menu_bg, (0, 0))
        t = self.time
        # анимированная «волна» на фоне заголовка
        pts = []
        for x in range(-20, W + 40, 10):
            u = (x + t * 220) % 120
            pts.append((x, 26 + abs(u - 60)))
        pygame.draw.lines(s, (20, 70, 100), False, [(x, y + 6) for x, y in pts], 12)
        pygame.draw.lines(s, (0, 200, 230), False, pts, 4)
        draw_text(s, "WAVE MEGAPRO", 76, (255, 255, 255), (W // 2, 128), "center")
        draw_text(s, "Выберите уровень", 22, (170, 190, 230), (W // 2, 176), "center", False)

        self.buttons = []
        mouse = pygame.mouse.get_pos()
        for i, cfg in enumerate(LEVELS):
            r = self.card_rect(i)
            pal = PALETTES[i]
            rec = self.save.lv(i)
            unlocked = self.save.unlocked(i)
            selected = (i == self.sel)
            if selected:
                r = r.inflate(10, 6)
            body = mix(pal["top"], pal["bot"], 0.5) if unlocked else (24, 24, 34)
            pygame.draw.rect(s, body, r, border_radius=14)
            pygame.draw.rect(s, pal["acc"] if unlocked else (70, 70, 90), r, 4 if selected else 2, border_radius=14)
            col = (255, 255, 255) if unlocked else (130, 130, 150)
            draw_text(s, "%d" % (i + 1), 40, pal["acc"] if unlocked else (100, 100, 120), (r.x + 16, r.y + 8))
            draw_text(s, cfg["name"], 21, col, (r.x + 58, r.y + 20))
            # сложность
            for k in range(6):
                on = k <= i
                pygame.draw.rect(s, (pal["acc"] if (on and unlocked) else (60, 64, 90)),
                                 (r.x + 18 + k * 18, r.y + 62, 13, 8), border_radius=3)
            if unlocked:
                bar = pygame.Rect(r.x + 18, r.y + 84, r.w - 36, 10)
                pygame.draw.rect(s, (15, 18, 40), bar, border_radius=5)
                if rec["best"] > 0:
                    fill = bar.copy()
                    fill.w = max(6, int(bar.w * rec["best"] / 100))
                    pygame.draw.rect(s, pal["acc"], fill, border_radius=5)
                label = "ПРОЙДЕН  100%" if rec["done"] else "Рекорд: %d%%" % int(rec["best"])
                draw_text(s, label, 17, (225, 235, 255), (r.x + 18, r.y + 102), bold=False)
                draw_text(s, "Попыток: %d" % rec["attempts"], 17, (170, 185, 220),
                          (r.right - 16, r.y + 102), "topright", False)
            else:
                # замок
                lx, ly = r.centerx + 60, r.y + 80
                pygame.draw.rect(s, (110, 110, 135), (lx - 14, ly - 4, 28, 22), border_radius=4)
                pygame.draw.arc(s, (110, 110, 135), (lx - 9, ly - 20, 18, 22), 0, math.pi, 4)
                draw_text(s, "Пройдите уровень %d" % i, 17, (130, 130, 150), (r.x + 18, r.y + 100), bold=False)
        draw_text(s, "← ↑ ↓ → / мышь — выбор  ·  Enter / клик — старт  ·  S — магазин  ·  -/= или колёсико — громкость  ·  M — звук  ·  Esc — выход",
                  14, (150, 165, 205), (W // 2, H - 22), "center", False, None)
        shop = pygame.Rect(16, 14, 190, 44)
        self.buttons.append((shop, "shop"))
        self.draw_button(shop, "Магазин  (S)", (255, 200, 80), shop.collidepoint(mouse))
        panel = pygame.Rect(W - 310, 14, 294, 44)
        pygame.draw.rect(s, (14, 18, 40), panel, border_radius=12)
        pygame.draw.rect(s, (70, 80, 120), panel, 2, border_radius=12)
        draw_text(s, "Музыка", 18, (210, 220, 245), (panel.x + 14, panel.centery), "midleft", False, None)
        self.vol_rect = pygame.Rect(panel.x + 92, panel.centery - 5, 130, 10)
        self.draw_slider(self.vol_rect, self.audio.volume)
        draw_text(s, "%d%%" % round(self.audio.volume * 100), 18, (255, 255, 255),
                  (panel.right - 12, panel.centery), "midright", False, None)
        if self.audio.muted:
            draw_text(s, "звук выключен (M)", 14, (255, 120, 120), (W - 16, 62), "topright", False, None)

    # --- игровой мир ---
    def draw_world(self):
        s, lv, pal = self.screen, self.level, self.pal
        cam = self.px - PLAYER_X
        beat = self.t * lv.cfg["bpm"] / 60.0
        pulse = (1.0 - (beat % 1.0)) ** 3 if self.state in ("play", "finish") else 0.0

        s.blit(lv.bg, (0, 0))
        base = mix(pal["top"], pal["bot"], 0.5)
        col = mix(base, pal["acc"], 0.07 + 0.10 * pulse)
        spacing = 190
        shift = cam * 0.3
        k0 = int(shift // spacing)
        off = shift - k0 * spacing
        for i in range(-1, W // spacing + 2):
            k = i + k0
            bx = i * spacing - off
            hh = 120 + 110 * abs(math.sin(k * 1.7))
            pygame.draw.rect(s, col, (bx, H - hh, 90, hh))
            pygame.draw.rect(s, col, (bx + 60, 0, 70, 90 + 80 * abs(math.sin(k * 2.3))))

        # финиш
        fx = lv.end_x - cam
        if -60 < fx < W + 60:
            for r in range(0, H, 24):
                pygame.draw.rect(s, (255, 255, 255) if (r // 24) % 2 == 0 else (30, 30, 40), (fx, r, 24, 24))
                pygame.draw.rect(s, (30, 30, 40) if (r // 24) % 2 == 0 else (255, 255, 255), (fx + 24, r, 24, 24))
            glow = mix(base, pal["acc"], 0.35)
            pygame.draw.rect(s, glow, (fx - 40, 0, 40, H))

        # стены
        i0 = max(0, bisect.bisect_right(lv.wall_x, cam) - 1)
        i1 = min(len(lv.pts) - 2, bisect.bisect_right(lv.wall_x, cam + W))
        wall = pal["wall"]
        for i in range(i0, i1 + 1):
            x0, c0, f0 = lv.pts[i]
            x1, c1, f1 = lv.pts[i + 1]
            a, b = x0 - cam, x1 - cam
            pygame.draw.polygon(s, wall, [(a, -10), (b, -10), (b, c1), (a, c0)])
            pygame.draw.polygon(s, wall, [(a, f0), (b, f1), (b, H + 10), (a, H + 10)])
        cpts = [(lv.pts[i][0] - cam, lv.pts[i][1]) for i in range(i0, i1 + 2)]
        fpts = [(lv.pts[i][0] - cam, lv.pts[i][2]) for i in range(i0, i1 + 2)]
        glow = mix(wall, pal["acc"], 0.35 + 0.25 * pulse)
        inner = mix(wall, pal["acc"], 0.18)
        for pts, sgn in ((cpts, -1), (fpts, 1)):
            pygame.draw.lines(s, glow, False, pts, 11)
            pygame.draw.lines(s, inner, False, [(x, y + sgn * -14) for x, y in pts], 2)
            pygame.draw.lines(s, pal["acc"], False, pts, 4)
            for p in pts:
                pygame.draw.circle(s, pal["acc"], p, 2)

        # препятствия
        lo = bisect.bisect_left(lv.o_minx, cam - lv.o_maxw - 20)
        hi = bisect.bisect_right(lv.o_minx, cam + W + 20)
        for j in range(lo, hi):
            o_min, o_max, poly, kind = lv.obst[j]
            if o_max - cam < -20:
                continue
            sp = [(x - cam, y) for x, y in poly]
            if kind == "spike":
                pygame.draw.polygon(s, mix(pal["spike"], (0, 0, 0), 0.45), sp)
                pygame.draw.polygon(s, pal["spike"], sp, 3)
            else:
                pygame.draw.polygon(s, mix(wall, pal["acc"], 0.12), sp)
                pygame.draw.polygon(s, pal["acc"], sp, 3)
                xs = [p[0] for p in sp]
                ys = [p[1] for p in sp]
                inner_r = pygame.Rect(min(xs) + 8, min(ys) + 8, max(xs) - min(xs) - 16, max(ys) - min(ys) - 16)
                if inner_r.w > 4 and inner_r.h > 4:
                    pygame.draw.rect(s, mix(wall, pal["acc"], 0.28), inner_r, 2)

        # текст «Попытка N» в мире
        tx = 110 - cam
        if tx > -400:
            draw_text(s, "Попытка %d" % self.attempt, 54, (255, 255, 255), (tx, CY - 110), "topleft")

        self.draw_trail(cam)
        if self.state not in ("dead",):
            self.draw_wave(cam)
        for p in self.particles:
            a = clamp(p[4] / p[5], 0, 1)
            sz = max(1, int(p[7] * a))
            pygame.draw.rect(s, p[6], (p[0] - cam - sz / 2, p[1] - sz / 2, sz, sz))
        if self.flash > 0:
            self.overlay.fill((255, 255, 255, int(120 * self.flash)))
            s.blit(self.overlay, (0, 0))

    def draw_trail(self, cam):
        pts = self.trail + [(self.px, self.py)]
        while len(pts) > 2 and pts[1][0] < self.px - TAIL_LEN - 50:   # отбрасываем невидимое начало
            pts.pop(0)
            if self.trail:
                self.trail.pop(0)
        base = mix(self.pal["top"], self.pal["bot"], 0.5)
        render_trail(self.screen, pts, self.px, cam, self.cfg_c("trail"), base)

    def draw_wave(self, cam):
        base = mix(self.pal["top"], self.pal["bot"], 0.5)
        self.blit_wave(self.screen, self.px - cam, self.py, self.anim, base)

    def draw_hud(self):
        s, pal = self.screen, self.pal
        pct = self.progress()
        bar = pygame.Rect(W // 2 - 190, 14, 380, 12)
        pygame.draw.rect(s, (10, 12, 28), bar.inflate(4, 4), border_radius=8)
        pygame.draw.rect(s, (40, 46, 80), bar, border_radius=6)
        if pct > 0.5:
            f = bar.copy()
            f.w = max(8, int(bar.w * pct / 100))
            pygame.draw.rect(s, pal["acc"], f, border_radius=6)
        draw_text(s, "%d%%" % int(pct), 22, (255, 255, 255), (bar.right + 14, 8))
        draw_text(s, "Попытка %d" % self.attempt, 20, (230, 235, 255), (16, 10), bold=False)
        rec = self.save.lv(self.level_idx)
        draw_text(s, "Рекорд: %d%%" % int(rec["best"]), 20, (230, 235, 255), (W - 16, 10), "topright", False)
        draw_text(s, "%d. %s" % (self.level_idx + 1, LEVELS[self.level_idx]["name"]), 16,
                  (170, 185, 225), (16, 36), bold=False)
        if self.audio.muted:
            draw_text(s, "звук выкл", 16, (255, 120, 120), (W - 16, 36), "topright", False)

    def dim(self, alpha=150):
        self.overlay.fill((4, 6, 18, alpha))
        self.screen.blit(self.overlay, (0, 0))

    def draw_pause(self):
        self.dim(160)
        s = self.screen
        draw_text(s, "ПАУЗА", 64, (255, 255, 255), (W // 2, 110), "center")
        mouse = pygame.mouse.get_pos()
        self.buttons = []
        items = [("Продолжить  (Esc)", "resume"), ("Заново  (R)", "restart"), ("В меню  (Q)", "menu")]
        for i, (label, act) in enumerate(items):
            r = pygame.Rect(W // 2 - 170, 175 + i * 62, 340, 50)
            self.buttons.append((r, act))
            self.draw_button(r, label, self.pal["acc"], r.collidepoint(mouse))
        draw_text(s, "Громкость музыки", 22, (225, 235, 255), (W // 2, 398), "center", False)
        self.vol_rect = pygame.Rect(W // 2 - 170, 436, 340, 14)
        self.draw_slider(self.vol_rect, self.audio.volume, self.pal["acc"])
        draw_text(s, "%d%%" % round(self.audio.volume * 100), 20, (255, 255, 255), (W // 2, 470), "center", False)
        draw_text(s, "колёсико мыши или  -  /  =  тоже меняют громкость", 15, (160, 175, 215),
                  (W // 2, 505), "center", False, None)

    def draw_dead(self):
        s = self.screen
        draw_text(s, "Крушение!  %d%%" % int(self.pct_died), 44, (255, 255, 255), (W // 2, 120), "center")
        rec = self.save.lv(self.level_idx)
        draw_text(s, "Рекорд: %d%%" % int(rec["best"]), 24, (220, 230, 255), (W // 2, 168), "center", False)

    def draw_win(self):
        self.dim(170)
        s, pal = self.screen, self.pal
        for c in self.confetti:
            pygame.draw.rect(s, c[4], (c[0], c[1], c[5], c[5] * 0.6))
        panel = pygame.Rect(W // 2 - 300, 70, 600, 400)
        pygame.draw.rect(s, (14, 18, 42), panel, border_radius=18)
        pygame.draw.rect(s, pal["acc"], panel, 3, border_radius=18)
        draw_text(s, "УРОВЕНЬ ПРОЙДЕН!", 48, pal["acc"], (W // 2, 118), "center")
        draw_text(s, "%d. %s" % (self.level_idx + 1, LEVELS[self.level_idx]["name"]), 26, (255, 255, 255),
                  (W // 2, 168), "center")
        rec = self.save.lv(self.level_idx)
        draw_text(s, "Попыток: %d" % rec["attempts"], 24, (225, 235, 255), (W // 2, 218), "center", False)
        draw_text(s, "Время: %.1f c   ·   лучшее: %.1f c" % (self.t, rec["best_time"] or self.t), 22,
                  (190, 205, 240), (W // 2, 252), "center", False)
        nxt = self.level_idx + 1
        if self.new_unlock is not None:
            draw_text(s, "Открыт уровень: %s" % LEVELS[nxt]["name"], 24, (255, 220, 90), (W // 2, 292), "center")
        elif nxt >= len(LEVELS):
            draw_text(s, "Вы прошли все уровни — вы МЕГА-ПРО!", 24, (255, 220, 90), (W // 2, 292), "center")
        mouse = pygame.mouse.get_pos()
        self.buttons = []
        items = [("Заново  (R)", "restart"), ("В меню  (Esc)", "menu")]
        if nxt < len(LEVELS):
            items.insert(0, ("Следующий уровень  (Enter)", "next"))
        for i, (label, act) in enumerate(items):
            r = pygame.Rect(W // 2 - 190, 326 + i * 46, 380, 40)
            self.buttons.append((r, act))
            self.draw_button(r, label, pal["acc"], r.collidepoint(mouse))

    def draw(self):
        self.vol_rect = None
        if self.state == "menu":
            self.draw_menu()
        elif self.state == "shop":
            self.draw_shop()
        else:
            self.draw_world()
            self.draw_hud()
            if self.state == "pause":
                self.draw_pause()
            elif self.state == "dead":
                self.draw_dead()
            elif self.state == "win":
                self.draw_win()
        if self.vol_popup > 0 and self.vol_rect is None:
            self.draw_vol_popup()

    # ──────────────────────────────────────────────────────────────────────────
    #  Громкость
    # ──────────────────────────────────────────────────────────────────────────
    def set_volume(self, v):
        v = clamp(round(v * 100) / 100.0, 0.0, 1.0)
        self.audio.set_volume(v)
        self.save.data["volume"] = v

    def change_volume(self, delta):
        self.set_volume(self.audio.volume + delta)
        self.vol_popup = 1.6
        self.save.write()

    def set_vol_x(self, x):
        if self.vol_rect is not None:
            self.set_volume((x - self.vol_rect.x) / self.vol_rect.w)

    def draw_slider(self, rect, value, color=(0, 230, 255)):
        s = self.screen
        col = (120, 125, 150) if self.audio.muted else color
        pygame.draw.rect(s, (14, 18, 40), rect.inflate(4, 4), border_radius=rect.h)
        pygame.draw.rect(s, (46, 52, 88), rect, border_radius=rect.h // 2)
        f = rect.copy()
        f.w = max(rect.h, int(rect.w * value))
        pygame.draw.rect(s, col, f, border_radius=rect.h // 2)
        kx = rect.x + int(rect.w * value)
        pygame.draw.circle(s, (255, 255, 255), (kx, rect.centery), rect.h + 1)
        pygame.draw.circle(s, col, (kx, rect.centery), rect.h + 1, 3)

    def draw_vol_popup(self):
        s = self.screen
        r = pygame.Rect(W // 2 - 140, H - 66, 280, 42)
        pygame.draw.rect(s, (10, 12, 30), r, border_radius=12)
        pygame.draw.rect(s, (0, 230, 255), r, 2, border_radius=12)
        draw_text(s, "Музыка", 18, (220, 230, 255), (r.x + 14, r.centery), "midleft", False, None)
        bar = pygame.Rect(r.x + 90, r.centery - 5, 120, 10)
        pygame.draw.rect(s, (46, 52, 88), bar, border_radius=5)
        f = bar.copy()
        f.w = max(0, int(bar.w * self.audio.volume))
        pygame.draw.rect(s, (120, 125, 150) if self.audio.muted else (0, 230, 255), f, border_radius=5)
        draw_text(s, "%d%%" % round(self.audio.volume * 100), 18, (255, 255, 255), (r.right - 12, r.centery),
                  "midright", False, None)

    # ──────────────────────────────────────────────────────────────────────────
    #  Иконка волны и магазин
    # ──────────────────────────────────────────────────────────────────────────
    R_BACK = pygame.Rect(16, 14, 150, 40)
    R_PREV = pygame.Rect(520, 80, 410, 150)
    R_SV = pygame.Rect(520, 306, 190, 150)
    R_HUE = pygame.Rect(722, 306, 22, 150)
    R_HEX = pygame.Rect(760, 306, 162, 34)
    R_RESET = pygame.Rect(30, 462, 210, 38)

    @staticmethod
    def skin_card(i):
        return pygame.Rect(30 + (i % 3) * 160, 90 + (i // 3) * 135, 150, 120)

    @staticmethod
    def slot_rect(k):
        return pygame.Rect(520 + k * 140, 246, 130, 40)

    @staticmethod
    def preset_rect(i):
        return pygame.Rect(760 + (i % 4) * 42, 350 + (i // 4) * 38, 36, 32)

    def cfg_c(self, key):
        return tuple(int(clamp(v, 0, 255)) for v in self.cfg[key])

    def blit_wave(self, surf, x, y, anim, bg, size=1.0, skin=None, glow=True):
        skin = self.cfg["skin"] if skin is None else skin
        c1, c2 = self.cfg_c("c1"), self.cfg_c("c2")
        img = self.skins.tinted(skin, c1, c2)
        spr = pygame.transform.rotozoom(img, anim.va, self.skins.scale(skin) * anim.scale() * size)
        if glow and bg is not None:
            pygame.draw.circle(surf, mix(bg, c1, 0.28), (int(x), int(y)), int(24 * size))
        surf.blit(spr, spr.get_rect(center=(int(x), int(y))))

    @staticmethod
    def make_hue():
        surf = pygame.Surface(Game.R_HUE.size)
        for y in range(surf.get_height()):
            c = colorsys.hsv_to_rgb(y / surf.get_height(), 1.0, 1.0)
            pygame.draw.line(surf, (int(c[0] * 255), int(c[1] * 255), int(c[2] * 255)), (0, y), (surf.get_width(), y))
        return surf

    @staticmethod
    def make_sv(h):
        w, hh = Game.R_SV.size
        surf = pygame.Surface((w, hh))
        for x in range(w):
            c = colorsys.hsv_to_rgb(h, x / (w - 1), 1.0)
            pygame.draw.line(surf, (int(c[0] * 255), int(c[1] * 255), int(c[2] * 255)), (x, 0), (x, hh))
        shade = pygame.Surface((w, hh), pygame.SRCALPHA)
        for y in range(hh):
            pygame.draw.line(shade, (0, 0, 0, int(255 * y / (hh - 1))), (0, y), (w, y))
        surf.blit(shade, (0, 0))
        return surf

    def load_hsv(self):
        r, g, b = self.cfg_c(SLOTS[self.slot])
        h, sat, v = colorsys.rgb_to_hsv(r / 255.0, g / 255.0, b / 255.0)
        if sat < 0.01 or v < 0.01:
            h = self.hsv[0]
        self.hsv = (h, sat, v)
        self.sync_hex()

    def sync_hex(self):
        if not self.hex_focus:
            self.hex_text = "%02X%02X%02X" % self.cfg_c(SLOTS[self.slot])

    def apply_hex(self):
        if len(self.hex_text) == 6:
            t = self.hex_text
            self.cfg[SLOTS[self.slot]] = [int(t[0:2], 16), int(t[2:4], 16), int(t[4:6], 16)]
            self.load_hsv()
            self.save.write()

    def shop_drag(self, pos):
        h, sat, v = self.hsv
        if self.drag == "sv":
            r = self.R_SV
            sat = clamp((pos[0] - r.x) / r.w, 0.0, 1.0)
            v = 1.0 - clamp((pos[1] - r.y) / r.h, 0.0, 1.0)
        else:
            r = self.R_HUE
            h = clamp((pos[1] - r.y) / r.h, 0.0, 0.999)
        self.hsv = (h, sat, v)
        c = colorsys.hsv_to_rgb(h, sat, v)
        self.cfg[SLOTS[self.slot]] = [int(round(c[0] * 255)), int(round(c[1] * 255)), int(round(c[2] * 255))]
        self.hex_focus = False
        self.sync_hex()

    def act_shop(self):
        self.state = "shop"
        self.slot, self.hex_focus, self.drag = 0, False, None
        self.pv_dir = 1
        self.pv_anim.reset(1)
        self.load_hsv()

    def act_shop_back(self):
        self.hex_focus = False
        self.save.write()
        self.state = "menu"

    def on_shop(self, e):
        if e.type == pygame.KEYDOWN:
            if self.hex_focus:
                if e.key in (pygame.K_RETURN, pygame.K_KP_ENTER, pygame.K_ESCAPE):
                    self.hex_focus = False
                    self.sync_hex()
                elif e.key == pygame.K_BACKSPACE:
                    self.hex_text = self.hex_text[:-1]
                else:
                    ch = e.unicode.upper()
                    if ch and ch in "0123456789ABCDEF" and len(self.hex_text) < 6:
                        self.hex_text += ch
                        self.apply_hex()
                return
            if e.key == pygame.K_ESCAPE:
                self.act_shop_back()
            elif e.key == pygame.K_TAB:
                self.slot = (self.slot + 1) % 3
                self.load_hsv()
            elif e.key in (pygame.K_RIGHT, pygame.K_LEFT):
                self.cfg["skin"] = (self.cfg["skin"] + (1 if e.key == pygame.K_RIGHT else -1)) % len(SKIN_NAMES)
                self.audio.play_sfx("click")
                self.save.write()
        elif e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
            p = e.pos
            if self.hex_focus and not self.R_HEX.collidepoint(p):
                self.hex_focus = False
                self.sync_hex()
            if self.R_BACK.collidepoint(p):
                self.audio.play_sfx("click")
                self.act_shop_back()
                return
            for i in range(len(SKIN_NAMES)):
                if self.skin_card(i).collidepoint(p):
                    self.cfg["skin"] = i
                    self.audio.play_sfx("click")
                    self.save.write()
                    return
            for k in range(3):
                if self.slot_rect(k).collidepoint(p):
                    self.slot = k
                    self.load_hsv()
                    self.audio.play_sfx("click")
                    return
            if self.R_SV.collidepoint(p):
                self.drag = "sv"
                self.shop_drag(p)
            elif self.R_HUE.inflate(8, 0).collidepoint(p):
                self.drag = "hue"
                self.shop_drag(p)
            elif self.R_HEX.collidepoint(p):
                self.hex_focus = True
                self.hex_text = ""
            elif self.R_RESET.collidepoint(p):
                for k, v in DEFAULT_WAVE.items():
                    self.cfg[k] = list(v) if isinstance(v, list) else v
                self.load_hsv()
                self.audio.play_sfx("click")
                self.save.write()
            else:
                for i, c in enumerate(PRESETS):
                    if self.preset_rect(i).collidepoint(p):
                        self.cfg[SLOTS[self.slot]] = list(c)
                        self.load_hsv()
                        self.audio.play_sfx("click")
                        self.save.write()
                        return

    def draw_shop(self):
        s, t = self.screen, self.time
        s.blit(self.menu_bg, (0, 0))
        mouse = pygame.mouse.get_pos()
        draw_text(s, "Магазин", 44, (255, 255, 255), (W // 2, 34), "center")
        self.draw_button(self.R_BACK, "← Назад", (0, 230, 255), self.R_BACK.collidepoint(mouse))

        # карточки иконок
        for i in range(len(SKIN_NAMES)):
            r = self.skin_card(i)
            sel = self.cfg["skin"] == i
            body = (32, 42, 92) if sel else ((30, 36, 76) if r.collidepoint(mouse) else (24, 28, 60))
            pygame.draw.rect(s, body, r, border_radius=14)
            pygame.draw.rect(s, (0, 230, 255) if sel else (70, 80, 120), r, 4 if sel else 2, border_radius=14)
            self.blit_wave(s, r.centerx, r.y + 52, STATIC_ANIM, None, 2.3, i, False)
            draw_text(s, SKIN_NAMES[i], 20, (255, 255, 255) if sel else (180, 190, 220),
                      (r.centerx, r.bottom - 22), "center", True, None)

        # живое превью: волна ходит зигзагом, иконка плавно наклоняется
        pv = self.R_PREV
        base = (10, 12, 30)
        pygame.draw.rect(s, base, pv, border_radius=14)
        A = 34.0
        hx = t * 190.0
        d = -1 if (hx % (4 * A)) < 2 * A else 1
        if d != self.pv_dir:
            self.pv_dir = d
            self.pv_anim.turn()
        self.pv_anim.update(self.dt, d)

        def path_y(x):
            u = (x % (4 * A)) / (4 * A)
            return pv.centery + A * (4 * abs(u - 0.5) - 1)

        x = math.floor((hx - TAIL_LEN - 80) / (2 * A)) * 2 * A
        pts = []
        while x < hx:
            pts.append((x, path_y(x)))
            x += 2 * A
        pts.append((hx, path_y(hx)))
        cam = hx - pv.centerx
        s.set_clip(pv.inflate(-4, -4))
        for gx in range(int(pv.x - cam % 40), pv.right + 40, 40):
            pygame.draw.line(s, (20, 24, 52), (gx, pv.y), (gx, pv.bottom))
        render_trail(s, pts, hx, cam, self.cfg_c("trail"), base)
        self.blit_wave(s, pv.centerx, path_y(hx), self.pv_anim, base, 1.5)
        s.set_clip(None)
        pygame.draw.rect(s, (70, 80, 120), pv, 2, border_radius=14)

        # выбор слота цвета
        for k in range(3):
            r = self.slot_rect(k)
            active = self.slot == k
            pygame.draw.rect(s, (28, 34, 72) if active else (22, 26, 56), r, border_radius=10)
            pygame.draw.rect(s, (255, 255, 255) if active else (70, 80, 120), r, 3 if active else 2, border_radius=10)
            sw = pygame.Rect(r.x + 8, r.y + 8, 24, 24)
            pygame.draw.rect(s, self.cfg_c(SLOTS[k]), sw, border_radius=6)
            pygame.draw.rect(s, (255, 255, 255), sw, 1, border_radius=6)
            draw_text(s, SLOT_NAMES[k], 19, (255, 255, 255), (r.x + 42, r.centery), "midleft", True, None)

        # палитра
        hk = int(self.hsv[0] * 360)
        if self._sv[0] != hk:
            self._sv = (hk, self.make_sv(hk / 360.0))
        s.blit(self._sv[1], self.R_SV.topleft)
        pygame.draw.rect(s, (255, 255, 255), self.R_SV, 2)
        mx = int(self.R_SV.x + self.hsv[1] * self.R_SV.w)
        my = int(self.R_SV.y + (1 - self.hsv[2]) * self.R_SV.h)
        pygame.draw.circle(s, (0, 0, 0), (mx, my), 9, 2)
        pygame.draw.circle(s, (255, 255, 255), (mx, my), 7, 2)
        s.blit(self._hue, self.R_HUE.topleft)
        pygame.draw.rect(s, (255, 255, 255), self.R_HUE, 2)
        hy = int(self.R_HUE.y + self.hsv[0] * self.R_HUE.h)
        pygame.draw.rect(s, (255, 255, 255), (self.R_HUE.x - 4, hy - 3, self.R_HUE.w + 8, 6), 2, border_radius=3)

        draw_text(s, "HEX-код: клик и ввод", 14, (170, 185, 225), (760, 290), "topleft", False, None)
        pygame.draw.rect(s, (14, 18, 40), self.R_HEX, border_radius=8)
        pygame.draw.rect(s, (0, 230, 255) if self.hex_focus else (70, 80, 120), self.R_HEX, 2, border_radius=8)
        caret = "|" if self.hex_focus and int(t * 2) % 2 == 0 else ""
        draw_text(s, "#" + self.hex_text + caret, 20, (255, 255, 255), (self.R_HEX.x + 10, self.R_HEX.centery),
                  "midleft", True, None)
        cur = self.cfg_c(SLOTS[self.slot])
        for i, c in enumerate(PRESETS):
            r = self.preset_rect(i)
            pygame.draw.rect(s, c, r, border_radius=6)
            pygame.draw.rect(s, (255, 255, 255) if c == cur else (70, 80, 120), r, 3 if c == cur else 1, border_radius=6)

        # громкость и сброс
        draw_text(s, "Громкость музыки", 20, (220, 230, 255), (30, 380), "topleft", False, None)
        self.vol_rect = pygame.Rect(30, 420, 300, 12)
        self.draw_slider(self.vol_rect, self.audio.volume)
        draw_text(s, "%d%%" % round(self.audio.volume * 100), 18, (255, 255, 255), (352, 426), "midleft", False, None)
        self.draw_button(self.R_RESET, "Сбросить цвета", (255, 120, 120), self.R_RESET.collidepoint(mouse))
        draw_text(s, "Tab — следующий цвет  ·  ← → — смена иконки  ·  Esc — назад  ·  колёсико / -  = — громкость",
                  14, (150, 165, 205), (W // 2, H - 20), "center", False, None)

    # --- главный цикл ---
    def run(self):
        while True:
            dt = min(self.clock.tick(FPS) / 1000.0, 0.05)
            for e in pygame.event.get():
                self.handle(e)
            self.update(dt)
            self.draw()
            pygame.display.flip()


# ──────────────────────────────────────────────────────────────────────────────
#  Данные иконок (слои PNG, base64)
# ──────────────────────────────────────────────────────────────────────────────
SKIN_DATA = [
    (
        "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"
    ),
    (
        "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"
    ),
    (
        "iVBORw0KGgoAAAANSUhEUgAAAGoAAABQCAIAAAB+oncLAAAFSElEQVR42u2dIXTbVhSGP+UYyCwai5lVZrOqLB6Kyrqhpawdy1jP"
        "WMI2mAyOpWwtiwfD7KAlbAqqAx20mE1BtZgGVKuWZSlPek+yPOmeHJ1nO3qWft3//vc93Sdr8CsKbBeMRdsDfemjzb504ZHCrKWi"
        "kx+gT6XtA9wX0e+OdA+9ymMHfFdQv/Lw2WyBGdWEr1vckW2FSca+TvQSzy1mQdtFN/DCj8p/OcasPnwR1zvCOeXbiviFhl/Ct+wo"
        "hM/ErRt5JeHTG/hkzKPetqOwL6N+aKqEz41yuW6JSzf70FKvOXkD+F6BtV3H7XDuolvMDE6EM/z7IuDbLQG7IRdjTIe9ID6GyW16"
        "w2ZqM7X5caW313wa0g8yzXPRQ3gLLozhTml2yR/wVklfIz7ETzXwlBcc5ZWj+d+8N/l5+c1v+OzSDto+Wsa0eQ4OOEomsqKjDn/O"
        "YtQlZnto7SeVV2b85NKeYpixNyVOuQ0DGMAEHElGrwzaZvAxy+5vWIImSXkroci+i7Yyu9GHPjyAA7e54ZNJ1nQxAi59he/AZEm+"
        "kxo2Wkcpfr/j98BCM2OzHh2w4QYmWRndkks+PDEC6pFXQnwpIgO/gzv8XRhAbznsQBtssCG4uvf5yFuIRWPixon8CJdwiX8A/Rij"
        "LbDEGS0Jny4yaHNXs+6K2BVc4T+Hfm5GS8LniUiEpPcVPJS+hVv8PbDQrJhGh4x21uYkrRLcQdL7ShHuGVziX0IKo6cwWWF0q4Rg"
        "VLHYJ8LotRptggkDcOBmLXmznptemPdtFuVAo9cy2lgw+hquWnLpgpfZ+zR7S+5thoy+/kJebWWoM1jrfd0EmGYZSVqxUYdUohNq"
        "tBVN5jtR6dA6adMH/vsYiLoITJL3QCoziR1o9HO0rzULO1mijJ2PvIfcHTLJd8gXDC1+qhijI8p7D3NE5jA0M9+9U4OTC9FJzerb"
        "srfpQez7DfbBSKi4MGksQTlD6bhJ/qdfJAdt/2NTeZ+3HnfaPIXw1dD0Br6qkLeBT50n10Rti5KOeihvYbGvfjUuehP7pMjXwLfJ"
        "2FdD6VAZ+2ooHYXlfc2grbFm0LY9iUvNi3O/zvd1oQ0G6Isap3ArGghqmLgE8L1TsrKvnoO2PVHs/Glu5T3hr2f8q+Fn+nvBP2eM"
        "Kp64iMUvfw7jfN8x5OKMwTS7gzt0TrAdzitO3hAjF5yE8Le2TksI+qlcZKhMOrm7qBWKwOdFDjXtnlFO6dj+dLoLFlr8mQNzlRVW"
        "SdIRrW2+hiuBzt7ECpw2Yj2wY/VqgT3AnyqLc8Uq6z1VV6VgnvZhP1YWtIhGOMHymi2obS6X+13ox4rSvlAV7uB6WQNU1jaLnX9l"
        "6/t6sJ+wGsJdLolMkQ4pFVfqfV5leDpJKbEvozi3qpX1KTwlpRw8Oe8rQXkrkcSsLV0OeToRyw1UwyemvO3kddfrY59S5d0HKyER"
        "eYKnhcMn5JWalXX5sCLlfSXJ0yT4vMiZchB1jfStUeL5y9ka7IKFvVcyvUalQzOCgnG1ZuW6sIvrOS/g8TBSi1DLlo5DXp8yWlkU"
        "nf4oqvCdU8YrS8kBm2nQ2xFO5kmcLAsmReC7h6mSCtwUkh7z8ljddRrx7IyRwfyI74V3GudYrivofR+hlzBTn761NvUAumNeZtzj"
        "pojDCMmb7/kSZs2f39fcqGzg21r4moUJUlbDhQmFkdehUzf4JNPmh+WEcUgPRkG6++Q2ILtgI8d2K+CbrXhf3RxwR9r7GuXNb49w"
        "vQ2nOa+sdDjFHZw67MYFda0p+sGJg4yD5fQtAg3B7QweivvNif8AOR7uP/yJ5bsAAAAASUVORK5CYII="
    ),
    (
        "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"
        "/SdFjDwAAAAASUVORK5CYII="
    ),
    (
        "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"
    ),
]


if __name__ == "__main__":
    Game().run()
