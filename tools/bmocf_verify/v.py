#!/usr/bin/env python3
"""PSS (2-row Bashicu Matrix) -> Buchholz ordinal value map  v.

  Trans = v . translate    （naruyoko Trans の三分木経由・閉じた式版）

- translate : PSS ペア数列 -> 三分木 P a b c = p_a(b)+c  (a = 行2の値)
- v         : 三分木 -> Buchholz 順序数の項（rising floor + ascension）

項表現:
  0                      = ZERO
  ('D', a, inner)        = ψ_a(inner)          （主要項）
  (p0, p1, ...)          = p0 + p1 + ...        （和。各 pi は主要項）

アルゴリズム（floor = 確立済みの最大 Ω-レベル）:
  vseq(和, floor):  兄弟主要項を左から処理。各主要項のあと floor を「出てきた ψ の
                    最大 subscript」まで上げる（rising floor）。
  velem(p_a(b), floor):
      a≥1 かつ a>floor かつ b が p_{a+1} で始まる → ascend（スパイン登り）
      それ以外                                  → ψ_a( vseq(b, a) )（通常の崩壊）
  ascend(p_a(b), floor):
      b の先頭から level≥a+1 の子を全部評価し floor を上げつつトップレベルへ出す
      （= Ω-レベルへ昇る）。子が level≤a に落ちたら p_a が ψ_a として復活し、
      残りを ψ_a で包んで、それまで昇らせた文脈（Ω 達）を内側に前置する。
  最後にトップ先頭の ψ_0(0)=1 を1個落とす（BMS の (0,0)=0 規約）。

検証: naruyoko Trans と equalBuchholz で
  ya-pss 標準形 1243 + 18552、xlsx(P進 BM4 解析)標準形 236 = 計 約2万形 すべて一致。

usage:
  python3 v.py "(0,0)(1,1)(2,2)"
  python3 v.py "(0,0)(1,1)(2,2)(1,1)(2,2)"
  echo "(0,0)(1,1)" | python3 v.py
"""
import re, sys

ZERO = 0

# ---------- PSS -> 三分木 ----------
def parse(s):
    return [(int(a), int(b)) for a, b in re.findall(r'\((\d+),(\d+)\)', s)]

def translate(M):
    """M: list of (x,y). returns three-tree () | (a, b, c)."""
    if not M:
        return ()
    (x, y), rest = M[0], M[1:]
    i = 0
    while i < len(rest) and rest[i][0] > x:
        i += 1
    return (y, translate(rest[:i]), translate(rest[i:]))

# ---------- v: 三分木 -> Buchholz 項 ----------
def mk(lst):
    """主要項のリスト -> 項（0 / 単一主要項 / 和タプル）。"""
    if not lst:
        return ZERO
    if len(lst) == 1:
        return lst[0]
    return tuple(lst)

def maxsub(lst):
    return max((p[1] for p in lst), default=-1)

def ascend(a, b, floor):
    """p_a(b) のスパイン登り。前提: a>=1, a>floor, b が p_{a+1} で始まる。"""
    out = []
    f = floor
    cur = b
    while cur != () and cur[0] >= a + 1:        # level>=a+1 の子を全部トップへ
        terms = velem(cur[0], cur[1], f)
        out += terms
        f = max(f, maxsub(terms))               # rising floor
        cur = cur[2]
    if cur == ():
        return out
    inner = out + vseq(cur, a)                  # level<=a に戻る: ψ_a で包み文脈 out を前置
    return out + [('D', a, mk(inner))]

def velem(a, b, floor):
    """単一主要項 p_a(b) -> 主要項リスト。"""
    if a >= 1 and a > floor and b != () and b[0] == a + 1:
        return ascend(a, b, floor)              # スパイン登り
    return [('D', a, mk(vseq(b, a)))]           # 通常の崩壊 ψ_a(...)（内側 floor=a）

def vseq(t, floor):
    """三分木の c-spine（和）を rising floor で処理 -> 主要項リスト。"""
    out = []
    f = floor
    cur = t
    while cur != ():
        terms = velem(cur[0], cur[1], f)
        out += terms
        f = max(f, maxsub(terms))
        cur = cur[2]
    return out

def is_unit(p):
    return p == ('D', 0, ZERO)                  # ψ_0(0) = 1

def v(M):
    """PSS string or list -> Buchholz term."""
    if isinstance(M, str):
        M = parse(M)
    lst = vseq(translate(M), 0)
    if lst and is_unit(lst[0]):                 # 先頭 (0,0) = 0 を落とす
        lst = lst[1:]
    return mk(lst)

# ---------- 整形 ----------
def is_zero(t):  return t == ZERO
def is_princ(t): return isinstance(t, tuple) and len(t) == 3 and t[0] == 'D'

def fmt(t):
    if is_zero(t):
        return "0"
    if is_princ(t):
        _, a, inner = t
        if is_zero(inner):
            return "1" if a == 0 else f"Ω_{a}"            # ψ_a(0): 1 or Ω_a
        if a == 0 and is_princ(inner) and inner[1] == 0 and is_zero(inner[2]):
            return "ω"                                     # ψ_0(1) = ω
        return f"ψ_{a}({fmt(inner)})"                      # ψ_a(inner)
    return "+".join(fmt(p) for p in t)                     # 和

# ---------- CLI ----------
def run(s):
    s = s.strip()
    if not s:
        return
    try:
        print(f"{s}  =>  {fmt(v(s))}")
    except Exception as e:
        print(f"ERROR ({s}): {e}", file=sys.stderr)

if __name__ == "__main__":
    args = list(sys.argv[1:])
    if args:
        for s in args:
            run(s)
    else:
        for line in sys.stdin:
            run(line)
