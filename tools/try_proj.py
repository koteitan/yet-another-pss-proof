#!/usr/bin/env python3
"""G_u / proj_u / nrm を手で試す小道具。

内部表現は valnorm/wfe_explore と同じ（木 = 主項レコード (0,a,b) の c-spine タプル、葉 = ()）。

使い方:
  # 木を D 記法で（D_a も Da も可、+ で兄弟、0 で葉）
  python3 try_proj.py "D3(D3(D0(0))+D3(D4(0)))" 3
  python3 try_proj.py "D1(D2(0))"            # u 省略時は u=0
  # 数列から translate
  python3 try_proj.py --seq "(0,0)(1,1)(2,2)(1,1)(2,2)" 0
  # G_u を u=0..N まで一覧
  python3 try_proj.py "D1(D5(0))+D3(D4(0))" --gtable 5
"""
import sys, re
sys.path.insert(0, '.'); sys.setrecursionlimit(1000000)
from valnorm import nrm, lt_term, fmtb
try:
    from valnorm import conv
    from wfe_explore import translate
    HAVE_SEQ = True
except Exception:
    HAVE_SEQ = False

Z = ()

# ---- D 記法パーサ -> 内部タプル -------------------------------------------
def parse(s):
    s = s.replace(' ', '').replace('D_', 'D').replace('_', '')
    pos = 0
    def peek():
        return s[pos] if pos < len(s) else ''
    def term():
        # 主項の和（+ 連結）。先頭が 0 単独なら葉。
        nonlocal pos
        out = ()
        while True:
            if peek() == '0':
                pos += 1            # 葉 0（和の項としては寄与なし）
            elif peek() == 'D':
                pos += 1
                m = re.match(r'\d+', s[pos:]); a = int(m.group()); pos += m.end()
                assert peek() == '(', f"expected ( at {pos}"
                pos += 1
                b = term()
                assert peek() == ')', f"expected ) at {pos}"
                pos += 1
                out = out + ((0, a, b),)
            else:
                break
            if peek() == '+':
                pos += 1; continue
            break
        return out
    t = term()
    assert pos == len(s), f"trailing input at {pos}: {s[pos:]}"
    return t

# ---- G_u / 違反子 / proj_u -------------------------------------------------
def Glist(u, x):
    if x == (): return []
    a = x[0][1]; b = x[0][2]; c = tuple(x[1:])
    head = ([b] + Glist(u, b)) if u <= a else []
    return head + Glist(u, c)

def violators(u, t):
    return [g for g in Glist(u, t) if not lt_term(g, t)]

def maxo(x, ys):
    m = x
    for y in ys:
        if lt_term(m, y): m = y
    return m

def proj(u, x):
    bb = x; steps = []
    while True:
        gs = [g for g in Glist(u, bb) if not lt_term(g, bb)]
        if not gs: break
        m = maxo(gs[0], gs[1:])
        steps.append((fmtb(bb), [fmtb(g) for g in gs], fmtb(m)))
        bb = m
    return bb, steps

def parse_seq(s):
    return [(int(a), int(b)) for a, b in re.findall(r'\((\d+),(\d+)\)', s)]

# ---- CLI -------------------------------------------------------------------
def main():
    args = sys.argv[1:]
    if not args:
        print(__doc__); return
    gtable = None
    if '--gtable' in args:
        i = args.index('--gtable'); gtable = int(args[i+1]); del args[i:i+2]
    if args and args[0] == '--seq':
        if not HAVE_SEQ:
            print("translate 不可（wfe_explore 読み込み失敗）"); return
        seq = parse_seq(args[1]); T = conv(translate(seq))
        u = int(args[2]) if len(args) > 2 else 0
        print(f"sequence    = {seq}")
        print(f"translate   = {fmtb(T)}")
    else:
        T = parse(args[0])
        u = int(args[1]) if len(args) > 1 else 0
        print(f"tree        = {fmtb(T)}")
    print(f"nrm(tree)   = {fmtb(nrm(T))}")
    if gtable is not None:
        for uu in range(gtable + 1):
            print(f"G_{uu}       = {[fmtb(g) for g in Glist(uu, T)]}")
        return
    print(f"--- u = {u} ---")
    print(f"G_{u}(T)      = {[fmtb(g) for g in Glist(u, T)]}")
    viol = violators(u, T)
    print(f"{u}-violators  = {[fmtb(g) for g in viol]}   (空なら proj は不発)")
    res, steps = proj(u, T)
    for i, (b, gs, m) in enumerate(steps):
        print(f"  step{i}: {b}  violators={gs}  -> {m}")
    print(f"proj_{u}(T)   = {fmtb(res)}")

if __name__ == '__main__':
    main()
