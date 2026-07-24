#!/usr/bin/env python3
"""FINAL tractability test: does the olt x b induction CLOSE on the ST_PS class?

For the BMOCF <_M^Next structural induction to be tractable, the equal-lead
recursion of olt x b must stay INSIDE the class where the IH applies.  Concretely
the lean residual is:
    P:  for b = translate of an ST_PS descendant block,
        forall x in Gterm 0 b, olt x b.
The natural induction (on the term / on the <_M^Next chain) reduces, at an
equal-lead head-0 step, to the SAME statement about (arg x, arg b).  The induction
CLOSES iff at every such reduction the sub-pair (arg x, arg b) is again an
instance of P, i.e. arg b is again translate-of-ST_PS-block and arg x in
Gterm 0 (arg b).

We test, over the real corpus, whether the hard-class arg-descent stays within
the legal class (closure of the induction), vs escaping it (open induction =>
difficulty relocates).
"""
import sys
sys.path.insert(0, '.')
from fast_pss import diagSeq, Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from probe_bmocf_ancestor import enum_depth
from probe_bmocf_core import Gterm, lead

def all_subterms(t):
    if t == (): return
    yield t
    a, b, c = t
    yield from all_subterms(b); yield from all_subterms(c)

def main():
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        frag = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)]
        md = max(seen.values())

        # The set of "legal arguments" B = { b : b = translate(K), K SubBlock of
        # some host's descendant block } -- approximated by all head-0 / head-1
        # argument subterms appearing in the corpus (the translate-derived class).
        legal = set()
        for M in frag:
            for st in all_subterms(translate(M)):
                legal.add(st)
        legal.discard(())

        # walk hard-class pairs; simulate the equal-lead arg-descent and check at
        # each step that the descended pair stays legal AND remains a Gterm-0
        # membership instance.
        steps_total = closes = escapes_legal = escapes_gterm = 0
        ex_escape = []
        for M in frag:
            for st in all_subterms(translate(M)):
                a, b, c = st
                if a != 0: continue
                for x in Gterm(0, b):
                    if x == b or lead(x) != lead(b): continue
                    # equal-lead descent: while leads equal, recurse args
                    cx, cb = x, b
                    while cx != () and cb != () and cx[0] == cb[0] and cx[1] != cb[1]:
                        steps_total += 1
                        ax, ab = cx[1], cb[1]   # args
                        # check induction-closure conditions on (ax, ab):
                        # (1) ab must be legal (translate-of-block) for IH
                        if ab not in legal:
                            escapes_legal += 1
                            if len(ex_escape) < 6:
                                ex_escape.append(('legal', b, x, ab, ax))
                        # (2) ax must be in Gterm 0 ab for the SAME statement
                        elif ax not in set(Gterm(0, ab)) and ax != ab:
                            escapes_gterm += 1
                            if len(ex_escape) < 6:
                                ex_escape.append(('gterm', b, x, ab, ax))
                        else:
                            closes += 1
                        cx, cb = ax, ab
        print(f'[closure+{rounds}] maxdepth={md} frag={len(frag)} legal-class={len(legal)}')
        print(f'  hard-class equal-lead descent steps: {steps_total}')
        print(f'    step stays in legal IH class (closes): {closes}')
        print(f'    step ESCAPES legal class (ab not translate-of-block): {escapes_legal}')
        print(f'    step ab legal but ax NOT in Gterm0 ab (stmt changes): {escapes_gterm}')
        for tag, b, x, ab, ax in ex_escape[:6]:
            print(f'    ESC[{tag}] b={tfmt(b)[:34]} x={tfmt(x)[:30]} '
                  f'-> ab={tfmt(ab)[:30]} ax={tfmt(ax)[:24]}')

if __name__ == '__main__':
    main()
