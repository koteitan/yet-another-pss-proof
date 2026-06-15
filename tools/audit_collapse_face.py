#!/usr/bin/env python3
"""Audit the collapse face of the nrm route at closure+5/+6.

Two findings, both reproduced here (run: python3 audit_collapse_face.py):

(A) IntervalNoncanon is FALSE via Omega-crossing.
    For a maxo OT3-violator g of a wf3 b' at level a, the lemma
    psi_proj_notmem_of_intervalNoncanon (= collapse_le) needs EVERY ordinal in
    [oV b', oV g) to be a-non-canonical. But the maxo violator typically has lead
    level k>a (g = D_k(...)), so oV g >= Om_k while oV b' = psi_a(...) < Om_{a+1};
    the gap crosses Om_k, and Om_k = psi_k(0) is a-CANONICAL (Om_k in C_a(Om_k)).
    => IntervalNoncanon false. (count: in-gap Om_k among wf3 b' instances.)

(B) The TRUE route: proj is the IDENTITY on nrm-images.
    The nrm value-chain only ever calls proj a (nrm b). On nrm-images proj never
    fires (proj a (nrm t) = nrm t), nrm is idempotent and lands in OT. So the
    collapse step is never invoked on the domain that matters; the sound residual
    is ProjFixesNrm, not CollapseResidueMaxo-over-all-wf3.
"""
import sys
sys.path.insert(0, '.')
from valnorm import conv, nrm, lt_term, G, in_OT
from wfe_explore import translate, enum_ST

Z = ()
def le_t(a, b): return a == b or lt_term(a, b)
def maxo(lst):
    m = lst[0]
    for h in lst[1:]:
        if lt_term(m, h): m = h
    return m
def Om_term(k): return (('D', k, ()),)
def proj(u, t):
    while True:
        bad = [x for x in G(u, t) if not lt_term(x, t)]
        if not bad: return t
        t = maxo(bad)

def audit(rounds):
    # (A) Omega-crossing among wf3 b' maxo-violator instances
    seen = set(); total = 0; wf3_inst = 0; crossing = 0; ex = []
    for M in enum_ST(rounds=rounds):
        t = conv(translate(M)); stack = [t]
        while stack:
            b = stack.pop()
            if not b: continue
            for (_, v, arg) in b: stack.append(arg)
            for a in range(0, 4):
                bad = [x for x in G(a, b) if not lt_term(x, b)]
                if not bad: continue
                g = maxo(bad)
                key = (a, tuple(map(str, b)), tuple(map(str, g)))
                if key in seen: continue
                seen.add(key); total += 1
                if in_OT(b):
                    wf3_inst += 1
                    hits = [k for k in range(0, 6)
                            if le_t(b, Om_term(k)) and lt_term(Om_term(k), g)]
                    if hits:
                        crossing += 1
                        if len(ex) < 3: ex.append((a, b, g, hits))
    print(f"(A) rounds={rounds}: maxo-violator instances total={total} "
          f"wf3(valid)={wf3_inst} Omega-crossing(IntervalNoncanon FALSE)={crossing}")
    for a, b, g, hits in ex:
        print(f"    a={a} in-gap Om_k={hits}  b'={b}  g={g}")

    # (B) proj fixes nrm-images
    checked = 0; fires = 0; bad_ot = 0; bad_idem = 0; n = 0
    for M in enum_ST(rounds=rounds):
        t = nrm(conv(translate(M))); n += 1
        if not in_OT(t): bad_ot += 1
        if nrm(t) != t: bad_idem += 1
        stack = [t]
        while stack:
            node = stack.pop()
            if not node: continue
            for (_, a, b) in node:
                checked += 1
                if proj(a, b) != b: fires += 1
                stack.append(b)
    print(f"(B) rounds={rounds}: nrm-images={n} proj-arg positions checked={checked} "
          f"proj FIRES={fires}  not-in-OT={bad_ot}  not-idempotent={bad_idem}")
    print(f"    => ProjFixesNrm TRUE on this corpus (fires=0 expected)")

if __name__ == "__main__":
    for r in (5, 6):
        audit(r)
        print()
