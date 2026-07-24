#!/usr/bin/env python3
"""DECISIVE: SubBlock-derivation route for olt(translate K)(translate B).

Faithful object: (0,0)::B in ST_PS row1<=1, K a Gterm-0 WITNESS of translate B
(i.e. translate K in Gterm0(translate B)).  We test:

T1. depth table dB vs dK (blockok depth = head row0 of the block).
T2/T3. Is olt(translate K)(translate B) composable along the SubBlock derivation
   (desc/sib constructor steps)?  We analyse each immediate constructor step:
     desc-step: B=p::rest, child=rest.takeWhile(p.1<.); translate(child)=ARG of translate B.
     sib-step:  B=p::rest, child=rest.dropWhile(p.1<.); translate(child)=TAIL of translate B.
   For a clean derivation-induction we'd want a carrier P(B,K) with
     P(child,K) => P(B,K)  at each step, P=olt at base.
   Adversarial checks:
     (D1) desc transitivity: is olt(translate child)(translate B) ALWAYS true?
          (if yes, olt(tK,tchild) -> olt(tK,tB) by trans; if NO, this route dies here)
     (D2) sib transitivity:  is olt(translate child)(translate B) ALWAYS true for sib?
     If D1/D2 false, the naive 'compose to parent' carrier is dead. Then test the
     REFINED carrier that the seqlex engine suggests:
     (S1) seqlex carrier: shift K so its head row0 = dB, then check
          seqlex(shift(K, dB-dK), B-suffix)?  We instead test the cleaner:
          (S2) olt(tK,tB) <-> seqlex( pad, ... ) -- but first just measure whether
          there's ANY fixed depth-shift delta = dB-dK making blockok aligned.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth

Z = ()
def Gterm(u,t):
    if t==(): return []
    a,b,c=t; out=[]
    if u<=a: out.append(b); out+=Gterm(u,b)
    out+=Gterm(u,c); return out

def head_row0(B):
    return B[0][0] if B else None

def all_subblocks(B):
    """list of (K, derivation) where derivation is a list of ('desc'|'sib', child_block)."""
    res = []
    def rec(seg, deriv):
        seg = tuple(seg)
        res.append((seg, list(deriv)))
        if not seg: return
        (x,y) = seg[0]; rest = seg[1:]
        i=0
        while i < len(rest) and rest[i][0] > x: i += 1
        desc = tuple(rest[:i]); sib = tuple(rest[i:])
        rec(desc, deriv+[('desc', desc, seg)])
        rec(sib,  deriv+[('sib',  sib,  seg)])
    rec(tuple(B), [])
    return res

def main():
    for rounds in (5,6):
        seen = enum_depth(4,(1,2,3),28,rounds)
        hosts = [M for M in seen if Lng(M)<=18 and all(c[1]<=1 for c in M)
                 and M and M[0]==(0,0)]
        md = max(seen.values())

        # T1 depth table
        from collections import Counter
        depthrel = Counter()   # (dB, dK)
        # witness olt sanity
        wit_chk = wit_viol = 0
        # D1/D2: per immediate constructor step, is olt(translate child)(translate parent)?
        desc_olt_true = desc_olt_false = 0
        sib_olt_true = sib_olt_false = 0
        # is the WITNESS-K's derivation composed of steps each going to a SMALLER olt?
        # we already know naive chain fails; here we tabulate which step kind breaks.
        descbad_ex = []; sibbad_ex = []
        for B0 in hosts:
            B = tuple(B0[1:])
            tB = translate(B)
            if tB == Z: continue
            dB = head_row0(B)
            G0 = set(Gterm(0, tB))
            sbs = all_subblocks(B)
            for (K, deriv) in sbs:
                tK = translate(K)
                # only WITNESSES: translate K in Gterm0(translate B)
                if tK not in G0: continue
                if tK == tB: continue
                wit_chk += 1
                if not olt(tK, tB): wit_viol += 1
                dK = head_row0(K)
                depthrel[(dB, dK)] += 1
            # D1/D2: every immediate desc/sib step from EVERY subblock parent
            for (seg, deriv) in sbs:
                if not seg: continue
                (x,y)=seg[0]; rest=seg[1:]
                i=0
                while i<len(rest) and rest[i][0]>x: i+=1
                desc=tuple(rest[:i]); sib=tuple(rest[i:])
                tparent=translate(seg)
                if desc:
                    if olt(translate(desc), tparent): desc_olt_true+=1
                    else:
                        desc_olt_false+=1
                        if len(descbad_ex)<5: descbad_ex.append((seg,desc))
                if sib:
                    if olt(translate(sib), tparent): sib_olt_true+=1
                    else:
                        sib_olt_false+=1
                        if len(sibbad_ex)<5: sibbad_ex.append((seg,sib))
        print(f'[+{rounds}] maxdepth={md} hosts={len(hosts)}')
        print(f'  witness olt sanity: checked={wit_chk} VIOL={wit_viol}')
        print(f'  T1 depth (dB,dK) table (top 12): {depthrel.most_common(12)}')
        dks = sorted(set(k for (_,k) in depthrel if k is not None))
        print(f'  dB values: {sorted(set(b for (b,_) in depthrel))}  dK values(non-None): {dks}')
        print(f'  D1 desc-step olt(child,parent): true={desc_olt_true} FALSE={desc_olt_false}')
        for s,d in descbad_ex[:4]: print('     DESCbad parent',tfmt(translate(s))[:34],'child',tfmt(translate(d))[:30])
        print(f'  D2 sib-step  olt(child,parent): true={sib_olt_true} FALSE={sib_olt_false}')
        for s,d in sibbad_ex[:4]: print('     SIBbad parent',tfmt(translate(s))[:34],'child',tfmt(translate(d))[:30])

if __name__ == '__main__':
    main()
