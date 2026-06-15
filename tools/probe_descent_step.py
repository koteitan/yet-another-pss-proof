#!/usr/bin/env python3
"""The descent step: nodeAtLead t (L+1) = (nodeAtLead t L).b  (chain is t.b.b...).
We have olt(nb)(nf) at lead L (both P L _ _).  Want olt(nb.b)(nf.b) (lead L+1).
This is NOT pure olt.  What makes it hold on the inv2 spine?

nb = P L nb_b nb_c,  nf = P L nf_b nf_c.  olt nb nf (lead equal L) means:
  olt nb_b nf_b  OR  (nb_b = nf_b AND olt nb_c nf_c).
We want olt nb_b nf_b (the args = the lead-(L+1) chain nodes).
  - Case olt nb_b nf_b: DONE directly.
  - Case nb_b = nf_b & olt nb_c nf_c: then nb_b = nf_b so olt FAILS (equal)!
    But the chain node at L+1 = nb_b = nf_b, so they're EQUAL at L+1, and the
    olt must be carried by deeper... wait but we claimed olt at EVERY node.
    If nb_b = nf_b then at lead L+1 the nodes are EQUAL, contradicting strict olt.

So either the 'olt at every node' is really 'ole (<=) at every node' with strict
somewhere, OR the case nb_b=nf_b never happens.  Let me re-test with ole and
find WHERE strictness sits.
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, enum_ST, olt, maxsub
Z = ()
def le(s,t): return s==t or olt(s,t)
def lead(t): return 0 if t==Z else t[0]
def Gterm(u, t):
    if t == Z: return []
    a, b, c = t; out = []
    if u <= a: out.append(b); out += Gterm(u, b)
    out += Gterm(u, c); return out
def pfire(u, b): return any(not olt(g, b) for g in Gterm(u, b))
def proj(u, b):
    while True:
        bad = [g for g in Gterm(u, b) if not olt(g, b)]
        if not bad: return b
        m = bad[0]
        for h in bad[1:]:
            if olt(m, h): m = h
        b = m
def nodeAtLead(t, L):
    cur=t
    while cur!=Z:
        if lead(cur)==L: return cur
        cur=cur[1]
    return None

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=14, rounds=8)
    NF = sorted({translate(list(M)) for M in ST}, key=str)
    args = sorted({t[1] for t in NF if t != Z and t[0] == 0}, key=str)
    fire = [b for b in args if pfire(0, b)]

    # At each lead L (1..k): classify the relation nb vs nf.
    # Per pair, find the FIRST lead L where olt is RESOLVED at the arg (nb_b<o nf_b)
    # vs carried at tail (nb_b=nf_b, olt nb_c nf_c).
    # Claim: once resolved at arg at some lead L0, all deeper nodes have
    #   nb_b <o nf_b => the lead-(L0+1) nodes are olt; continue.
    # Actually the descent: at lead L, nodes nb,nf. If olt resolved at ARG
    # (nb_b<o nf_b), the NEXT chain node (nb_b,nf_b) is strictly olt -> recurse,
    # STAYS arg-resolved or deeper. If resolved at TAIL (nb_b=nf_b), the next
    # chain node is EQUAL (nb_b=nf_b), and strictness is in the TAIL c, off-chain.
    # But chain continues via .b = nb_b=nf_b (equal!), so deeper chain nodes EQUAL
    # until... the lead-k node would be EQUAL => proj0 b=proj0 f, contradicting strict!
    # So in eqmaxsub firing, the resolution must ALWAYS be at the ARG, never tail,
    # at EVERY lead up to k.  Re-test: at every lead L in 1..k, is it arg-resolved?
    allarg=0; tot=0; tailcase=[]
    for b in fire:
        k=maxsub(b)
        for f in fire:
            if not olt(b,f) or maxsub(f)!=k: continue
            tot+=1
            ok=True
            for L in range(1,k+1):
                nb=nodeAtLead(b,L); nf=nodeAtLead(f,L)
                _,nbb,nbc=nb; _,nfb,nfc=nf
                if olt(nbb,nfb): continue  # arg-resolved, good
                elif nbb==nfb:
                    # tail-resolved at this lead: chain goes equal below
                    ok=False
                    if len(tailcase)<6: tailcase.append((L,k,nb,nf))
                    break
                else:
                    ok=False; break
            if ok: allarg+=1
    print(f"eqmaxsub pairs {tot}: arg-resolved at EVERY lead 1..k: {allarg}")
    for tc in tailcase: print("  TAIL-resolved at lead",tc[0],"/",tc[1],":",tc[2],tc[3])

if __name__ == '__main__':
    main()
