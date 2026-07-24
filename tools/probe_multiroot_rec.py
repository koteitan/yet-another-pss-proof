#!/usr/bin/env python3
"""DECISIVE: the multi-root recursion + per-block shifted-seqlex.

translate B = P y A S  where (B=(d,y)::rest), A=translate(rest.takeWhile(d<.)),
S=translate(rest.dropWhile(d<.)).  d = B.head row0 (=1 usually).
The LEADING TREE  LT = (d,y)::rest.takeWhile(d<.)  is a single block blockok d.
The SIBLING forest = rest.dropWhile(d<.)  (re-opens at <=d).

x in Gterm0(translate B) = Gterm0(P y A S).  mem_Gterm_P (0<=y):
   x == A,  or x in Gterm0 A,  or x in Gterm0 S.
We want olt x (P y A S).

CARRIER for clean proof:
 (R1) x in Gterm0 S branch  (sibling forest): x in Gterm0(translate(siblingforest)).
      Need olt x (P y A S).  Claim: this reduces to the SAME statement on the
      sibling forest as a smaller (0,0)::-host?  Actually translate B's SIBLINGS S
      = translate(dropWhile) and dropWhile re-opens at depth<=d. olt x (P y A S):
      since x in Gterm0 S, and S = translate(forest at depth<=d)... TEST whether
      olt x (P y A S) <- (olt x S) AND (olt S-stuff). Hmm. Just MEASURE:
      for x in Gterm0 S: is olt x (P y A S) ALWAYS true? (must be, =core). And is
      it implied by olt x A' for some cleaner thing? We test the reduction:
        olt x (P y A S): x is in Gterm0 S. The whole P y A S has lead y. If
        lead x < y: auto (olt_P_of_lead_lt). If lead x == y: need deeper.
 (R2) x == A or x in Gterm0 A branch (leading-tree arg): A = translate(takeWhile),
      LT=(d,y)::takeWhile is a single block blockok d.  These x correspond to
      witnesses INSIDE the leading tree => shifted-seqlex on the single block LT.

We MEASURE, splitting every witness x by branch (Sbranch / Abranch), and within
each:
  - lead x vs y split (easy: lead<y).
  - HARD (lead==y): for Abranch, does shifted-seqlex(K, LT) discharge it?
                    for Sbranch, does recursion on the sibling forest discharge it?
We want: 0 cases where olt x (P y A S) is NOT reachable by (easy) OR (A:seqlex on
blockok LT) OR (S:recursion).  Report adversarially.
"""
import sys
sys.path.insert(0,'.')
from fast_pss import Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth
Z=()
def lead(t): return t[0] if t else -1
def Gterm(u,t):
    if t==(): return []
    a,b,c=t; out=[]
    if u<=a: out.append(b); out+=Gterm(u,b)
    out+=Gterm(u,c); return out
def steps1(B): return all(B[j+1][0]<=B[j][0]+1 for j in range(len(B)-1))
def blockok(d,B):
    if not B: return True
    return B[0][0]==d and all(p[0]>=d for p in B) and steps1(B)
def shift(B,delta): return tuple((p[0]+delta,p[1]) for p in B)
def pairlt(p,q): return p[0]<q[0] or (p[0]==q[0] and p[1]<q[1])
def seqlex(M,N):
    M=list(M);N=list(N);i=0
    while i<len(M) and i<len(N):
        if M[i]!=N[i]: return pairlt(M[i],N[i])
        i+=1
    if i==len(M): return len(N)>len(M)
    return False
def all_subblocks(B):
    res=[]
    def rec(seg):
        seg=tuple(seg); res.append(seg)
        if not seg: return
        (x,y)=seg[0]; rest=seg[1:]; i=0
        while i<len(rest) and rest[i][0]>x: i+=1
        rec(rest[:i]); rec(rest[i:])
    rec(tuple(B)); return res

def main():
    for rounds in (5,6):
        seen=enum_depth(4,(1,2,3),28,rounds)
        hosts=[M for M in seen if Lng(M)<=18 and all(c[1]<=1 for c in M) and M and M[0]==(0,0)]
        md=max(seen.values())
        # Recursive evaluator: prove_olt(x, B) returns True if olt x (translate B)
        # is discharged by: easy (lead x<lead) OR Abranch-seqlex OR Sbranch-recursion.
        # We implement the PROOF SCHEMA and check it never fails to discharge a true olt.
        total=0; discharged=0; failed=0; fail_ex=[]
        # also classify
        cnt_easy=cnt_A_seqlex=cnt_S_rec=0

        def leading_split(B):
            # B=(d,y)::rest ; LT=(d,y)::takeWhile(d<.); sib=dropWhile(d<.)
            (d,y)=B[0]; rest=B[1:]
            i=0
            while i<len(rest) and rest[i][0]>d: i+=1
            LT = (B[0],)+tuple(rest[:i])     # leading tree block (single, blockok d)
            sib = tuple(rest[i:])            # sibling forest
            takeW = tuple(rest[:i])
            return d,y,LT,takeW,sib

        def prove(x, B):
            """schema: discharge olt(x, translate B). B nonempty."""
            nonlocal cnt_easy, cnt_A_seqlex, cnt_S_rec
            tB = translate(B)
            assert tB != Z
            y = lead(tB)
            if lead(x) < y:
                cnt_easy += 1
                return True   # olt_P_of_lead_lt
            # lead x == y (can't be > on a true witness)
            d,_,LT,takeW,sib = leading_split(B)
            A = translate(takeW)   # arg of translate B
            S = translate(sib)
            Gset_A = set(Gterm(0,A)); Gset_S = set(Gterm(0,S))
            # which branch is x in?
            if x == A or x in Gset_A:
                # Abranch: x is a witness within the leading tree LT (blockok d).
                # find SubBlock K of LT (the takeW arg-region) with translate K = x,
                # then shifted-seqlex(K, LT).  We verify existence + seqlex.
                # The relevant container for these x is LT itself (the single block).
                # witness K: SubBlock of LT with translate K = x.
                Kfound=None
                for K in all_subblocks(LT):
                    if translate(K)==x and K!=LT and K!=():
                        Kfound=K; break
                if Kfound is None:
                    return False
                dK = Kfound[0][0]
                Ksh = shift(Kfound, d-dK)
                if blockok(d,LT) and blockok(d,Ksh) and seqlex(Ksh,LT):
                    # gives olt(x, translate LT). But we need olt(x, translate B)!
                    # translate LT = P y A Z  (single tree). translate B = P y A S.
                    # olt(x, P y A Z) with x lead==y... and we need olt(x,P y A S).
                    # Since translate LT = P y A Z and translate B = P y A S differ only
                    # in tail (Z vs S), and olt(x,P y A Z) holds => the (lead,arg) part
                    # already decides (a==y, then arg-comparison), which is identical in
                    # P y A S. So olt(x,P y A S) too (tail only matters if arg equal).
                    cnt_A_seqlex += 1
                    return True
                return False
            elif x in Gset_S:
                # Sbranch: x in Gterm0 S, lead x == y. Need olt(x, P y A S).
                # x = P y ax sx.  olt_P_P: olt ax A  OR (ax==A and olt sx S).
                # HONEST schema: discharge via olt ax A.  ax = arg of x.  We need a
                # proof of olt ax A.  A = translate(takeW) (the leading-tree arg, a
                # block at depth d+1... actually takeW is body of LT, blockok d+1).
                # Discharge olt ax A by: shifted-seqlex of ax's witness against takeW,
                # OR ax==A (then need olt sx S -> recurse on tail).  We test olt ax A
                # via shifted-seqlex on the takeW block.
                if x == Z: return False
                _, ax, sx = x
                if ax == A:
                    # need olt sx S : recurse (sx in Gterm0 S? not nec.) -- TEST honestly
                    # this sub-case: compare sx vs S directly via seqlex on sib block.
                    # We just check via the witness route on sib.
                    return _olt_via_seqlex(sx, sib)
                # discharge olt ax A via seqlex on takeW block (blockok d+1)
                ok = _olt_via_seqlex(ax, takeW)
                if ok:
                    cnt_S_rec += 1
                    return True
                return False
            else:
                return False

        for B0 in hosts:
            B=tuple(B0[1:]); tB=translate(B)
            if tB==Z: continue
            for x in Gterm(0,tB):
                total+=1
                real = olt(x,tB)
                got = prove(x,B)
                if got != real:
                    failed+=1
                    if len(fail_ex)<10: fail_ex.append((B,x,real,got))
                elif real:
                    discharged+=1
        print(f'[+{rounds}] maxdepth={md} hosts={len(hosts)} witnesses={total}')
        print(f'  schema discharged-correctly={discharged}  MISMATCH(schema!=real)={failed}')
        print(f'  branch usage: easy={cnt_easy} A-seqlex={cnt_A_seqlex} S-recursion={cnt_S_rec}')
        for B,x,real,got in fail_ex[:10]:
            print(f'    MISMATCH B {mfmt(B)} x {tfmt(x)[:30]} real_olt={real} schema={got}')

if __name__ == '__main__':
    main()
