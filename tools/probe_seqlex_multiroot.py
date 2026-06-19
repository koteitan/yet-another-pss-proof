#!/usr/bin/env python3
"""DECISIVE: the generalized seqlex_imp_olt' for MULTI-ROOT B.

Established this round: for every Gterm-0 witness K of translate B,
  - shift K (by dB - dK) is blockok dB        [0 viol +5/+6]
  - seqlex (shift K) B                         [0 viol +5/+6]
  - the ONLY reason seqlex_imp_olt doesn't fire is B is multi-root (not blockok).

So the live lemma is a MULTI-ROOT generalization:
  seqlex_imp_olt' :  blockok d A  ->  seqlex A N  ->  translate A <o translate N
WITHOUT requiring blockok d N (N may re-open below d, i.e. be multi-root).

This probe stress-tests seqlex_imp_olt' as a STANDALONE order fact over a BROAD
domain (not just witnesses): all (A, N) with A blockok d, seqlex A N, over
enumerated short pair-sequences -- to see if it is universally TRUE (the notes
claim 0 viol 34k) OR has a precise failure mode we must guard.

We test two forms:
  G1: A blockok d, seqlex A N           -> olt(translate A, translate N)   [most general]
  G2: additionally N nonempty & d <= N.head.1 (A and N start at same/aligned
      depth d -- the natural alignment from shift)                          [guarded]
We also reconfirm the WITNESS instance is 0-viol, and check whether N's first
column being possibly < d (multi-root re-open) breaks G1.
"""
import sys, itertools
sys.path.insert(0, '.')
from wfe_explore import translate, olt

Z = ()
def steps1(B): return all(B[j+1][0] <= B[j][0]+1 for j in range(len(B)-1))
def blockok(d, B):
    if not B: return True
    return B[0][0] == d and all(p[0] >= d for p in B) and steps1(B)
def pairlt(p, q): return p[0] < q[0] or (p[0] == q[0] and p[1] < q[1])
def seqlex(M, N):
    M = list(M); N = list(N); i = 0
    while i < len(M) and i < len(N):
        if M[i] != N[i]: return pairlt(M[i], N[i])
        i += 1
    if i == len(M): return len(N) > len(M)
    return False

def gen_seqs(maxlen, rows0, rows1):
    cols = [(a, b) for a in rows0 for b in rows1]
    for L in range(0, maxlen + 1):
        for combo in itertools.product(cols, repeat=L):
            yield tuple(combo)

def main():
    d = 1
    rows0 = (1, 2, 3)        # A is blockok d=1, internal rows >= 1
    rows1 = (0, 1, 2)
    maxlen = 4
    g1_chk = g1_bad = 0
    g2_chk = g2_bad = 0
    g1ex = []
    # N can re-open below d (multi-root): allow row0 in {0,1,2,3}
    Ns = list(gen_seqs(maxlen, (0, 1, 2, 3), rows1))
    As = [A for A in gen_seqs(maxlen, rows0, rows1) if blockok(d, A)]
    print(f'enumerating |A blockok|={len(As)} x |N|={len(Ns)} ...')
    for A in As:
        tA = translate(A)
        for N in Ns:
            if not seqlex(A, N): continue
            tN = translate(N)
            real = olt(tA, tN)
            g1_chk += 1
            if not real:
                g1_bad += 1
                if len(g1ex) < 12:
                    g1ex.append((A, N))
            # G2 guard: N nonempty and d <= N.head.1
            if N and d <= N[0][0]:
                g2_chk += 1
                if not real: g2_bad += 1
    print(f'G1 (blockok d A & seqlex A N -> olt): chk={g1_chk} BAD={g1_bad}')
    print(f'G2 (+ d<=N.head.1):                   chk={g2_chk} BAD={g2_bad}')
    for A, N in g1ex[:12]:
        print('   G1BAD A', A, 'N', N, 'tA', translate(A), 'tN', translate(N))

if __name__ == '__main__':
    main()
