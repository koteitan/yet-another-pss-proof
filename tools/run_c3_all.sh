#!/bin/bash
# closure+3 re-audit of all frozen statements (sequential, hours)
cd /home/koteitan/proofs/ya-pss/git/tools
for s in mine_g6c2_c3 mine_seam6c2_c3 mine_qdiag2c2_c3 mine_osc_c3 mine_gcd_c3 mine_bwt3_c3; do
  echo "=== $s start $(date +%H:%M) ===" >> /tmp/c3_all.out
  timeout 14400 python3 $s.py >> /tmp/c3_all.out 2>&1
  echo "=== $s done rc=$? $(date +%H:%M) ===" >> /tmp/c3_all.out
done
