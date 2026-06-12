#!/bin/bash
cd /home/koteitan/ya-pss/git/tools
echo "=== topdesc EXTRA=3 $(date +%H:%M) ===" >> /tmp/c3_b2.out
EXTRA=3 timeout 14400 python3 mine_topdesc2.py >> /tmp/c3_b2.out 2>&1
echo "=== openm1 sibrel4 closure+2 $(date +%H:%M) ===" >> /tmp/c3_b2.out
sed 's/hosts_plus(extra=1)/hosts_plus(extra=3)/; s/def hosts_plus(extra=1)/def hosts_plus(extra=3)/' mine_openm1.py > mine_openm1_c3.py
timeout 14400 python3 mine_openm1_c3.py >> /tmp/c3_b2.out 2>&1
echo "=== stsb closure+2 $(date +%H:%M) ===" >> /tmp/c3_b2.out
sed 's/hosts_plus(1)/hosts_plus(2)/' mine_stsb.py > mine_stsb_c2.py
timeout 14400 python3 mine_stsb_c2.py >> /tmp/c3_b2.out 2>&1
echo "=== done $(date +%H:%M) ===" >> /tmp/c3_b2.out
