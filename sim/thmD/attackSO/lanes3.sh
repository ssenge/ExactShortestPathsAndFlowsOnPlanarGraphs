#!/bin/sh
# wave 3: long strips (depth 7+); S1/S_1 on random maps; the two alternatives of RECURSION.md
# (ENDS=2: P_{j_A}, P_{k_A}; ENDS=3: P_{i-} only if i1 < j_A, P_{i+} only if i2 > k_A), each on the
# saved hits, exhaustively for m = 4..7, and by hill-climbing. GEOK=1 (global check of (I1)) everywhere.
cd "$(dirname "$0")"
GEO=1 GEOK=1 perl -e 'alarm 3600; exec @ARGV' python3 -I run_adv.py 500000 1000000 logs/advL.json 4 longstrip all 2400 > logs/advL.txt 2>&1 &
perl -e 'alarm 3600; exec @ARGV' python3 -I s1_test.py rand 0 100000000 logs/s1_rand.json 2400 > logs/s1_rand.txt 2>&1 &
for E in 2 3; do
  ( ENDS=$E GEOK=1 perl -e 'alarm 3600; exec @ARGV' python3 -I run_hits.py logs/ends${E}_hits.json 500 1000 > logs/ends${E}_hits.txt 2>&1
    for M in 4 5 6 7; do
      ENDS=$E GEOK=1 perl -e 'alarm 3600; exec @ARGV' python3 -I run_exh.py logs/maps8nl.json $M 0 1 logs/ends${E}_exh_m$M.json one,r012 200 1500 > logs/ends${E}_exh_m$M.txt 2>&1
    done ) &
  ENDS=$E GEO=1 GEOK=1 perl -e 'alarm 3600; exec @ARGV' python3 -I hill.py 5$E logs/ends${E}_hill_5$E.json 2400 4 > logs/ends${E}_hill_5$E.txt 2>&1 &
done
wait
