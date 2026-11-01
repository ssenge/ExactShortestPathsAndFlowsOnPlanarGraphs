#!/bin/sh
# exhaustive m = 4..7 with the per-incision (GEO) and the global (GEOK) curve-model checks
cd "$(dirname "$0")"
for M in 4 5 6 7; do
  GEO=1 GEOK=1 perl -e 'alarm 3600; exec @ARGV' python3 -I run_exh.py logs/maps8nl.json $M 0 1 logs/exhK_m$M.json one,r012,gen 300 3400 > logs/exhK_m$M.txt 2>&1
done
