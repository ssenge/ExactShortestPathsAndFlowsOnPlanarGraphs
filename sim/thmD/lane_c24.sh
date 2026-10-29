#!/bin/sh
# Interval form of [18, Claim 2.4] (flag c24_interval), checked with the drop-end repair on.
cd "$(dirname "$0")"
R="perl -e alarm(9000);exec(@ARGV) python3 -I thmD.py --variant fixed --ends 1"
$R --start 1200000 --count 150000 --tiebreak random --size 25 --grid 6 --pcommon 0.5 --pfar 0.3 --out logs/c24_small.json > logs/c24_small.txt 2>&1 &
$R --start 1400000 --count 100000 --tiebreak minid --size 70 --grid 12 --pcommon 0.15 --pfar 0.7 --out logs/c24_mid.json > logs/c24_mid.txt 2>&1 &
wait
echo done > logs/lane_c24.done
