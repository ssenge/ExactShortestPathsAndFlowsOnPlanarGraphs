#!/bin/sh
# Separation fact (S) and the hull of {i, x, y} (flags sep_fail, hull_i12), with the repair on.
cd "$(dirname "$0")"
R="perl -e alarm(9000);exec(@ARGV) python3 -I thmD.py --variant fixed --ends 1"
$R --start 2000000 --count 150000 --tiebreak random --size 25 --grid 6 --pcommon 0.5 --pfar 0.3 --out logs/sep_small.json > logs/sep_small.txt 2>&1 &
$R --start 2200000 --count 60000 --tiebreak minid --size 70 --grid 12 --pcommon 0.15 --pfar 0.7 --out logs/sep_mid.json > logs/sep_mid.txt 2>&1 &
wait
echo done > logs/lane_sep.done
