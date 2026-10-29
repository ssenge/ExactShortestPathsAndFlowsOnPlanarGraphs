#!/bin/sh
# Drop-end repair (--ends 1) against the unrepaired recursion (--ends 0), same seeds.
cd "$(dirname "$0")"
R="perl -e alarm(9000);exec(@ARGV) python3 -I thmD.py --variant fixed"
B="--size 70 --grid 12 --pcommon 0.15 --pfar 0.7"
S="--size 25 --grid 6 --pcommon 0.5 --pfar 0.3"
T="--size 12 --grid 4 --pcommon 0.5 --pfar 0.5"
for e in 1 0; do
  $R --ends $e --start 0 --count 300000 --tiebreak minid $B --out logs/ends${e}_mid.json > logs/ends${e}_mid.txt 2>&1 &
  $R --ends $e --start 0 --count 300000 --tiebreak random $B --out logs/ends${e}_rnd.json > logs/ends${e}_rnd.txt 2>&1 &
  $R --ends $e --start 200000 --count 300000 --tiebreak random $S --out logs/ends${e}_small.json > logs/ends${e}_small.txt 2>&1 &
  $R --ends $e --start 500000 --count 300000 --tiebreak random $T --out logs/ends${e}_tiny.json > logs/ends${e}_tiny.txt 2>&1 &
done
$R --ends 1 --start 100000 --count 40000 --tiebreak minid --size 160 --grid 20 --pcommon 0.1 --pfar 0.8 --out logs/ends1_big.json > logs/ends1_big.txt 2>&1 &
$R --ends 1 --start 900000 --count 200000 --tiebreak random --size 40 --grid 8 --pcommon 0.9 --pfar 0.5 --out logs/ends1_ties.json > logs/ends1_ties.txt 2>&1 &
wait
echo done > logs/lane_ends.done
