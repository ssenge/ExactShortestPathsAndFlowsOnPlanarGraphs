#!/bin/sh
cd "$(dirname "$0")"
R="perl -e alarm(3000);exec(@ARGV) python3 -I thmD.py"
B="--size 70 --grid 12 --pcommon 0.15 --pfar 0.7"
$R --start 0 --count 30000 --variant literal --tiebreak minid $B --out logs/B_literal_minid.json > logs/B.txt 2>&1
$R --start 100000 --count 4000 --variant fixed --tiebreak minid --size 160 --grid 20 --pcommon 0.1 --pfar 0.8 --out logs/D_fixed_big.json > logs/D.txt 2>&1
$R --start 100000 --count 4000 --variant literal --tiebreak minid --size 160 --grid 20 --pcommon 0.1 --pfar 0.8 --out logs/E_literal_big.json > logs/E.txt 2>&1
$R --start 300000 --count 15000 --variant literal --tiebreak random --size 25 --grid 6 --pcommon 0.5 --pfar 0.3 --out logs/H_literal_small.json > logs/H.txt 2>&1
$R --start 0 --count 6000 --variant literal --e0rule free $B --out logs/F_literal_free_e0.json > logs/F.txt 2>&1
perl -e 'alarm(2400);exec(@ARGV)' python3 -I minimize.py 300204 D2 25 6 0.5 0.3 > logs/min_D2.json 2> logs/min_D2.err
echo done > logs/lane2.done
