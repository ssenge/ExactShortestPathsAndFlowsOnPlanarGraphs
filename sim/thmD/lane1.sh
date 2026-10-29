#!/bin/sh
cd "$(dirname "$0")"
R="perl -e alarm(3000);exec(@ARGV) python3 -I thmD.py"
B="--size 70 --grid 12 --pcommon 0.15 --pfar 0.7"
$R --start 0 --count 30000 --variant fixed --tiebreak minid $B --out logs/A_fixed_minid.json > logs/A.txt 2>&1
$R --start 0 --count 30000 --variant fixed --tiebreak random $B --out logs/C_fixed_random.json > logs/C.txt 2>&1
$R --start 200000 --count 15000 --variant fixed --tiebreak random --size 25 --grid 6 --pcommon 0.5 --pfar 0.3 --out logs/G_fixed_small.json > logs/G.txt 2>&1
$R --start 0 --count 3000 --variant fixed --mode cw $B --out logs/N_cw.json > logs/Ncw.txt 2>&1
$R --start 0 --count 3000 --variant fixed --mode Msmall $B --out logs/N_Msmall.json > logs/NM.txt 2>&1
$R --start 0 --count 3000 --variant fixed --mode noise $B --out logs/N_noise.json > logs/Nn.txt 2>&1
perl -e 'alarm(2400);exec(@ARGV)' python3 -I minimize.py 300615 D1 25 6 0.5 0.3 > logs/min_D1.json 2> logs/min_D1.err
echo done > logs/lane1.done
