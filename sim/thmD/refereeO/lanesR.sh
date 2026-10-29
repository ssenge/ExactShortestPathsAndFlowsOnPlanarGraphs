#!/bin/sh
cd "$(dirname "$0")"
R="perl -e 'alarm 1800; exec @ARGV' python3 -I runR.py"
perl -e 'alarm 1800; exec @ARGV' python3 -I runR.py 2000000 60000 R1.json random > R1.txt 2>&1 &
perl -e 'alarm 1800; exec @ARGV' python3 -I runR.py 2100000 12000 R2.json minid 70 12 0.15 0.7 > R2.txt 2>&1 &
E0RULE=anycorner perl -e 'alarm 1800; exec @ARGV' python3 -I runR.py 2200000 60000 R3.json random > R3.txt 2>&1 &
E0RULE=anycorner perl -e 'alarm 1800; exec @ARGV' python3 -I runR.py 2300000 12000 R4.json minid 70 12 0.15 0.7 > R4.txt 2>&1 &
perl -e 'alarm 1800; exec @ARGV' python3 -I runR.py 2400000 3000 R5.json random 120 14 0.1 0.8 > R5.txt 2>&1 &
E0RULE=anycorner perl -e 'alarm 1800; exec @ARGV' python3 -I runR.py 2500000 3000 R6.json minid 120 14 0.1 0.8 > R6.txt 2>&1 &
perl -e 'alarm 1800; exec @ARGV' python3 -I runR.py 2600000 12000 R7.json random 40 9 0.05 0.9 > R7.txt 2>&1 &
wait
