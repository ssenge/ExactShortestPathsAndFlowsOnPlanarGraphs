#!/bin/sh
cd "$(dirname "$0")"
perl -e 'alarm 1800; exec @ARGV' python3 -I runF.py 2000000 60000 F1.json random > F1.txt 2>&1 &
perl -e 'alarm 1800; exec @ARGV' python3 -I runF.py 2100000 12000 F2.json minid 70 12 0.15 0.7 > F2.txt 2>&1 &
perl -e 'alarm 1800; exec @ARGV' python3 -I runF.py 2600000 12000 F3.json random 40 9 0.05 0.9 > F3.txt 2>&1 &
wait
