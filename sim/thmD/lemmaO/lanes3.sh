#!/bin/sh
# (I5) strong form at every incision, plus all other checks
cd "$(dirname "$0")"
perl -e 'alarm 1800; exec @ARGV' python3 -I runO.py 300000 60000 laneE.json random > laneE.txt 2>&1 &
perl -e 'alarm 1800; exec @ARGV' python3 -I runO.py 700000 12000 laneF.json minid 70 12 0.15 0.7 > laneF.txt 2>&1 &
wait
