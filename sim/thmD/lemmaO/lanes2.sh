#!/bin/sh
# rerun with the refined end-rule check (cut position of the old end token)
cd "$(dirname "$0")"
perl -e 'alarm 1800; exec @ARGV' python3 -I runO.py 200000 80000 laneC.json random > laneC.txt 2>&1 &
perl -e 'alarm 1800; exec @ARGV' python3 -I runO.py 600000 15000 laneD.json minid 70 12 0.15 0.7 > laneD.txt 2>&1 &
wait
