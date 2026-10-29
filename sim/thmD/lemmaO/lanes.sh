#!/bin/sh
# two lanes of Lemma O checks
cd "$(dirname "$0")"
perl -e 'alarm 1800; exec @ARGV' python3 -I runO.py 1000 150000 laneA.json random > laneA.txt 2>&1 &
perl -e 'alarm 1800; exec @ARGV' python3 -I runO.py 500000 25000 laneB.json minid 70 12 0.15 0.7 > laneB.txt 2>&1 &
wait
