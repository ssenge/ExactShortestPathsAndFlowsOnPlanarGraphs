#!/bin/bash
cd "$(dirname "$0")"
while pgrep -f batch2.sh >/dev/null; do sleep 20; done
perl -e 'alarm 5400; exec @ARGV' python3 s7_rebuild.py 60 > logs/s7_rebuild.txt 2>&1
perl -e 'alarm 3600; exec @ARGV' python3 run.py mix 60000 300 neg=1 neg_e2e=1 stop=0 leaf=rand > logs/negcontrol.txt 2>&1
