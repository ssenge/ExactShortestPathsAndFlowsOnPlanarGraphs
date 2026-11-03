#!/bin/zsh
cd "$(dirname "$0")"
perl -e 'alarm 5000; exec @ARGV' python3 -I exh.py 7 0 2 10 > logs/exh7_0.txt 2>&1 &
p0=$!
perl -e 'alarm 5000; exec @ARGV' python3 -I exh.py 7 1 2 10 > logs/exh7_1.txt 2>&1 &
p1=$!
wait $p0 $p1
./queue.sh
