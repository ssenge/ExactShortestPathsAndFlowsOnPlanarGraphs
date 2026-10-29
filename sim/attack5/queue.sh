#!/bin/zsh
# runs sequentially (one heavy process)
cd "$(dirname "$0")"
for neg in noheavy anycorner skip1; do perl -e 'alarm 900; exec @ARGV' python3 -I negctl.py $neg 0 400 >> logs/negctl.txt 2>&1; done
perl -e 'alarm 1800; exec @ARGV' python3 -I rand.py 100000 112000 10 13 all 6 100 > logs/rand_small.txt 2>&1
for n in 8 9 10; do perl -e 'alarm 1800; exec @ARGV' python3 -I exh_trees.py $n 3000 5 > logs/trees_$n.txt 2>&1; done
for obj in in1 outm inj wjm1 chord side; do for s in 1 2 3; do perl -e 'alarm 600; exec @ARGV' python3 -I hill.py $obj $s 600 36 >> logs/hill.txt 2>&1; done; done
perl -e "alarm 2400; exec @ARGV" python3 -I rand.py 200000 200600 100 400 all 40 3 > logs/rand_big.txt 2>&1
echo QUEUE_DONE >> logs/queue_done.txt
