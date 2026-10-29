#!/bin/sh
cd "$(dirname "$0")"
run() { perl -e 'alarm 2400; exec @ARGV' python3 -I deep.py "$@"; }
for pol in kiss touch random avoid; do
  run 1000000 150000 10 $pol "" "" generic,generic0 > logs/e2e_gen_$pol.json 2> logs/e2e_gen_$pol.err
done
run 2000000 150000 10 kiss "" "" unit,small,zeros > logs/e2e_tie_kiss.json 2> logs/e2e_tie_kiss.err
echo ALLDONE
