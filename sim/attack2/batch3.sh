#!/bin/bash
# runs after batch1: tiny exhaustive-ish, 7(a)-violating, and region-based children
cd "$(dirname "$0")"
while pgrep -f batch1.sh >/dev/null; do sleep 20; done
run() { perl -e 'alarm 5400; exec @ARGV' python3 run.py "$@" ; }
run tiny 20000 20000 leaf=2 lp=5 > logs/tiny.log 2>&1
for fam in star windmill k2m fan broom cactus treeplus_sparse; do
  run $fam 30000 150 allow7a=1 leaf=rand > logs/a7_$fam.log 2>&1
done
run mix 40000 400 region=1 leaf=rand > logs/region_mix.log 2>&1
run mix 41000 300 region=1 global=1 leaf=rand tries=200 > logs/region_global.log 2>&1
for fam in star windmill k2m fan broom; do
  run $fam 42000 150 region=1 leaf=rand > logs/region_$fam.log 2>&1
done
