#!/bin/bash
# main sweep: every family, per-bag spanning trees, all separator strategies, 7(a) enforced
cd "$(dirname "$0")"
run() { perl -e 'alarm 5400; exec @ARGV' python3 run.py "$@" ; }
for fam in treeplus_sparse treeplus_mid treeplus_dense delaunay grid nested wheels outerplanar cactus; do
  run $fam 1000 250 leaf=rand > logs/main_$fam.log 2>&1
done
