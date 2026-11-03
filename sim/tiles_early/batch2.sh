#!/bin/bash
# targeted sweeps
cd "$(dirname "$0")"
run() { perl -e 'alarm 5400; exec @ARGV' python3 run.py "$@" ; }
run mix 5000 500 global=1 leaf=rand tries=200 > logs/global_mix.log 2>&1
run treeplus_dense 6000 200 strats=chordy,rand,hub preal=1.0 leaf=rand > logs/t_chords_tpd.log 2>&1
run delaunay 6000 200 strats=chordy,rand,hub preal=1.0 leaf=rand > logs/t_chords_del.log 2>&1
run grid 7000 200 strats=hole,face preal=0 leaf=rand > logs/t_virtual_grid.log 2>&1
run nested 7000 200 strats=hole,face preal=0 leaf=rand > logs/t_virtual_nested.log 2>&1
run cactus 8000 200 strats=pinch,anc,single leaf=rand > logs/t_pinch_cactus.log 2>&1
run treeplus_sparse 8000 200 strats=pinch,anc,single leaf=rand > logs/t_pinch_tps.log 2>&1
run mix 9000 300 strats=anc,hole,single inside=empty leaf=rand > logs/t_emptyin.log 2>&1
run mix 9500 300 strats=far leaf=rand > logs/t_far.log 2>&1
run mix 9800 300 strats=single,anc preal=0 leaf=rand > logs/t_single_anc.log 2>&1
