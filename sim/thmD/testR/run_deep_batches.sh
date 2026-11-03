#!/bin/sh
# long deep runs; each capped
D=$(dirname "$0")
cd "$D"
run() { perl -e 'alarm 3000; exec @ARGV' python3 -I deep.py "$@"; }
run 100000 60000 10 mix "" "" "" > logs/deep_A_mix_default.json 2> logs/deep_A.err
run 200000 30000 10 mix "" big,biggrid "" > logs/deep_B_big_default.json 2> logs/deep_B.err
run 300000 40000 10 mix lit_chord "" "" > logs/deep_C_litchord.json 2> logs/deep_C.err
run 400000 40000 10 mix lit_full "" "" > logs/deep_D_litfull.json 2> logs/deep_D.err
run 500000 40000 10 kiss_c "" grid,sparse,rand,biggrid unit,zeros,small > logs/deep_E_kissc.json 2> logs/deep_E.err
run 600000 30000 10 kiss_c lit_chord grid,sparse,rand,biggrid unit,zeros,small > logs/deep_F_kissc_lit.json 2> logs/deep_F.err
echo ALLDONE
