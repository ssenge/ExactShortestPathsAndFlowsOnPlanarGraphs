#!/bin/sh
# negative controls with per-instance detection counts, the Theorem D SSSP check, and the author's driver
cd "$(dirname "$0")"
run() { perl -e 'alarm 1500; exec @ARGV' python3 -I deep.py "$@"; }
for v in no_opt2 all_opt2 xswap literal_D1 nonmono; do
  run 0 2000 8 mix $v > logs/ctl_$v.json 2> logs/ctl_$v.err
done
run 0 2000 8 mix "" > logs/ctl_none.json 2> logs/ctl_none.err
run 0 4000 8 kiss_c F3off grid,sparse,rand unit,zeros,small > logs/ctl_F3off_kissc.json 2> logs/ctl_F3off_kissc.err
run 0 4000 8 kiss F3off grid,sparse,rand unit,zeros,small > logs/ctl_F3off_kiss.json 2> logs/ctl_F3off_kiss.err
perl -e 'alarm 2400; exec @ARGV' python3 -I deep2.py 3000000 30000 8 mix "" > logs/sssp_mix.json 2> logs/sssp_mix.err
perl -e 'alarm 1200; exec @ARGV' python3 -I deep2.py 0 2000 8 mix no_reroute > logs/sssp_ctl_noreroute.json 2> logs/sssp_ctl_noreroute.err
SSSP_CTL=M1 perl -e 'alarm 1200; exec @ARGV' python3 -I deep2.py 0 2000 8 mix "" > logs/sssp_ctl_M1.json 2> logs/sssp_ctl_M1.err
perl -e 'alarm 1800; exec @ARGV' python3 -I confirm_author.py logs/search_e2e_n4_12.json 4 fixed > logs/author_confirm_multi.jsonl 2> logs/author_confirm_multi.err
echo ALLDONE
