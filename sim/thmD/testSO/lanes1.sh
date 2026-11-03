#!/bin/sh
# wave 1: hill-climbing x2, policies (all incl. dropmin/outside),
# whole-path reading (F), exhaustive m=8 shard 0/2, exhaustive m=4..7; all with GEO=1 except F
cd "$(dirname "$0")"
A="perl -e 'alarm 3600; exec @ARGV'"
for sd in 11 12; do
  GEO=1 perl -e 'alarm 3600; exec @ARGV' python3 -I hill.py $sd logs/hill_$sd.json 3400 4 > logs/hill_$sd.txt 2>&1 &
done
GEO=1 perl -e 'alarm 3600; exec @ARGV' python3 -I run_adv.py 100000 1000000 logs/advA.json 4 any all 3400 > logs/advA.txt 2>&1 &
THMD_VARIANT=F perl -e 'alarm 3600; exec @ARGV' python3 -I run_adv.py 400000 1000000 logs/advF.json 4 any all 3400 > logs/advF.txt 2>&1 &
GEO=1 perl -e 'alarm 3600; exec @ARGV' python3 -I run_exh.py logs/maps8nl.json 8 0 2 logs/exhnl_m8_s0.json one,r012 200 3400 > logs/exhnl_m8_s0.txt 2>&1 &
( for M in 4 5 6 7; do
    GEO=1 perl -e 'alarm 3600; exec @ARGV' python3 -I run_exh.py logs/maps8nl.json $M 0 1 logs/exhgeo_m$M.json one,r012,gen 300 3400 > logs/exhgeo_m$M.txt 2>&1
  done ) &
wait
