#!/bin/sh
# wave 2: hill-climbing (GEO), the saved hits of the unrepaired recursion (run_hits.py, GEO), hill-climbing on the whole-path reading (F), minimum-aware
# policies (GEO), exhaustive m=8 shard 1/2 (GEO), structured small graphs (GEO, 20 (s,t) pairs each)
# GEOK=1 everywhere: the global check of (I1) for K_l (geoK.py)
cd "$(dirname "$0")"
for sd in 21; do
  GEO=1 GEOK=1 perl -e 'alarm 3600; exec @ARGV' python3 -I hill.py $sd logs/hill_$sd.json 3400 4 > logs/hill_$sd.txt 2>&1 &
done
THMD_VARIANT=F GEOK=1 perl -e 'alarm 3600; exec @ARGV' python3 -I hill.py 23 logs/hillF_23.json 3400 4 > logs/hillF_23.txt 2>&1 &
GEO=1 GEOK=1 perl -e 'alarm 3600; exec @ARGV' python3 -I run_adv.py 300000 1000000 logs/advC.json 4 any dropmin,outside,maxbound,alongQ 3400 > logs/advC.txt 2>&1 &
GEO=1 GEOK=1 perl -e 'alarm 3600; exec @ARGV' python3 -I run_exh.py logs/maps8nl.json 8 1 2 logs/exhnl_m8_s1.json one,r012 200 3400 > logs/exhnl_m8_s1.txt 2>&1 &
GEO=1 GEOK=1 STPAIRS=20 perl -e 'alarm 3600; exec @ARGV' python3 -I run_exh.py logs/struct.json 0 0 1 logs/exhstruct.json one,r12 500 3400 > logs/exhstruct.txt 2>&1 &
GEO=1 GEOK=1 perl -e 'alarm 3600; exec @ARGV' python3 -I run_hits.py logs/hits.json 2000 2000 > logs/hits.txt 2>&1 &
wait
