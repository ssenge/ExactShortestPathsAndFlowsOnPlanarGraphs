#!/bin/sh
# the maps of m = 8 that the two shards of waves 1 and 2 did not reach in 3400 s
# (shard 0/2 stopped after map index 7434, shard 1/2 after 6327)
cd "$(dirname "$0")"
for sh in 1 3 5 7; do
  GEO=1 GEOK=1 MAPLO=6329 perl -e 'alarm 3600; exec @ARGV' python3 -I run_exh.py logs/maps8nl.json 8 $sh 8 logs/exhnl_m8_rest_s$sh.json one,r012 200 3000 > logs/exhnl_m8_rest_s$sh.txt 2>&1 &
done
GEO=1 GEOK=1 MAPLO=7436 perl -e 'alarm 3600; exec @ARGV' python3 -I run_exh.py logs/maps8nl.json 8 0 2 logs/exhnl_m8_rest_s0.json one,r012 200 3000 > logs/exhnl_m8_rest_s0.txt 2>&1 &
wait
