#!/bin/sh
# wave 1: exhaustive M<=6 (two lanes), planar, rand8. Each python under alarm 1500.
cd "$(dirname "$0")"
A="perl -e 'alarm 1500; exec @ARGV'"
( for M in 1 2 3 4 5; do perl -e 'alarm 1500; exec @ARGV' python3 -I nd_drive.py exh logs/exh_m$M.json 300 $M 0 1 200 > logs/exh_m$M.txt 2>&1; done
  perl -e 'alarm 1500; exec @ARGV' python3 -I nd_drive.py exh logs/exh_m6_s0.json 1300 6 0 2 200 > logs/exh_m6_s0.txt 2>&1 ) &
perl -e 'alarm 1500; exec @ARGV' python3 -I nd_drive.py exh logs/exh_m6_s1.json 1420 6 1 2 200 > logs/exh_m6_s1.txt 2>&1 &
perl -e 'alarm 1500; exec @ARGV' python3 -I nd_drive.py planar logs/planar_1.json 1420 101 > logs/planar_1.txt 2>&1 &
perl -e 'alarm 1500; exec @ARGV' python3 -I nd_drive.py rand8 logs/rand8_1.json 1420 201 > logs/rand8_1.txt 2>&1 &
wait
