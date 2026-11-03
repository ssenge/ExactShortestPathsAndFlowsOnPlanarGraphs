#!/bin/sh
# wave 2: hard + mutated hard, reading-direction variants, controls + geometry, deep planar. Each python under alarm 1500.
cd "$(dirname "$0")"
( perl -e 'alarm 1500; exec @ARGV' python3 -I nd_drive.py hard logs/hard.json 700 > logs/hard.txt 2>&1
  perl -e 'alarm 1500; exec @ARGV' python3 -I nd_drive.py mut logs/mut.json 700 301 > logs/mut.txt 2>&1 ) &
perl -e 'alarm 1500; exec @ARGV' python3 -I nd_drive.py C logs/C 1400 401 > logs/C.txt 2>&1 &
( perl -e 'alarm 1500; exec @ARGV' python3 -I nd_drive.py ctl logs/ctl 300 501 > logs/ctl.txt 2>&1
  perl -e 'alarm 1500; exec @ARGV' python3 -I nd_drive.py geo logs/geo.json 1100 601 > logs/geo.txt 2>&1 ) &
( perl -e 'alarm 1500; exec @ARGV' python3 -I nd_drive.py planar logs/planar_grid.json 700 102 grid 60 > logs/planar_grid.txt 2>&1
  perl -e 'alarm 1500; exec @ARGV' python3 -I nd_drive.py planar logs/planar_rings.json 700 103 rings 60 > logs/planar_rings.txt 2>&1 ) &
wait
