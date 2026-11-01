#!/bin/sh
# wave 3: added after the text of the paper changed during the run. Direct checks of the new text; smallest simple instances (no parallel edges).
cd "$(dirname "$0")"
perl -e 'alarm 1500; exec @ARGV' python3 -I scan_simple.py logs/t_simple.json 420 > logs/t_simple.txt 2>&1 &
( perl -e 'alarm 1500; exec @ARGV' python3 -I nd_drive.py exh logs/t_new_exh5.json 100 5 0 1 > logs/t_new_exh5.txt 2>&1
  perl -e 'alarm 1500; exec @ARGV' python3 -I nd_drive.py exh logs/t_new_exh6.json 320 6 0 1 > logs/t_new_exh6.txt 2>&1 ) &
perl -e 'alarm 1500; exec @ARGV' python3 -I nd_drive.py geo logs/t_new_geo.json 420 701 > logs/t_new_geo.txt 2>&1 &
perl -e 'alarm 1500; exec @ARGV' python3 -I nd_drive.py planar logs/t_new_planar.json 420 104 > logs/t_new_planar.txt 2>&1 &
wait
