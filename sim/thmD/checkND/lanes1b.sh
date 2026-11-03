#!/bin/sh
# wave 1b, on the two slots freed by the exhaustive lanes: 6 edges with all 0/1 capacity vectors, and all maps with 7 edges
cd "$(dirname "$0")"
RICH=1 perl -e 'alarm 1500; exec @ARGV' python3 -I nd_drive.py exh logs/exh_m6rich.json 1100 6 0 1 200 > logs/exh_m6rich.txt 2>&1 &
perl -e 'alarm 1500; exec @ARGV' python3 -I nd_drive.py exh logs/exh_m7.json 1100 7 0 1 100 > logs/exh_m7.txt 2>&1 &
wait
