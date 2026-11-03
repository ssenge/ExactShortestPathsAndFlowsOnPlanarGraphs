#!/bin/zsh
# usage: batch.sh TAG "conf1 conf2 ..." START:END SCALE [full]
D=$(cd "$(dirname "$0")" && pwd)
FAMS=dl,grid,k2m,fan,nested,pend,flower,swiss,dlsparse,ringch,k2mh,cactus,subdl,gridholes,spiral,wheels
mkdir -p $D/logs
for c in ${=2}; do
  perl -e 'alarm 3600; exec @ARGV' python3 -I $D/adv.py $c $3 $FAMS $4 $5 > $D/logs/$1_$c.txt 2>&1
done
echo DONE $1
