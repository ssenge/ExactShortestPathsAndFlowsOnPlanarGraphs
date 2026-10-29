#!/bin/sh
cd "$(dirname "$0")"
R="perl -e alarm(5400);exec(@ARGV) python3 -I test_mono.py"
$R formal 0 15000 > mlogs/F1.json 2>&1 &
$R anylegal 0 15000 > mlogs/A1.json 2>&1 &
$R formal 300000 4000 70 12 > mlogs/F2.json 2>&1 &
$R anylegal 400000 4000 70 12 > mlogs/A2.json 2>&1 &
$R anylegal 500000 15000 12 4 > mlogs/A3.json 2>&1 &
$R anylegal 700000 30000 > mlogs/A4.json 2>&1 &
$R formal 800000 15000 > mlogs/F4.json 2>&1 &
wait
echo done > mlogs/done
