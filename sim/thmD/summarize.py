#!/usr/bin/env python3
"""Aggregate logs/*.json run files into a compact table (stdout)."""
import json, os, sys, glob, collections
HERE = os.path.dirname(os.path.abspath(__file__))
rows = []
for p in sorted(glob.glob(os.path.join(HERE, 'logs', '[A-Z]_*.json'))):
    r = json.load(open(p))
    name = os.path.basename(p)[:-5]
    fl = r['flag_instances']
    claims = {k: v for k, v in fl.items() if not k.startswith(('dev_', 'levels=', 'stat_'))}
    lv = {k[7:]: v for k, v in fl.items() if k.startswith('levels=')}
    st = {k[5:]: v for k, v in fl.items() if k.startswith('stat_')}
    dev = {k: v for k, v in fl.items() if k.startswith('dev_')}
    tot = sum(r['families'].values())
    print(f"== {name}  opts={r['opts']}  instances={tot}  failing={r['nfail']}  secs={r['secs']:.0f}")
    print(f"   families: {r['families']}")
    print(f"   failing per family: {r['family_fail']}")
    print(f"   levels: {dict(sorted(lv.items()))}")
    print(f"   coverage stats (#instances): {st}")
    print(f"   deviations: {dev}")
    print(f"   flags (#instances): {dict(sorted(claims.items(), key=lambda z: -z[1]))}")
    # root-cause split for failing instances (only the first 200 are stored)
    rc = collections.Counter()
    for f in r['fails']:
        fs = f['flags']
        if f['info'].get('e0_same'):
            rc['D2 (e0=e_last=st)'] += 1
        elif 'struct_merge' in fs or 'struct_merged_with_source' in fs:
            rc['D1 (incised endpoint-case edge)'] += 1
        else:
            rc['other'] += 1
    if rc:
        print(f"   root cause of stored failing instances: {dict(rc)}")
    print()
