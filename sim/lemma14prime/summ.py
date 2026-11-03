import sys, json
keys = sys.argv[2].split(',') if len(sys.argv) > 2 else None
tot = {}
for l in open(sys.argv[1]):
    if l.startswith('FAM ') or l.startswith('MAX '):
        tag, fam, js = l.rstrip('\n').split(' ', 2)
        d = json.loads(js)
        print(tag, fam, {k: d[k] for k in d if keys is None or k in keys or k.startswith('FAIL')})
    elif not l.startswith('FAM') and not l.startswith('MAX'):
        print(l.rstrip())
