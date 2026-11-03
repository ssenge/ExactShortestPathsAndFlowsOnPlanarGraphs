"""aggregate adv9 logs: python3 agg.py logs/*.txt"""
import sys, ast, collections
T = collections.Counter(); M = collections.defaultdict(float); per = {}
viol = []; fails = []
for fn in sys.argv[1:]:
    for line in open(fn):
        if line.startswith('TOTAL '):
            parts = line.split(' ', 2)
            body = parts[2]
            i = body.index('} {')
            d1 = ast.literal_eval(body[:i + 1]); d2 = ast.literal_eval(body[i + 2:].strip())
            T.update(d1); T.update(d2)
            per[fn] = (d1.get('instances', 0), d1.get('bags', 0), d1.get('bags_d8', 0))
        elif line.startswith('TOTMX '):
            d = ast.literal_eval(line.split(' ', 2)[2])
            for k, v in d.items():
                M[k] = max(M[k], v)
        elif line.startswith('VIOL '):
            viol.append((fn, line.strip()[:400]))
        elif line.startswith('FAIL '):
            fails.append((fn, line.strip()[:400]))
for fn, v in per.items():
    print(fn.split('/')[-1], v)
print('TOTAL', dict(T))
print('MAX', dict(M))
print('VIOL lines', len(viol)); [print(' ', v) for v in viol[:20]]
print('FAIL lines', len(fails)); [print(' ', v) for v in fails[:20]]
