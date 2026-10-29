import sys, ast
K = ('mult_induced', 'mult_comm', 'vmult_all', 'vmult_phantom', 'commdiam_over_GXdiam', 'commdiam_over_D')
for f in sys.argv[1:]:
    print('==', f)
    for l in open(f):
        if l.startswith('    '):
            d = ast.literal_eval(l.strip()); print('   ', {k: d[k] for k in K if k in d})
        elif l.strip():
            print(' ', l.strip()[:110])
