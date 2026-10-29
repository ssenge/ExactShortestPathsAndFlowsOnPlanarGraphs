"""Larger instances for the component bound: python3 big.py CONF START:END (FAST mode of rsweep)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'attack3'))
import sys, os
os.environ['FAST'] = '1'
import sweep
def params(fam, r):
    if fam == 'dl': return dict(n=r.randint(300, 700), drop=r.choice([0.0, 0.2, 0.4]))
    if fam == 'grid': return dict(k=r.randint(16, 26), drop=r.choice([0.0, 0.15, 0.3]))
    if fam == 'nested': return dict(R=r.randint(6, 10), K=r.randint(20, 40), p=r.choice([0.2, 0.35, 0.6]))
    if fam == 'pend': return dict(n=r.randint(60, 120), k=r.choice([2, 3, 4]))
    raise KeyError(fam)
sweep.params = params
import rsweep
rsweep.params = params
sys.argv = ['rsweep.py', sys.argv[1], sys.argv[2], 'dl,grid,nested,pend']
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'rsweep.py')).read().split("if __name__ == '__main__':", 1)[1].replace('\n    ', '\n'), rsweep.__dict__)
