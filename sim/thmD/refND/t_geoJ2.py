import sys,os,random,collections,json
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode=True
import nd_core as X, nd_drive as D
D.lane_geo('logs/t_geo2.json',15,77)
C=json.load(open('logs/t_geo2.json'))['counts']
print({k:v for k,v in C.items() if k.startswith(('a2.geo','FAIL','a1.geo'))}, C['runs'])
