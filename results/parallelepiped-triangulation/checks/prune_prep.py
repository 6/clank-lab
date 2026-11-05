import json,sys,random
# usage: prune_prep.py B.json cert.json out.txt [corruption]
B=json.load(open(sys.argv[1]))['B']; c=json.load(open(sys.argv[2])); assert c['B']==B
dl=c['deletions']; mode=sys.argv[4] if len(sys.argv)>4 else ''
if mode=='movelast': dl=[dl[-1]]+dl[:-1]
elif mode=='dropone': dl=dl[:len(dl)//2]+dl[len(dl)//2+1:]
elif mode=='reverse': dl=dl[::-1]
elif mode=='swapapex':  # change apex of first entry to another vertex
    s,a=dl[0]; dl=[[s,[v for v in s if v!=a][0]]]+dl[1:]
elif mode=='dup': dl=dl[:-1]+[dl[0]]
elif mode=='swap2':
    random.seed(1); i=len(dl)//3; j=2*len(dl)//3; dl=list(dl); dl[i],dl[j]=dl[j],dl[i]
with open(sys.argv[3],'w') as f:
    f.write(' '.join(str(x) for r in B for x in r)+'\n%d\n'%len(dl))
    for s,a in dl: f.write(' '.join(str(x) for p in s for x in p)+' '+' '.join(map(str,a))+'\n')
