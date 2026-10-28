#!/usr/bin/env python3
"""Plant four independent certificate corruptions and require 8 rejections."""
import copy, json, os, subprocess, sys, tempfile, time
from pathlib import Path

HERE=Path(__file__).resolve().parent
def main():
    start=time.time();c=json.loads((HERE/'certificate.json').read_text())
    variants={}
    v=copy.deepcopy(c);v['coefficients'][0]+=1;variants['wrong-class-coefficient']=v
    v=copy.deepcopy(c);v['blocks'][0]['matrix'][0][0]=-1;variants['non-PSD-block']=v
    v=copy.deepcopy(c);v['multipliers'][0]=-1;variants['negative-multiplier']=v
    v=copy.deepcopy(c);v['selectors'][0]['weight']+=1;variants['selector-sum']=v
    receipts=[]
    with tempfile.TemporaryDirectory(prefix='p32-corrupt-') as tmp:
        for name,v in variants.items():
            path=Path(tmp)/(name+'.json');path.write_text(json.dumps(v,separators=(',',':')))
            for checker in ('check_masks.py','check_embeddings.py'):
                r=subprocess.run([sys.executable,str(HERE/checker),str(path)],capture_output=True,text=True)
                if r.returncode!=1 or not r.stdout.startswith('REJECT:'):
                    raise RuntimeError((name,checker,r.returncode,r.stdout,r.stderr))
                receipts.append({'corruption':name,'checker':checker,'verdict':r.stdout.strip()})
        # Exercise the cover proofs themselves, after every class identity
        # has passed: omit the empty labelled graph from each cover tally.
        for checker in ('check_masks.py','check_embeddings.py'):
            r=subprocess.run([sys.executable,str(HERE/checker),str(HERE/'certificate.json'),'--plant-cover-gap'],capture_output=True,text=True)
            if r.returncode!=1 or not r.stdout.startswith('REJECT:') or 'cover' not in r.stdout:
                raise RuntimeError(('cover-gap',checker,r.returncode,r.stdout,r.stderr))
            receipts.append({'corruption':'cover-gap','checker':checker,'verdict':r.stdout.strip()})
    print(json.dumps({'rejections':receipts,'count':len(receipts),'seconds':time.time()-start}),flush=True)
if __name__=='__main__':main()
