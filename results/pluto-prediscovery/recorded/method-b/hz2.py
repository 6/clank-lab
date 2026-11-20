import sys, json, numpy as np, urllib.request, urllib.parse
wd=sys.argv[1]
nights={'731':("'1908-12-20 21:00'","'1908-12-21 13:00'"),'733':("'1908-12-21 21:00'","'1908-12-22 13:00'")}
ids={'179':"'179;'",'1436':"'1436;'",'2891':"'2891;'",'4204':"'4204;'",'2175':"'2175;'",'3147':"'3147;'",'9593':"'9593;'",'13567':"'13567;'",'15751':"'15751;'",'25493':"'25493;'",'999':"'999'"}
for pl,(a,b) in nights.items():
    if len(sys.argv) > 2 and pl != sys.argv[2]: continue
    for k,cmd in ids.items():
        if len(sys.argv) > 3 and k != sys.argv[3]: continue
        p=dict(format='json',COMMAND=cmd,OBJ_DATA='NO',MAKE_EPHEM='YES',EPHEM_TYPE='OBSERVER',CENTER="'coord@399'",COORD_TYPE='GEODETIC',SITE_COORD="'-71.0903,41.8997,0.003'",START_TIME=a,STOP_TIME=b,STEP_SIZE="'1m'",QUANTITIES="'1,9'",CSV_FORMAT='YES',ANG_FORMAT='DEG',EXTRA_PREC='YES',TIME_DIGITS='SECONDS')
        u='https://ssd.jpl.nasa.gov/api/horizons.api?'+urllib.parse.urlencode(p)
        txt=json.load(urllib.request.urlopen(u,timeout=120))['result']
        open(f'{wd}/hz_{pl}_{k}.txt','w').write(txt)
        s=txt.index('$$SOE'); e=txt.index('$$EOE')
        rows=[r.split(',') for r in txt[s+5:e].strip().splitlines()]
        import re
        jd=[];ra=[];de=[];mag=[]
        from astropy.time import Time
        t=Time([r[0].strip().replace('A.D. ','') for r in rows][:1],format='iso') if False else None
        dts=[r[0].strip() for r in rows]
        ra=np.array([float(r[3]) for r in rows]); de=np.array([float(r[4]) for r in rows]); mag=np.array([float(r[5]) if r[5].strip() not in ('n.a.','') else np.nan for r in rows])
        np.savez(f'{wd}/hz_{pl}_{k}.npz',dt=np.array(dts),ra=ra,dec=de,mag=mag)
        tgt=re.search(r'Target body name: (.*?)\{',txt)
        print(pl,k,(tgt.group(1).strip() if tgt else '?'),len(rows),dts[0],ra[0],de[0],mag[0])
