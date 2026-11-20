import json, urllib.request, urllib.parse, sys, numpy as np
wd=sys.argv[1]
# measured midpoints from (179) trail fits: minutes after 21:00 UT
times={'731':"'1908-12-21 00:58:23.1'",'733':"'1908-12-22 01:28:37.1'"}
spans={'731':("'1908-12-21 00:21:54'","'1908-12-21 01:34:48'"),'733':("'1908-12-22 00:06:24'","'1908-12-22 02:50:48'")}
out={}
for pl in ['731','733']:
    rows=[]
    for tl in [times[pl],spans[pl][0],spans[pl][1]]:
        p=dict(format='json',COMMAND="'999'",OBJ_DATA='NO',MAKE_EPHEM='YES',EPHEM_TYPE='OBSERVER',CENTER="'coord@399'",COORD_TYPE='GEODETIC',SITE_COORD="'-71.0903,41.8997,0.003'",TLIST=tl,TLIST_TYPE='CAL' ,QUANTITIES="'1,9,19,20,24'",CSV_FORMAT='YES',ANG_FORMAT='DEG',EXTRA_PREC='YES',TIME_DIGITS='FRACSEC')
        txt=json.load(urllib.request.urlopen('https://ssd.jpl.nasa.gov/api/horizons.api?'+urllib.parse.urlencode(p),timeout=120))['result']
        s=txt.index('$$SOE');e=txt.index('$$EOE'); r=txt[s+5:e].strip().split(',')
        hdr=txt[:s].strip().splitlines()[-2]
        rows.append([x.strip() for x in r])
    out[pl]=dict(header=hdr,mid=rows[0],open=rows[1],close=rows[2])
    print(pl,'header:',hdr[:200]); print(' mid',rows[0][:12]); print(' open',rows[1][3:5],' close',rows[2][3:5])
json.dump(out,open(f'{wd}/pluto_hz.json','w'),indent=1)
