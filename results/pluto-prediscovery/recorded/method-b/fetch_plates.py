# Download the public DASCH DR7 full-resolution mosaics and jacket photos for MA 731 and MA 733.
# The API returns short-lived signed URLs; none are stored. Extra arguments name other plates (e.g. mc06858).
import sys, json, urllib.request
out=sys.argv[1]; API='https://api.starglass.cfa.harvard.edu/public'
def call(path,payload=None):
    req=urllib.request.Request(API+path,data=None if payload is None else json.dumps(payload).encode(),
        headers={'Content-Type':'application/json','Accept':'application/json','User-Agent':'curl/8'},method='GET' if payload is None else 'POST')
    return json.load(urllib.request.urlopen(req,timeout=120))
for p in (sys.argv[2:] or ['ma00731','ma00733']):
    m=call('/dasch/dr7/mosaic_package',{'plate_id':p,'binning':1})
    urllib.request.urlretrieve(m['baseFitsUrl'],f'{out}/{p}_mosaic.fits.fz')
    s=call(f'/plates/p/{p}')
    for j in s['jacket_images']: urllib.request.urlretrieve(j['url'],f"{out}/{p}_jacket_{j['portion']}.jpg")
    print(p,'exposures',json.dumps(s['exposures']))
