import sys, numpy as np
from astropy.io import fits
from astropy.wcs import WCS
fn, out = sys.argv[1], sys.argv[2]
h=fits.open(fn); hd=h[1].header
w=WCS(hd, naxis=2)
x,y=w.all_world2pix(85.885,16.017,0)
print('seed pix', x,y)
x,y=int(round(float(x))),int(round(float(y)))
H=2100
d=h[1].data
y0,y1=max(0,y-H),min(d.shape[0],y+H); x0,x1=max(0,x-H),min(d.shape[1],x+H)
sub=np.array(d[y0:y1,x0:x1])
print('cut',x0,x1,y0,y1,sub.shape,sub.dtype,np.percentile(sub,[1,50,99]))
np.save(out+'.npy',sub)
open(out+'.off','w').write(f'{x0} {y0}\n')
