import sys
from astroquery.vizier import Vizier
import astropy.units as u
from astropy.coordinates import SkyCoord
out=sys.argv[1]
V=Vizier(columns=['RAJ2000','DEJ2000','Bmag','e_Bmag','Vmag','e_Vmag','B-V'],row_limit=-1)
V.VIZIER_SERVER="vizier.cfa.harvard.edu"
r=V.query_region(SkyCoord(85.885,16.017,unit='deg'),radius=0.75*u.deg,catalog='II/336/apass9')
r[0].write(out+'/apass.fits',overwrite=True); print('apass',len(r[0]))
from astropy.table import Table
print('gaia',len(Table.read(out+'/gaia.fits')))
