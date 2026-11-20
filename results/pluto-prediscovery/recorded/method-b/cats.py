# Gaia DR3 within 0.75 deg of Pluto's December 1908 position, G < 19.5
import sys
from astroquery.gaia import Gaia
out=sys.argv[1]
q="""SELECT source_id, ra, dec, pmra, pmdec, parallax, phot_g_mean_mag, bp_rp, ra_error, dec_error
FROM gaiadr3.gaia_source WHERE 1=CONTAINS(POINT('ICRS',ra,dec), CIRCLE('ICRS',85.885,16.017,0.75)) AND phot_g_mean_mag<19.5"""
t=Gaia.launch_job_async(q).get_results(); t.write(out+'/gaia.fits',overwrite=True); print('gaia',len(t))
