import numpy as np
from scipy import ndimage as nd
ra0,de0=np.radians(85.885),np.radians(16.017)
def std(rad,ded):
    a=np.radians(rad);d=np.radians(ded)
    c=np.sin(d)*np.sin(de0)+np.cos(d)*np.cos(de0)*np.cos(a-ra0)
    return np.degrees(np.cos(d)*np.sin(a-ra0)/c)*3600,np.degrees((np.sin(d)*np.cos(de0)-np.cos(d)*np.sin(de0)*np.cos(a-ra0))/c)*3600
def inv(xi,eta):
    xi=np.radians(np.asarray(xi)/3600);eta=np.radians(np.asarray(eta)/3600)
    den=np.cos(de0)-eta*np.sin(de0)
    return np.degrees(ra0+np.arctan2(xi,den))%360,np.degrees(np.arctan2(np.sin(de0)+eta*np.cos(de0),np.hypot(xi,den)))
def design(u,v,o=3): return np.array([u**i*v**j for i in range(o+1) for j in range(o+1-i)]).T
class Plate:
    def __init__(s,wd,pl):
        s.img=np.load(f'{wd}/cut{pl}.npy').astype(np.float32); ny,nx=s.img.shape
        z=np.load(f'{wd}/astrom{pl}.npz'); s.a=z['cxi']; s.b=z['cet']
        B=64; bm=np.median(s.img[:ny//B*B,:nx//B*B].reshape(ny//B,B,nx//B,B),axis=(1,3)); bm=nd.median_filter(bm,5)
        bg=nd.zoom(bm,(ny/bm.shape[0],nx/bm.shape[1]),order=1); bg=np.pad(bg,((0,ny-bg.shape[0]),(0,nx-bg.shape[1])),mode='edge')
        s.r=s.img-bg; s.ny,s.nx=ny,nx
    def pix2std(s,x,y):
        D=design((np.atleast_1d(x)-2100)/2000,(np.atleast_1d(y)-2100)/2000); return D @ s.a,D @ s.b
    def std2pix(s,xi,eta):
        xi=np.atleast_1d(np.asarray(xi,float)); eta=np.atleast_1d(np.asarray(eta,float))
        X=np.full(xi.shape,2100.);Y=np.full(xi.shape,2100.)
        for _ in range(10):
            f1,f2=s.pix2std(X,Y); e=0.01
            g1,g2=s.pix2std(X+e,Y); h1,h2=s.pix2std(X,Y+e)
            j11=(g1-f1)/e;j21=(g2-f2)/e;j12=(h1-f1)/e;j22=(h2-f2)/e; det=j11*j22-j12*j21
            dx=xi-f1; dy=eta-f2
            X+=( j22*dx-j12*dy)/det; Y+=(-j21*dx+j11*dy)/det
        return X,Y
    def sky2pix(s,ra,dec): return s.std2pix(*std(ra,dec))
    def pix2sky(s,x,y): return inv(*s.pix2std(x,y))
