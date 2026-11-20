import sys, numpy as np
wd=sys.argv[1]
L={'731':72.9,'733':164.3}
faint=['1436','2891','4204','2175','3147','9593','13567','25493']
def hh(m): t=21*60+m; t%=1440; return f'{int(t//60):02d}:{t%60:04.1f}'
for pl in ['731','733']:
    starts=np.arange(-60,900,2.0); tot=np.zeros(len(starts)); cnt=np.zeros(len(starts))
    for aid in faint:
        z=np.load(f'{wd}/trailS_{pl}_{aid}.npz'); T,S=z['T'],z['S']
        prof=[]
        for st in starts:
            v=[]
            for o in range(2,7):
                s=S[o]; m=(T>=st)&(T<=st+L[pl])&np.isfinite(s)
                v.append(np.median(s[m])-np.nanmedian(s) if m.sum()>=10 else np.nan)
            prof.append(np.nanmax(v) if np.any(np.isfinite(v)) else np.nan)
        prof=np.array(prof); ok=np.isfinite(prof)
        if ok.sum()<50: continue
        zs=(prof-np.nanmedian(prof))/(1.4826*np.nanmedian(np.abs(prof-np.nanmedian(prof))))
        tot[ok]+=zs[ok]; cnt[ok]+=1
    sc=tot/np.sqrt(np.maximum(cnt,1))
    good=cnt>=4
    i=np.argmax(np.where(good,sc,-1e9))
    mid=starts[i]+L[pl]/2
    # half-max width of the peak
    srt=np.sort(sc[good])[::-1]
    print(pl,'faint-asteroid stack peak mid',hh(mid),'UT score',round(sc[i],1),'n_ast',int(cnt[i]),'next-best score away (>60 min) ',round(np.max(sc[good & (np.abs(starts-starts[i])>60)]),1))
    above=good&(sc>sc[i]/2); print('   windows with >half peak score: mid',hh(starts[above].min()+L[pl]/2),'to',hh(starts[above].max()+L[pl]/2))
