import sys, numpy as np, json
wd=sys.argv[1]
K={'731':(201.9,274.8),'733':(186.4,350.8)}            # from the (179) trail fit, minutes after 21:00 UT
A={'731':(556.6-30,556.6+30),'733':(589.2-90.5,589.2+90.5)}  # archive midpoint +/- half logged duration
names={'1436':'Salonta','2891':'McGetchin','4204':'Barsig','2175':'Andrea Doria','3147':'Samantha','9593':'1991 PZ17','13567':'Urabe','25493':'1999 XG85','179':'Klytaemnestra'}
for aid in ['179','1436','2891','4204','2175','3147','9593','13567','25493']:
    for pl in ['731','733']:
        try: z=np.load(f'{wd}/trailS_{pl}_{aid}.npz')
        except Exception: print(pl,aid,'missing'); continue
        T,S,Sc=z['T'],z['S'],z['Sc']
        def stat(SS,t1,t2,offs):
            vals=[]
            for o in offs:
                s=SS[o]; m=(T>=t1)&(T<=t2)&np.isfinite(s)
                if m.sum()<0.5*((T>=t1)&(T<=t2)).sum() or m.sum()<5: vals.append(np.nan); continue
                vals.append(np.median(s[m])-np.nanmedian(s))
            return np.nanmax(vals) if np.any(np.isfinite(vals)) else np.nan
        on=range(2,7)  # offsets -2..+2 px
        def null(t1,t2):
            L=t2-t1; out=[]
            for st in np.arange(T.min(),T.max()-L,5.0):
                if st+L>t1-5 and st<t2+5: continue   # exclude windows overlapping the tested one
                out.append(stat(S,st,st+L,on))
            for st in np.arange(T.min(),T.max()-L,5.0):
                out.append(stat(Sc,st,st+L,range(0,5)))
            return np.array([o for o in out if np.isfinite(o)])
        res={}
        for lab,(t1,t2) in [('K',K[pl]),('archive',A[pl])]:
            v=stat(S,t1,t2,on); n=null(t1,t2)
            res[lab]=(v,(n>=v).mean() if np.isfinite(v) else np.nan,len(n),np.median(n),1.4826*np.median(np.abs(n-np.median(n))))
        k=res['K'];a=res['archive']
        print(f"{pl} {aid:>5} {names[aid]:<13} K-window: excess {k[0]:7.1f} p={k[1]:.3f} (z={(k[0]-k[3])/k[4]:5.1f}, n={k[2]}) | archive-window: excess {a[0]:7.1f} p={a[1]:.3f} (z={(a[0]-a[3])/a[4]:5.1f})")
