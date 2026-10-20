"""Replay the named primary P16 programs using only this public bundle.

Each part has its own fresh output directory. --part all runs every part;
separate invocations may distribute independent parts across machines.
The numerical kernels are unchanged. Outputs, logs and timings stay outside
this source tree. A zero process status alone never establishes acceptance.
"""
import argparse
import ast
from collections import Counter
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
PRIMARY = HERE / 'primary'
BUNDLE = HERE.parent


def require(ok, why):
    if not ok:
        raise ValueError(why)


def load(path):
    return json.loads(Path(path).read_text())


def read_gzip(path):
    return json.loads(gzip.decompress(Path(path).read_bytes()))


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class Replay:
    def __init__(self, out, jobs):
        self.out = out.resolve()
        self.out.mkdir(parents=True, exist_ok=False)
        self.jobs = jobs
        self.records = []
        self.env = dict(os.environ, U5_EXACT_INPUT_ROOT=str(PRIMARY),
                        OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1',
                        PYTHONDONTWRITEBYTECODE='1', PYTHONOPTIMIZE='')

    def run(self, name, script, *args, cwd=None):
        log = self.out / (name + '.log')
        start = time.monotonic()
        with log.open('w') as stream:
            result = subprocess.run([sys.executable, str(script), *map(str, args)],
                                    cwd=cwd or self.out, env=self.env,
                                    stdout=stream, stderr=subprocess.STDOUT)
        self.records.append(dict(step=name, exit_code=result.returncode,
                                 wall_seconds=time.monotonic()-start,
                                 log=log.name))
        (self.out/'commands.json').write_text(json.dumps(self.records, indent=2)+'\n')
        require(result.returncode == 0, name+' failed; inspect '+log.name)
        print('PASS execution '+name, flush=True)
        return log

    def library(self):
        for filename, args in [('cert_facets4.py', (16,'A4,B4,D4,F4,H4')),
                               ('cert_stage1_5d.py',(16,)),
                               ('exact_angles.py',(16,)),
                               ('class_filter.py',(16,))]:
            self.run(filename[:-3], PRIMARY/'enum'/filename, *args)
        facets=load(self.out/'cert_facets4_p16.json')
        cycles=load(self.out/'cert_stage1_5d_p16.json')
        classes=load(self.out/'classes_p16.json')
        flat=load(self.out/'exact_flat_p16.json')
        boundary=load(self.out/'exact_boundary_p16.json')
        require(len(facets)==181 and len(cycles)==14965, 'library/S1 inventory')
        require(len(flat['flat'])==7080 and not flat['failed'], 'flat exclusions')
        require(len(boundary['degenerate'])==57 and not boundary['unhandled'], 'endpoint exclusions')
        require(sum(bool(c['alive']) for c in classes)==563, 'surviving classes')
        pins={p:h for h,p in (s.split() for s in (HERE/'check_u1/current-inputs.sha256').read_text().splitlines())}
        for stem in ['cert_stage1_5d','exact_flat','exact_boundary','classes']:
            path=self.out/(stem+'_p16.json')
            require(hashlib.sha256(path.read_bytes()).hexdigest()==pins['producer-p16/'+path.name], 'regenerated input differs: '+stem)
        self.run('input-link',PRIMARY/'input_link/compare_legacy.py',self.out/'cert_facets4_p16.json',16,'--selftest')
        aliases=self.out/'facet-aliases.json'
        aliases.write_text(json.dumps([dict(name=f['name'],aliases=f['aliases']) for f in facets]))
        self.run('merge',PRIMARY/'check_merge/run.py','--facets',aliases)
        self.run('exact-inputs-a',PRIMARY/'repair-exact-inputs/check_inputs.py',PRIMARY/'repair-exact-inputs/inputs.json')
        self.run('exact-inputs-b',PRIMARY/'repair-exact-inputs/check_inputs_b.py',PRIMARY/'repair-exact-inputs/inputs.json')
        ridges=self.run('ridges',PRIMARY/'enum/cert_ridges.py',16)
        rows=[json.loads(s) for s in ridges.read_text().splitlines() if s.strip()]
        require(len(rows)==181 and all(r['status']=='certified' for r in rows), 'ridge certificates incomplete')
        self.run('ridge-corruptions',PRIMARY/'enum/cert_ridges.py','--corrupt')
        self.run('omega',PRIMARY/'enum/export_omega.py','--input-dir',self.out,'--output',self.out/'u5_omega_p16.json')
        require(load(self.out/'u5_omega_p16.json')==load(HERE/'acceptance-third/infinite/outputs/enum/u5_omega_p16.json'), 'unfiltered Omega differs')
        print('PASS primary library/S1: 181 models, 14965 cycles, 563 surviving classes; exact inputs, aliases, ridges and Omega',flush=True)

    def s23(self):
        self.run('unpack', HERE/'independent-s23/unpack_inputs.py', self.out/'input','--pmax',16)
        classes=load(self.out/'input/u2_classes_p16.json')
        expected=read_gzip(BUNDLE/'data/primary-u2-signatures-p16.json.gz')
        self.run('s2',PRIMARY/'check_u2/run.py',self.out/'input/u2_classes_p16.json',self.out/'signatures.json',
                 '--jobs',self.jobs,'--prebuild','--stats',self.out/'s2-stats.json')
        actual=load(self.out/'signatures.json')
        spec=module('primary_replay_acceptance',PRIMARY/'stage2/replay_all.py')
        spec.require_certified_completions(load(self.out/'s2-stats.json'),actual)
        key=lambda v:json.dumps(v,sort_keys=True,separators=(',',':'))
        keyed=lambda rows:{r['index']:{key(v):v for v in r['vfs']} for r in rows}
        require(keyed(actual)==keyed(expected),'primary S2 full signature difference')
        require(len(actual)==563 and sum(len(c['vfs']) for c in actual)==629,'primary S2 counts')
        # Freeze only presentation order from the published source; every
        # signature has just been regenerated and compared in full.
        generated=keyed(actual);radii={c['index']:c['R'] for c in classes}
        vfs=[dict(index=c['index'],R=radii[c['index']],
                  vfs=[generated[c['index']][key(v)] for v in c['vfs']]) for c in expected]
        (self.out/'vfs.json').write_text(json.dumps(vfs))
        for checker in ['audit_certificates.py','check_equivalences.py']:
            self.run(checker[:-3],PRIMARY/'stage2'/checker,PRIMARY/'stage2/equivalences-p16.json','--corruptions')
        self.run('s3',PRIMARY/'check_u3/run.py',self.out/'vfs.json',self.out/'input/u3_known_p16.json',self.out/'result_p16.json','--jobs',self.jobs)
        result=load(self.out/'result_p16.json');summary=result['summary']
        for k,n in dict(classes=563,vertex_figures=629,realisations=629,search_states=633,
                        verdict_KNOWN=628,verdict_REFUTED=1,unique_root=629,forced=629,
                        known_names_matched=890,distinct_known_polytopes=628).items():
            require(summary.get(k)==n,'primary S3 count: '+k)
        for k in ['search_undecided','development_undecided','model_guard_undecided','verdict_OPEN','vf_errors','vf_without_realisation','known_unmatched']:
            require(summary.get(k,0)==0,'primary S3 unresolved: '+k)
        for k in ['known_names_in_no_class','known_outside_library','known_without_exact_count','facet_type_mismatches']:
            require(summary.get(k)==[],'primary S3 model admission: '+k)
        require(result['model_guard']['active'] is True,'primary S3 guard inactive')
        audit=module('primary_radius_audit',PRIMARY/'check_u3/audit_radius_route.py')
        # The public class file is the authenticated final class interval.
        # C8 independently checks its containment of the S1 class hull.
        producer=[dict(alive=False) for _ in range(max(radii)+1)]
        for c in classes:producer[c['index']]=dict(alive=True,R=c['R'])
        radius=audit.audit(producer,vfs,result)
        require(radius['status']=='PASS','primary radius coverage')
        (self.out/'radius-audit.json').write_text(json.dumps(radius,indent=2)+'\n')
        self.run('radius-corruptions',PRIMARY/'check_u3/audit_radius_route.py','--selftest')
        bridge=HERE/'report_bridge.py'
        self.run('lean-report-bridge',bridge,'--primary-report',self.out/'result_p16.json','--signatures',self.out/'vfs.json')
        self.run('lean-report-corruptions',HERE/'test_report_bridge.py',
                 '--primary-report',self.out/'result_p16.json','--signatures',self.out/'vfs.json')
        print('PASS primary S2/S3: 563 classes, 629 signatures, 628 KNOWN, 1 REFUTED, 890 names; every ROOT and forcing check passed',flush=True)

    def caseb(self):
        omega=HERE/'acceptance-third/infinite/outputs/enum/u5_omega_p16.json'
        log=self.run('b2',PRIMARY/'check_b2/b2check.py',omega,'--audit',self.out/'b2-roots.json')
        text=log.read_text()
        counts=[ast.literal_eval(line.split(': ',1)[1]) for line in text.splitlines() if line.startswith('counts (n, configuration) pairs: ')]
        require(counts==[dict(i=496824,ii=150495,iii=1905)] and 'COINCIDENCES: 0' in text,'primary B2 outcome accounting')
        self.run('b2-root-audit',PRIMARY/'check_b2/check_root_audit.py',self.out/'b2-roots.json','--corruptions')
        data=load(self.out/'b2-roots.json')
        require(not data['undecided'],'B2 unresolved')
        fam=self.run('p1',PRIMARY/'enum/caseb_famfilter.py')
        text=fam.read_text()
        degenerate=[ast.literal_eval(line.split(' ',1)[1]) for line in text.splitlines() if line.startswith('CLOSABILITY-UNDECIDED ')]
        require(set(degenerate)=={(3,3,4),(3,4,6),(3,5,10)} and len(degenerate)==3,'unexpected primary P1 undecided case')
        # These three endpoint equalities are supplied by the written exact
        # chord identities; confirm them algebraically instead of counting
        # an undecided numerical status as a successful exclusion.
        import sympy as sp
        x=sp.Symbol('x')
        for a,b,c in degenerate:
            residual=4*sp.cos(sp.pi/a)**2+4*sp.cos(sp.pi/b)**2-4*sp.cos(sp.pi/c)**2
            require(sp.Poly(sp.minimal_polynomial(residual,x),x).monic().all_coeffs()==[1,0],'P1 degenerate identity')
        require('configurations 168, closable 137, with family polygon and excluded 67,' in text,'primary P1 inventory')
        self.run('partner-repairs',PRIMARY/'enum/caseb_wedge/wpoint.py')
        print('PASS primary B2, P1 and seven partner repairs',flush=True)

    def wedge(self):
        inventory=self.run('wedge-inventory',PRIMARY/'enum/caseb_wedge/wrun.py','list')
        self.run('wedge',PRIMARY/'enum/caseb_wedge/wrun.py','all','-j',self.jobs,'-o',self.out/'wedge.jsonl')
        rows=[json.loads(s) for s in (self.out/'wedge.jsonl').read_text().splitlines()]
        counts=Counter(r['status'].split(' (')[0] for r in rows)
        require(len(rows)==228 and len({r['fan'] for r in rows})==228 and {r['fan'] for r in rows}==set(inventory.read_text().splitlines()),'W inventory')
        require(counts==dict(CERTIFIED=184,**{'NOT CLOSABLE':31},DEGENERATE=3,FAILED=10),'W outcomes: '+str(counts))
        expected={'pi:38,3,7','pi:39,3,7','pi:40,3,7','pi:41,3,7','pi:23,3,8','pi:17,3,9','pi:19,4,5','i:3,11,13','i:4,7,9','i:5,6,7'}
        require({r['fan'] for r in rows if r['status']=='FAILED'}==expected,'unexpected W failure')
        p1=self.run('wedge-p1-exclusions',PRIMARY/'enum/caseb_famfilter.py')
        excluded={ast.literal_eval(line[len('EXCLUDED '):].split(' by q=',1)[0]) for line in p1.read_text().splitlines() if line.startswith('EXCLUDED ')}
        require(len(excluded)==67 and {(3,11,13),(4,7,9),(5,6,7)}<=excluded,'unrepaired supplementary W failure lacks a P1 exclusion')
        self.run('wedge-corruptions',PRIMARY/'enum/caseb_wedge/wcorrupt.py')
        self.run('partner-repairs',PRIMARY/'enum/caseb_wedge/wpoint.py')
        print('PASS primary W: 228 rows; 184 certified, 31 nonclosable, 3 degenerate, 10 expected full-domain failures; seven repairs certified',flush=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--jobs',type=int,default=2)
    ap.add_argument('--part',choices=['all','library','s23','caseb','wedge'],default='all')
    a=ap.parse_args();require(a.jobs>=1,'positive worker count required')
    parts=['library','s23','caseb','wedge'] if a.part=='all' else [a.part]
    if a.part=='all':a.out.mkdir(parents=True,exist_ok=False)
    for part in parts:
        r=Replay(a.out/part if a.part=='all' else a.out,a.jobs)
        getattr(r,part)()
    print('PASS primary replay '+a.part)


if __name__=='__main__':
    main()
