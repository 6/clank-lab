#!/usr/bin/env python3
"""Render actual coordinate witnesses into fully checked Lean constructions.

The renderer is untrusted: partition, all grid-neighbor coverage, pattern
matching, and exact certificate assembly are rechecked by Lean's kernel.
Input directory: palette.json plus witnesses/{width-N,direct-Hx5}.json.
No receipt, search code, Python checker or solver is imported.
"""
import argparse
import hashlib
import json
from pathlib import Path


def cells(xs):
    return '[' + ','.join(f'({r},{c})' for r,c in xs) + ']'


def canon(xs):
    return tuple(sorted(map(tuple,xs)))


def shifted(xs,d):
    return tuple((r+d[0],c+d[1]) for r,c in xs)


def adjacent(a,b):
    return any(abs(r-s)+abs(c-t)==1 for r,c in a for s,t in b)


def normalized(a,b):
    d=(min(r for r,c in a+b),min(c for r,c in a+b))
    aa=shifted(a,(-d[0],-d[1])); bb=shifted(b,(-d[0],-d[1]))
    return tuple(sorted((aa,bb))),d,aa>bb


def load(path):
    data=json.loads(path.read_text())
    blocks=data['blocks']
    if not isinstance(blocks,dict) or not blocks:
        raise ValueError(f'{path.name}: missing blocks')
    for name,b in blocks.items():
        for key in ['height','width']:
            if type(b[key]) is not int or b[key]<=0: raise ValueError('invalid dimension')
        for tile in b['tiles']:
            if len(tile)!=3 or any(len(x)!=2 or any(type(v) is not int for v in x) for x in tile):
                raise ValueError('invalid tile coordinates')
        b['tiles']=[canon(t) for t in b['tiles']]
    for orientation in ['vertical','horizontal']:
        seams=data[orientation]
        if len({tuple(s) for s in seams})!=len(seams): raise ValueError('duplicate seam')
        for a,b in seams:
            if a not in blocks or b not in blocks: raise ValueError('unknown seam block')
            if blocks[a]['width' if orientation=='vertical' else 'height']!=blocks[b]['width' if orientation=='vertical' else 'height']:
                raise ValueError('incompatible seam dimensions')
    return data


def seam_offset(data,orientation,a):
    b=data['blocks'][a]
    return (b['height'],0) if orientation=='vertical' else (0,b['width'])


def pair_sets(data):
    bs=data['blocks']
    for b in bs.values():
        yield b['tiles'],b['tiles']
    for orientation in ['vertical','horizontal']:
        for a,b in data[orientation]:
            yield bs[a]['tiles'],[shifted(t,seam_offset(data,orientation,a)) for t in bs[b]['tiles']]


def header(module='Catalog'):
    return [f'import Generated.{module}', '', 'namespace LockedTromino.Witnesses',
            'set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', '']


def entries(name,source,target,index):
    lines=[f'def {name} : List EntryData := [']
    for xs in source:
        links=[]
        for ys in target:
            if xs==ys or not adjacent(xs,ys): continue
            p,d,flip=normalized(xs,ys)
            links.append(f'⟨{cells(ys)},{index[p]},({d[0]},{d[1]}),{str(flip).lower()}⟩')
        lines.append(f'  ⟨{cells(xs)},['+','.join(links)+']⟩,')
    lines.append(']')
    lines.extend([f'theorem {name}_match : CatalogLinksCheck catalog {name} := by decide +kernel',
                  f'theorem {name}_links : CertifiedLinks (localEntries {name}) :=',
                  f'  catalogLinks_sound catalog_sound {name}_match',''])
    return lines


def make_catalog(patterns):
    lines=['import CatalogCertificate','','namespace LockedTromino.Witnesses',
           'set_option maxRecDepth 1000000','set_option maxHeartbeats 0','']
    for i,(a,b) in enumerate(patterns):
        lines.extend([f'def pattern_{i} : Pattern := ({cells(a)},{cells(b)})',
                      f'theorem pattern_{i}_check : SubsetPairCheck pattern_{i}.1 pattern_{i}.2 := by decide +kernel',
                      f'theorem pattern_{i}_rigid : Rigid (Cells pattern_{i}.1) (Cells pattern_{i}.2) :=',
                      f'  subsetPairCheck_sound pattern_{i}_check',''])
    lines.extend(['def patterns : List Pattern := ['+','.join(f'pattern_{i}' for i in range(len(patterns)))+']',
                  'def catalog (k : Nat) : Pattern := patterns[k]?.getD pattern_0',
                  'theorem patterns_sound : ∀ p ∈ patterns, Rigid (Cells p.1) (Cells p.2) := by',
                  '  intro p hp',
                  '  simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hp',
                  '  rcases hp with '+' | '.join(f'h{i}' for i in range(len(patterns)))])
    for i in range(len(patterns)):
        lines.append(f'  · subst p; exact pattern_{i}_rigid')
    lines.extend(['theorem catalog_sound : ∀ k, Rigid (Cells (catalog k).1) (Cells (catalog k).2) :=',
                  '  catalog_getD_sound patterns_sound pattern_0_rigid',
                  '', 'end LockedTromino.Witnesses',''])
    return '\n'.join(lines)


def render_module(data,module,index):
    lines=header()
    bs=data['blocks']; ids={name:f'{module}_b{i}' for i,name in enumerate(bs)}
    for name,b in bs.items():
        ident=ids[name]; h,w=b['height'],b['width'];ts=b['tiles']
        lines.extend(entries(ident+'_entries',ts,ts,index))
        lines.extend([f'def {ident}_tiles := EntryTiles (localEntries {ident}_entries)'])
        owners={cell:i for i,tile in enumerate(ts) for cell in tile}
        table=[owners.get((r,c),0) for r in range(h) for c in range(w)]
        lines.extend([f'def {ident}_owner : Cell → List Cell := tableOwner {w} {ident}_tiles ['+','.join(map(str,table))+']',
                      f'theorem {ident}_partition : OwnerPartitionCheck {h} {w} {ident}_tiles {ident}_owner := by decide +kernel',
                      f'theorem {ident}_cover : EdgeCoverCheck (localEntries {ident}_entries) {ident}_owner 0 0 {h} {w} := by decide +kernel',
                      f'def {ident} : RigidBlock {h} {w} :=',
                      f'  localCheckedBlock {ident}_partition {ident}_entries_links {ident}_cover',''])
    for orientation in ['vertical','horizontal']:
        for i,(a,b) in enumerate(data[orientation]):
            an,bn=ids[a],ids[b];d=seam_offset(data,orientation,a)
            ident=f'{module}_{orientation}_{i}'
            lines.extend(entries(ident+'_entries',bs[a]['tiles'],[shifted(t,d) for t in bs[b]['tiles']],index))
            lines.extend([f'theorem {ident}_same : EntryTiles (localEntries {ident}_entries) = {an}_tiles := by rfl',
                f'theorem {ident}_cover : EdgeCoverCheck (localEntries {ident}_entries)',
                f'    (shiftOwner ({d[0]},{d[1]}) {bn}_owner) {d[0]} {d[1]} {bs[b]["height"]} {bs[b]["width"]} := by decide +kernel',
                f'theorem {ident} : ∀ A B, {an}.tiles A → {bn}.tiles B → Rigid A (Shift ({d[0]},{d[1]}) B) := by',
                f'  have hp := localSeam_rigid (h := {bs[a]["height"]}) (w := {bs[a]["width"]})',
                f'    ({ident}_same.symm ▸ {an}.partition) {bn}_partition',
                f'    {ident}_entries_links {ident}_cover',
                f'    (side_disjoint {bs[a]["height"]} {bs[a]["width"]} {bs[b]["height"]} {bs[b]["width"]}).'+('1' if orientation=='vertical' else '2'),
                f'  rw [{ident}_same] at hp', '  exact hp',''])
    if module.startswith('Width'):
        h0,h1=(9,12) if module=='Width5' else (6,9)
        w=next(iter(bs.values()))['width']
        bydim={(b['height'],b['width']):ids[name] for name,b in bs.items()}
        a,b=bydim[(h0,w)],bydim[(h1,w)]
        lines.extend([f'def {module}_palette : VerticalPalette (fun h => h = {h0} ∨ h = {h1}) {w} where',
            f'  tiles h := if h = {h0} then {a}.tiles else {b}.tiles',
            '  partition := by','    intro h hh', '    rcases hh with rfl | rfl',
            f'    · exact {a}.partition', f'    · exact {b}.partition',
            '  internal := by','    intro h hh', '    rcases hh with rfl | rfl',
            f'    · exact {a}.internal', f'    · exact {b}.internal',
            '  vertical := by','    intro h k hh hk',
            '    rcases hh with rfl | rfl <;> rcases hk with rfl | rfl'])
        seam_ids={(bs[an]['height'],bs[bn]['height']):i for i,(an,bn) in enumerate(data['vertical'])}
        for hh in [h0,h1]:
            for hk in [h0,h1]:
                lines.append(f'    · exact {module}_vertical_{seam_ids[(hh,hk)]}')
    elif module=='Tail':
        dims={(b['height'],b['width']):ids[name] for name,b in bs.items()}
        lines.extend(['def tailPalette : Palette (fun h => h = 6 ∨ h = 9) (fun w => w = 8 ∨ w = 9) where',
          f'  tiles h w := if h = 6 then (if w = 8 then {dims[(6,8)]}.tiles else {dims[(6,9)]}.tiles)',
          f'    else (if w = 8 then {dims[(9,8)]}.tiles else {dims[(9,9)]}.tiles)'])
        for field in ['partition','internal']:
            lines.extend([f'  {field} := by','    intro h w hh hw','    rcases hh with rfl | rfl <;> rcases hw with rfl | rfl'])
            for h in [6,9]:
                for w in [8,9]:lines.append(f'    · exact {dims[(h,w)]}.{field}')
        lines.extend(['  vertical := by','    intro h k w hh hk hw',
          '    rcases hh with rfl | rfl <;> rcases hk with rfl | rfl <;> rcases hw with rfl | rfl'])
        seams={(bs[a]['height'],bs[b]['height'],bs[a]['width']):i for i,(a,b) in enumerate(data['vertical'])}
        for h in [6,9]:
            for k in [6,9]:
                for w in [8,9]:lines.append(f'    · exact Tail_vertical_{seams[(h,k,w)]}')
        lines.extend(['  horizontal := by','    intro h w v hh hw hv',
          '    rcases hh with rfl | rfl <;> rcases hw with rfl | rfl <;> rcases hv with rfl | rfl'])
        seams={(bs[a]['height'],bs[a]['width'],bs[b]['width']):i for i,(a,b) in enumerate(data['horizontal'])}
        for h in [6,9]:
            for w in [8,9]:
                for v in [8,9]:lines.append(f'    · exact Tail_horizontal_{seams[(h,w,v)]}')
    lines.extend(['','end LockedTromino.Witnesses',''])
    return '\n'.join(lines)


def final_module():
    modules=['Tail','Direct6','Direct15']+[f'Width{w}' for w in range(4,56)]
    lines=[f'import Generated.{m}' for m in modules]
    lines.extend(['','namespace LockedTromino.Witnesses',
      'def actualCertificate : ProposedCertificate where',
      '  small := by','    intro w hlo hhi hne'])
    for w in [w for w in range(4,56) if w!=5]:
        lines.extend([f'    by_cases h{w} : w = {w}',f'    · subst w; exact Width{w}_palette'])
    lines.extend(['    omega',
      '  five := ⟨Direct6_b0, Direct15_b0, Width5_palette⟩',
      '  tail := tailPalette','',
      '/-- Exact universal construction, with no finite-certificate hypotheses. -/',
      'theorem locked_tromino_rectangles (m n : Nat) (hm : 6 ≤ m) (hd : 3 ∣ m) (hn : 4 ≤ n) :',
      '    ∃ T, Locked (Rectangle m n) T :=',
      '  universal_of_proposed_certificate actualCertificate m n hm hd hn','',
      '#print axioms locked_tromino_rectangles','',
      'end LockedTromino.Witnesses',''])
    return '\n'.join(lines)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path)
    parser.add_argument('output',type=Path)
    parser.add_argument("--check", action="store_true", help="compare regenerated sources without writing")
    args=parser.parse_args()
    records=[('Tail',args.input/'palette.json'),('Direct6',args.input/'witnesses/direct-6x5.json'),
             ('Direct15',args.input/'witnesses/direct-15x5.json')]
    records += [(f'Width{w}',args.input/f'witnesses/width-{w}.json') for w in range(4,56)]
    loaded=[(m,p,load(p)) for m,p in records]
    patterns=set()
    for _,_,data in loaded:
        for aa,bb in pair_sets(data):
            for a in aa:
                for b in bb:
                    if a!=b and adjacent(a,b):patterns.add(normalized(a,b)[0])
    patterns=sorted(patterns);index={p:i for i,p in enumerate(patterns)}
    if not args.check: args.output.mkdir(parents=True,exist_ok=True)
    outputs={'Catalog.lean':make_catalog(patterns),'Universal.lean':final_module()}
    for module,_,data in loaded:outputs[f'{module}.lean']=render_module(data,module,index)
    for name,text in outputs.items():
        if len(text.encode())>=2_000_000:raise ValueError(f'{name} exceeds file cap')
        if args.check:
            if (args.output/name).read_text() != text: raise ValueError(f"stale generated source: {name}")
        else:
            (args.output/name).write_text(text)
    manifest={'patterns':len(patterns),'modules':len(outputs),
       'inputs':{str(p.relative_to(args.input)):hashlib.sha256(p.read_bytes()).hexdigest() for _,p,_ in loaded},
       'outputs':{name:hashlib.sha256(text.encode()).hexdigest() for name,text in outputs.items()}}
    manifest_text=json.dumps(manifest,indent=2)+'\n'
    if args.check:
        if (args.output/'manifest.json').read_text()!=manifest_text: raise ValueError('stale manifest')
        if {p.name for p in args.output.glob('*.lean')}!=set(outputs): raise ValueError('extra generated Lean source')
    else:
        (args.output/'manifest.json').write_text(manifest_text)
    print(json.dumps({'patterns':len(patterns),'modules':len(outputs),'bytes':sum(len(t.encode()) for t in outputs.values()),
                      'max_file_bytes':max(len(t.encode()) for t in outputs.values())}))


if __name__=='__main__': main()
