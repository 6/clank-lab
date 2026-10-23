#!/usr/bin/env python3
"""Write the Lean transcription of data/d7k3.cert.  The certificate is copied verbatim
(n, m, the seven sorted (mu, r) pairs, the weights); nothing is computed here.

  CubelikeSC/Cert/Data/Nxxx.lean   the entries for one n, one definition each
  CubelikeSC/Cert/Check/Nxxx.lean  one kernel `decide` per entry, then their conjunction
  CubelikeSC/Cert/Cover/Nxxx.lean  every case (n, B, t) finds its entry: one kernel
                                   `decide` per t (over all B), then their union
  CubelikeSC/Cert/Certs.lean, Checked.lean, Covered.lean  the collectors

Kernel checks are split this finely to keep each declaration's memory small
(one `decide` per n needed over 16 GB at n >= 102).

usage: transcribe.py CERTFILE OUTDIR"""
import sys, os, collections
cert, out = sys.argv[1], sys.argv[2]
byn = collections.defaultdict(list)
for line in open(cert):
    if line.startswith('#'):
        assert 'units 1/15000 ' in line, line
        continue
    left, right = line.split(';')
    f = list(map(int, left.split()[1:]))
    assert len(f) == 16
    right = right.strip()
    w = [] if right == 'EMPTY' else [tuple(map(int, x.split(':'))) for x in right.split()]
    byn[f[0]].append((f[0], f[1], [(f[i], f[i + 1]) for i in range(2, 16, 2)], w))
assert sorted(byn) == list(range(128))
def lean(e):
    n, m, pr, w = e
    return '(%d, %d, [%s], [%s])' % (n, m, ', '.join('(%d, %d)' % p for p in pr),
                                     ', '.join('(%d, %d)' % x for x in w))
base = os.path.join(out, 'CubelikeSC/Cert')
for d in ('Data', 'Check', 'Cover'):
    os.makedirs(os.path.join(base, d), exist_ok=True)
HEAD = '-- Certificate transcription from data/d7k3.cert\n\nnamespace CubelikeSC.Cert\n\n'
TAIL = '\nend CubelikeSC.Cert\n'
def write(path, text):
    with open(os.path.join(base, path), 'w') as f: f.write(text)
for n in range(128):
    es = byn[n]; N = '%03d' % n
    names = ['e%s_%02d' % (N, i) for i in range(len(es))]
    write('Data/N%s.lean' % N, 'import CubelikeSC.Cert.Defs\n\n' + HEAD +
          ''.join('def %s : Entry := %s\n' % (nm, lean(e)) for nm, e in zip(names, es)) +
          '\ndef entries%s : List Entry := [%s]\n' % (N, ', '.join(names)) + TAIL)
    write('Check/N%s.lean' % N, 'import CubelikeSC.Cert.Data.N%s\n\n' % N + HEAD +
          ''.join('theorem c%s : %s.check = true := by decide +kernel\n' % (nm[1:], nm) for nm in names) +
          '\ntheorem check%s : entries%s.all Entry.check = true := by\n'
          '  simp only [entries%s, List.all_cons, List.all_nil, Bool.and_true, %s]\n' %
          (N, N, N, ', '.join('c' + nm[1:] for nm in names)) + TAIL)
    covs = ''.join(
        'theorem cov%s_%d : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ %d →\n'
        '    covered certs %d B ⟨%d, by decide⟩ = true := by decide +kernel\n' % (N, t, n, n, t)
        for t in range(8))
    write('Cover/N%s.lean' % N, 'import CubelikeSC.Cert.Key\nimport CubelikeSC.Cert.Certs\n\n' + HEAD +
          covs + '\ntheorem cov%s : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → ∀ t : Fin 8, B.card ≤ %d →\n'
          '    covered certs %d B t = true := by\n  intro B hB t hc\n  match t with\n' % (N, n, n) +
          ''.join('  | ⟨%d, _⟩ => exact cov%s_%d B hB hc\n' % (t, N, t) for t in range(8)) +
          '  | ⟨k + 8, h⟩ => exact absurd h (by omega)\n' + TAIL)
write('Certs.lean', ''.join('import CubelikeSC.Cert.Data.N%03d\n' % n for n in range(128)) + '\n' + HEAD +
      '/-- The certificate entries for `n` (`[]` for `n ≥ 128`). -/\ndef certs : Nat → List Entry\n' +
      ''.join('  | %d => entries%03d\n' % (n, n) for n in range(128)) + '  | _ => []\n' + TAIL)
write('Checked.lean', 'import CubelikeSC.Cert.Certs\n' +
      ''.join('import CubelikeSC.Cert.Check.N%03d\n' % n for n in range(128)) + '\n' + HEAD +
      'theorem certs_checked : ∀ n < 128, (certs n).all Entry.check = true := by\n'
      '  intro n hn\n  match n, hn with\n' +
      ''.join('  | %d, _ => exact check%03d\n' % (n, n) for n in range(128)) +
      '  | n + 128, h => exact absurd h (by omega)\n' + TAIL)
write('Covered.lean', ''.join('import CubelikeSC.Cert.Cover.N%03d\n' % n for n in range(128)) + '\n' + HEAD +
      'theorem all_covered : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → ∀ t : Fin 8, ∀ n < 128,\n'
      '    B.card ≤ n → covered certs n B t = true := by\n'
      '  intro B hB t n hn hc\n  match n, hn with\n' +
      ''.join('  | %d, _ => exact cov%03d B hB t hc\n' % (n, n) for n in range(128)) +
      '  | n + 128, h => exact absurd h (by omega)\n' + TAIL)
print('entries:', sum(len(v) for v in byn.values()))
