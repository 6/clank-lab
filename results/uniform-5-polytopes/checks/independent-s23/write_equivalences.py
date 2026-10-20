"""Emit exact correspondence equivalence witnesses for independent checking."""
import argparse,json
from pathlib import Path
from models import facet
from stage2 import equivalences


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('classes',type=Path);p.add_argument('output',type=Path)
    a=p.parse_args();classes=json.loads(a.classes.read_text())
    names={name for c in classes for cy in c['cycles'] for name in cy['facets']}
    certificates={n:equivalences(facet(n))[1] for n in sorted(names)}
    a.output.write_text(json.dumps(certificates,sort_keys=True)+'\n')
    print(json.dumps({'models':len(names),'retained':sum(len(c['retained']) for c in certificates.values()),
                      'ordered_options':sum(len(c['options']) for c in certificates.values())}))


if __name__=='__main__':main()
