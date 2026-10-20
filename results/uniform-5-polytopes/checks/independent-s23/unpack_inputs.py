"""Materialize only the inputs needed for replay; authenticate original bytes."""
import argparse,gzip,hashlib,json
from pathlib import Path


def unpack(output,pmax):
    here=Path(__file__).resolve().parent
    original={p:h for h,p in (line.split() for line in (here.parent/'check_u1/current-inputs.sha256').read_text().splitlines())}
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    entries=json.loads((here/'inputs/manifest.json').read_text())
    for row in entries:
        if not row['source_manifest_path'].startswith(f'producer-p{pmax}/'):continue
        data=gzip.decompress((here/'inputs'/row['file']).read_bytes())
        actual=hashlib.sha256(data).hexdigest()
        if actual!=row['decompressed_sha256'] or actual!=original[row['source_manifest_path']]:
            raise ValueError('input digest mismatch')
        (output/row['file'][:-3]).write_bytes(data)
    if pmax==6:
        data=(here.parent/'check_u3/inputs/u3_known_p6.json').read_bytes()
        if hashlib.sha256(data).hexdigest()!=original['producer-p6/u3_known_p6.json']:
            raise ValueError('known-name digest mismatch')
        (output/'u3_known_p6.json').write_bytes(data)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('output');p.add_argument('--pmax',type=int,choices=[6,10,16],required=True)
    a=p.parse_args();unpack(a.output,a.pmax)
