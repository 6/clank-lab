"""Exact byte and canonical JSON bindings for the S1 -> S2 -> S3 handoff."""
import hashlib,json,math
from pathlib import Path


def json_digest(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()).hexdigest()


def file_digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def authenticate(path,manifest_name):
    manifest=Path(__file__).parent.parent/'check_u1/current-inputs.sha256'
    pins={name:h for h,name in (line.split() for line in manifest.read_text().splitlines())}
    actual=file_digest(path)
    if actual!=pins[manifest_name]:raise ValueError('authoritative input digest mismatch: '+manifest_name)
    return actual


def model_data_hashes():
    root=Path(__file__).parent.parent
    names=('check_u1/inputs/u1_facets_p16.json','model_audit/q5_certificate.json',
           'model_audit/snub_certificate.json')
    return {name:file_digest(root/name) for name in names}


def scientific(value):
    """Parsed S23 output, omitting only measured execution times."""
    if isinstance(value, dict):
        for key in {'cpu_seconds', 'model_cpu_seconds', 'elapsed_seconds'} & value.keys():
            measured=value[key]
            if type(measured) not in (int,float) or not math.isfinite(measured) or measured < 0:
                raise ValueError('invalid observed S23 timing: '+key)
        return {k: scientific(v) for k, v in value.items()
                if k not in {'cpu_seconds', 'model_cpu_seconds', 'elapsed_seconds'}}
    if isinstance(value, list):
        return [scientific(v) for v in value]
    return value


def parsed_json(text):
    def unique(pairs):
        result={}
        for key,value in pairs:
            if key in result:raise ValueError('duplicate S23 JSON key: '+key)
            result[key]=value
        return result
    def nonfinite(value):raise ValueError('nonfinite S23 JSON: '+value)
    def finite_float(value):
        parsed=float(value)
        if not math.isfinite(parsed):raise ValueError('nonfinite S23 JSON number: '+value)
        return parsed
    return json.loads(text,object_pairs_hook=unique,parse_constant=nonfinite,parse_float=finite_float)


def scientific_records(path):
    text = Path(path).read_text().strip()
    if not text:
        return []
    data = parsed_json(text) if text.startswith('[') else [parsed_json(line) for line in text.splitlines() if line.strip()]
    records = data if isinstance(data, list) else [data]
    return [scientific(row) for row in sorted(records, key=lambda row: row['index'])]


def check_frozen_science(receipt, path, field='scientific_results'):
    records = scientific_records(path)
    if field in receipt:
        if json.dumps(scientific(receipt[field]),sort_keys=True,allow_nan=False) != json.dumps(records,sort_keys=True,allow_nan=False):
            raise ValueError('frozen scientific output differs: '+field)
    elif field == 'scientific_results':
        # Historical byte hashes are provenance only. Their scientific
        # class/open counts remain checked, followed by the full independent
        # coverage audit and reference-conclusion comparison at the callers.
        if receipt.get('classes') != len(records) or receipt.get('open') != sum(row['status']=='OPEN' for row in records):
            raise ValueError('historical receipt scientific counts differ')
    return records


def source_document(value):
    """Parsed provenance with historical prose entries omitted."""
    if isinstance(value,dict):
        return {k:source_document(v) for k,v in scientific(value).items()
                if Path(k).suffix.lower() not in {'.md','.tex','.pdf','.rst'}}
    if isinstance(value,list):return [source_document(v) for v in value]
    return value
