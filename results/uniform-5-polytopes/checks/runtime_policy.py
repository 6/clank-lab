"""Runtime acceptance: input/checker identities and parsed scientific outputs.

Historical hashes in receipts are provenance, not output acceptance gates.
Only named timing fields are omitted; verdicts, counts and all other fields
remain part of the comparison. No search implementation is imported here.
"""
import argparse
import ast
from collections import Counter
import gzip
import hashlib
import json
import math
from pathlib import Path
import re

TIMING_FIELDS = frozenset({
    'cpu', 'cpu_seconds', 'model_cpu_seconds', 'wall_seconds', 'elapsed_seconds',
    'wall_s', 'elapsed_s', 'cpu_user_s', 'cpu_system_s', 'user_seconds',
    'system_seconds', 'time_wall_s', 'started_utc', 'finished_utc',
    'peak_rss_kib', 'max_rss_kib', 'max_rss_kib_children',
})


def hashed_input(name, authoritative=()):
    path = Path(name)
    # A manifest cannot promote prose, a receipt, or a generated report to
    # an acceptance prerequisite simply by listing a digest for it.
    if path.suffix.lower() in {'.md', '.tex', '.pdf', '.rst'}:
        return False
    return (path.suffix in {'.py', '.sh', '.lean', '.c', '.h'}
            or path.name.endswith('requirements.txt') or name in authoritative)


def verify_inputs(root, pins, authoritative=()):
    checked = {}
    for name, record in pins.items():
        if not hashed_input(name, authoritative):
            continue
        expected = record if isinstance(record, str) else record['sha256']
        actual = hashlib.sha256((Path(root)/name).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError('runtime input identity mismatch: ' + name)
        checked[name] = expected
    return checked


def scientific(value, ignore=()):
    omitted = TIMING_FIELDS | set(ignore)
    if isinstance(value, dict):
        for key, measured in value.items():
            if key in TIMING_FIELDS:
                if key in {'started_utc', 'finished_utc'}:
                    if not isinstance(measured, str):
                        raise ValueError('invalid observed timestamp: '+key)
                elif type(measured) not in (int, float) or not math.isfinite(measured) or measured < 0:
                    raise ValueError('invalid observed timing/resource value: '+key)
        return {k: scientific(v, ignore) for k, v in value.items() if k not in omitted}
    if isinstance(value, list):
        return [scientific(v, ignore) for v in value]
    return value


def parse_json(text):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError('duplicate JSON key: '+key)
            result[key] = value
        return result
    def nonfinite(value):
        raise ValueError('nonfinite JSON value: '+value)
    def finite_float(value):
        parsed = float(value)
        if not math.isfinite(parsed):
            raise ValueError('nonfinite JSON number: '+value)
        return parsed
    return json.loads(text, object_pairs_hook=unique, parse_constant=nonfinite, parse_float=finite_float)


def load_json(path):
    path = Path(path)
    text = (gzip.decompress(path.read_bytes()).decode() if path.suffix == '.gz'
            else path.read_text())
    try:
        return parse_json(text)
    except json.JSONDecodeError:
        return [parse_json(line) for line in text.splitlines() if line.strip()]


def compare_json(expected, actual, ignore=()):
    normalized=lambda path: json.dumps(scientific(load_json(path), ignore),sort_keys=True,allow_nan=False)
    if normalized(expected) != normalized(actual):
        raise ValueError('scientific output differs: ' + str(actual))


def _literal(value):
    if isinstance(value, dict):
        return ('dict', sorted([(_literal(k), _literal(v)) for k, v in value.items()], key=repr))
    if isinstance(value, (tuple, list)):
        return (type(value).__name__, [_literal(v) for v in value])
    return value


def text_science(text):
    lines = []
    for line in text.splitlines():
        if re.match(r'^\s*(?:CPU seconds|Total CPU|elapsed seconds)\b', line):
            continue
        def literal(match):
            try:
                return repr(_literal(ast.literal_eval(match.group())))
            except (ValueError, SyntaxError):
                return match.group()
        line = re.sub(r'[\[{].*[\]}]', literal, line)
        if line.strip():
            lines.append(tuple(line.split()))
    return Counter(lines)


def compare_text(expected, actual):
    if text_science(Path(expected).read_text()) != text_science(Path(actual).read_text()):
        raise ValueError('scientific text output differs: ' + str(actual))



def integer_records(path):
    return sorted(tuple(map(int, line.split(','))) for line in Path(path).read_text().splitlines() if line.strip())

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('json', 'text', 'inputs'))
    parser.add_argument('expected', type=Path)
    parser.add_argument('actual', type=Path)
    parser.add_argument('--ignore', action='append', default=[])
    parser.add_argument('--authoritative', action='append', default=[])
    args = parser.parse_args()
    if args.mode == 'inputs':
        pins = {name: digest for digest, name in
                (line.split(maxsplit=1) for line in args.expected.read_text().splitlines() if line.strip())}
        verify_inputs(args.actual, pins, args.authoritative)
    elif args.mode == 'json':
        compare_json(args.expected, args.actual, args.ignore)
    else:
        compare_text(args.expected, args.actual)


if __name__ == '__main__':
    main()
