#!/usr/bin/env python3
"""Independent positive join control at order 65, unit 5200, with 32-bit keys.

Usage: collision_check.py DATADIR TRUNCATED_RECEIPTDIR [--corruptions | --wrong-match-count]
The NumPy row/filter implementation is independent of the production search.
The specified key constants and definition are shared, no search code is.
"""
import importlib.util
from pathlib import Path
import sys
import numpy as np

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('independent_unit', Path(__file__).with_name('unit_recheck.py'))
independent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(independent)


def require(condition, description):
    if not condition:
        raise ValueError(description)


def coefficients():
    state = 0x5713a1d2c0ffee65
    mask = (1 << 64)-1
    result = []
    for _ in range(33):
        state = (state+0x9e3779b97f4a7c15) & mask
        value = state
        value = ((value ^ (value >> 30))*0xbf58476d1ce4e5b9) & mask
        value = ((value ^ (value >> 27))*0x94d049bb133111eb) & mask
        result.append((value ^ (value >> 31)) | 1)
    return np.array(result[1:], dtype=np.uint64)


def main():
    endings = []
    for path in Path(sys.argv[2]).glob('batch_*.tsv'):
        for line in path.read_text().splitlines():
            if line.startswith('END\t'):
                require('pair=1 xor=1 kmin=1 keybits=32' in line, 'incorrect positive-control options')
                endings.append(line.split('\t')[1:3])
    require(endings == [['5200', '5201']], 'missing or incorrect completion marker')
    independent.setup(65, 5, sys.argv[1], sys.argv[2])
    state = independent.G
    state['W'] = coefficients()
    receipt = state['rec'][5200]
    require(set(state['rec']) == {5200}, 'expected exactly the fixed control unit')
    require(receipt[11] == 1, 'control must finish in one pass')
    lists = []
    for position, cid in enumerate(state['units'][5200]):
        count, offset = state['cls'][cid]
        masks = np.array(state['rows'][offset:offset+count], dtype=np.uint32)
        if position == receipt[6]:
            masks = independent.kmin(masks)
        lists.append(independent.rowdata(masks))
    sizes = [len(item['mask']) for item in lists]
    require(sizes == receipt[7:11], 'list sizes disagree')
    pairing = independent.PAIRS[receipt[5]]
    a, b, c, d = (lists[i] for i in pairing)
    la, lb = independent.side_pairs(a, b, c, d)
    ra, rb = independent.side_pairs(c, d, a, b)
    left_product, right_product = len(a['mask'])*len(b['mask']), len(c['mask'])*len(d['mask'])
    expected = receipt[14:16] if left_product < right_product else receipt[14:16][::-1]
    require([len(la), len(ra)] == expected, 'survivor counts disagree')
    with np.errstate(over='ignore'):
        mix = np.uint64(0xd6e8feb86659fd93)
        full = np.uint64(0xffffffff)
        left = (a['h'][la]+b['h'][lb]) ^ (mix*(a['mask'][la]^b['mask'][lb]).astype(np.uint64))
        right = (np.uint64(0)-(c['h'][ra]+d['h'][rb])) ^ (mix*((c['mask'][ra]^d['mask'][rb]).astype(np.uint64)^full))
        left &= full; right &= full
        left[left == 0] = 1; right[right == 0] = 1
    li = np.argsort(left); ri = np.argsort(right)
    ls, rs = left[li], right[ri]
    common = np.intersect1d(ls, rs)
    matches = solutions = 0
    for key in common:
        left_ids = li[np.searchsorted(ls, key, 'left'):np.searchsorted(ls, key, 'right')]
        right_ids = ri[np.searchsorted(rs, key, 'left'):np.searchsorted(rs, key, 'right')]
        matches += len(left_ids)*len(right_ids)
        right_paf = c['paf'][ra[right_ids]]+d['paf'][rb[right_ids]]
        for i in left_ids:
            sums = right_paf+a['paf'][la[i]]+b['paf'][lb[i]]
            solutions += int((~sums.any(axis=1)).sum())
    expected_matches = receipt[16]+('--wrong-match-count' in sys.argv[3:])
    require(matches > 0 and matches == expected_matches, 'positive key-match count disagrees')
    require(solutions == receipt[17] == 0, 'exact solution count disagrees')
    print(f'PASS positive_join n=65 unit=5200 keybits=32 sizes={sizes} survivors={[len(la),len(ra)]} matches={matches} solutions={solutions}', flush=True)
    if '--corruptions' in sys.argv[3:]:
        try:
            require(matches > 0 and matches == receipt[16]+1, 'positive key-match count disagrees')
        except ValueError:
            print('PASS rejected modified expected key-match count', flush=True)
        else:
            raise ValueError('modified expected key-match count was accepted')


if __name__ == '__main__':
    try:
        main()
    except ValueError as error:
        print('REJECT:', error)
        sys.exit(1)
