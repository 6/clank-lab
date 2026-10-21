"""Strict task row grammar and canonical mathematical row digest."""
import re, hashlib
DEPTH=12
BATCH=4096
TOTAL=8*3**12
UINT=re.compile(r"0|[1-9][0-9]*")

def need(ok, message):
    if not ok:
        raise ValueError(message)

def bounds(index):
    return index * BATCH, min((index + 1) * BATCH, TOTAL)

def row(line, ident, depth=DEPTH, final=False):
    """Independently parse strict worker grammar, including continuation states."""
    need(type(line) is str and '\n' not in line and '\r' not in line, 'row line format')
    p = line.split(' ')
    need(len(p) >= 9 and all(p) and all(UINT.fullmatch(x) for x in p[:6]), 'row integer grammar')
    i, init, done, valid, nodes, solutions = map(int, p[:6])
    need(i == ident and i < 8 * 3**depth, 'row ID/coverage')
    need(init in (0, 1) and done in (0, 1) and valid in (0, 1), 'row flags')
    path, stack = p[6:8]
    path, stack = ('' if s == '-' else s for s in (path, stack))
    need(all(c in '012' for c in path) and all(c in '0123' for c in stack), 'continuation digits')
    need(depth + len(path) <= 24, 'continuation depth')
    need(UINT.fullmatch(p[8]) and all(UINT.fullmatch(x) for x in p[9:]), 'witness grammar')
    nw, points = int(p[8]), list(map(int, p[9:]))
    need(nw in (0, 121) and nw == len(points), 'witness length')
    need(not points or (solutions > 0 and points == sorted(set(points)) and points[-1] < 243), 'witness contents')
    if init == 0:
        need(not (done or valid or nodes or solutions or path or stack or points), 'pending state')
    elif done:
        need(not path and not stack, 'final continuation')
        need((valid == 1 and nodes > 0) or (valid == 0 and nodes == solutions == 0), 'final counters')
    else:
        need(valid == 1 and nodes > 0 and len(stack) == len(path) + 1, 'partial state')
        need(all(int(stack[j]) == int(path[j]) + 1 for j in range(len(path))), 'partial parent choices')
    if final:
        need(init == done == 1 and nw == 0 and solutions == 0, 'negative final row required')
    return init, done, valid, nodes, solutions

def rows_summary(rows, first, stop, final=True):
    need(type(rows) is list and len(rows) == stop - first, 'row count/coverage')
    totals = dict(covered=0, valid=0, nodes=0, solutions=0)
    h = hashlib.sha256()
    for ident, line in enumerate(rows, first):
        init, done, valid, nodes, solutions = row(line, ident, final=final)
        totals['covered'] += done
        totals['valid'] += valid
        totals['nodes'] += nodes
        totals['solutions'] += solutions
        h.update(f'{ident} {valid} {nodes} {solutions}\n'.encode('ascii'))
    return totals, h.hexdigest()

def range_entry(index, rows):
    first, stop = bounds(index)
    totals, hashed = rows_summary(rows, first, stop)
    return dict(range=index, first=first, stop=stop, valid=totals['valid'],
                nodes=totals['nodes'], solutions=totals['solutions'], rows_sha256=hashed)
