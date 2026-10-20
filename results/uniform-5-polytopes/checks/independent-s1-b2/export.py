"""Outward-rounded evaluation and standalone, reproducible JSON export."""
from functools import lru_cache
import json
import sympy as sp
from flint import arb,fmpq,ctx


@lru_cache(None)
def evaluate(expr,bits=200):
    """Evaluate the mathematical expression as an Arb enclosure, never float."""
    if ctx.prec < bits:
        raise ValueError('precision must be set before evaluation')
    expr = sp.sympify(expr)
    if expr.is_Rational:
        return arb(fmpq(int(expr.p),int(expr.q)))
    if expr == sp.pi:
        return arb.pi()
    if isinstance(expr,sp.CRootOf):
        interval = expr._get_interval().refine_size(sp.Rational(1,2**(bits+40)))
        a,b = fmpq(str(interval.a)),fmpq(str(interval.b))
        return arb(a).union(arb(b))
    if expr.is_Add:
        return sum((evaluate(t,bits) for t in expr.args),arb(0))
    if expr.is_Mul:
        result = arb(1)
        for t in expr.args:
            result *= evaluate(t,bits)
        return result
    if expr.is_Pow:
        base,exponent = expr.args
        x = evaluate(base,bits)
        if exponent.is_Integer:
            return x**int(exponent)
        if exponent == sp.Rational(1,2):
            if not (x >= 0):
                raise AssertionError(('uncertified square root sign',expr,x))
            return x.sqrt()
        if exponent == -sp.Rational(1,2):
            if not (x > 0):
                raise AssertionError()
            return 1/x.sqrt()
        if exponent.is_Rational:
            if not (x > 0):
                raise AssertionError()
            return (evaluate(exponent,bits)*x.log()).exp()
    if expr.func in (sp.sin,sp.cos):
        x = evaluate(expr.args[0],bits)
        return x.sin() if expr.func == sp.sin else x.cos()
    raise ValueError(('unsupported expression',expr))


def bracket(ball):
    if not (ball.is_finite()):
        raise AssertionError()
    return [str(ball.lower().fmpq()),str(ball.upper().fmpq())]


def encode_record(record,bits):
    result = dict(record)
    radius2 = record['radius_squared']
    radius_ball = evaluate(radius2,bits)
    if not (radius_ball > 0):
        raise AssertionError()
    result['radius_squared'] = str(radius2)
    result['radius_squared_bracket'] = bracket(radius_ball)
    result['radius_bracket'] = bracket(radius_ball.sqrt())
    result['words'] = []
    from library import word_cosine
    for word in record['words']:
        cosine = word['cos_alpha']
        ball = evaluate(cosine,bits)
        if not (ball > -1 and ball < 1):
            raise AssertionError()
        if not (ball <= arb(1)/2):
            raise AssertionError(('angle below pi/3',record['name'],word))
        from library import polygon_radius_squared,cell_radius_squared
        rp2 = polygon_radius_squared(word['p'])
        T = evaluate(radius2-rp2,bits)
        a = evaluate(cell_radius_squared(word['A'])-rp2,bits)
        b = evaluate(cell_radius_squared(word['B'])-rp2,bits)
        if not (a > 0 and b > 0 and T-a > 0 and T-b > 0):
            raise AssertionError()
        # Different derivation: normal-based exact cosines must intersect
        # the word-angle formula derived only from the circumradii.
        other = evaluate(word_cosine(radius2,word['p'],word['A'],word['B']),bits)
        if not (ball.overlaps(other)):
            raise AssertionError(('normal/radius disagreement',record['name'],word))
        result['words'].append({**word,'cos_alpha':str(cosine),
                                'cos_alpha_bracket':bracket(ball),
                                'alpha_bracket':bracket(ball.acos())})
    return result


def export_library(path,bits=200,announce=True):
    from library import library_records,cell_radius_squared
    ctx.prec = bits+64
    records = library_records()
    labels = sorted({label for r in records for w in r['words'] for label in (w['A'],w['B'])})
    data = {'schema':'independent-facets-v1','precision_bits':bits,
            'arithmetic_precision_bits':ctx.prec,
            'counts':{'types':len(records),'words':sum(len(r['words']) for r in records),
                      'occurrences':sum(w['multiplicity'] for r in records for w in r['words'])},
            'cell_radius_squared':{label:{'expression':str(cell_radius_squared(label)),
                                          'bracket':bracket(evaluate(cell_radius_squared(label),bits))}
                                   for label in labels},
            'records':[encode_record(r,bits) for r in records]}
    with open(path,'w') as handle:
        json.dump(data,handle,sort_keys=True,indent=2)
        handle.write('\n')
    if announce:
        print(json.dumps({'status':'CERTIFIED','counts':data['counts'],'output':str(path)},sort_keys=True))
    return data
