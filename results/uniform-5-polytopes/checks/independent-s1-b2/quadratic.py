"""Small exact ordered Q(sqrt(d)) field, independent of geometry software."""
from flint import fmpq
import sympy as sp


class Field:
    def __init__(self, d):
        self.d = d
        self.zero = (fmpq(0), fmpq(0))
        self.one = (fmpq(1), fmpq(0))

    def q(self, a=0, b=0):
        return (fmpq(a), fmpq(b))

    def add(self, x, y):
        return x[0]+y[0], x[1]+y[1]

    def neg(self, x):
        return -x[0], -x[1]

    def sub(self, x, y):
        return x[0]-y[0], x[1]-y[1]

    def mul(self, x, y):
        return x[0]*y[0]+self.d*x[1]*y[1], x[0]*y[1]+x[1]*y[0]

    def div(self, x, y):
        den = y[0]*y[0]-self.d*y[1]*y[1]
        if not (den != 0):
            raise AssertionError()
        return ((x[0]*y[0]-self.d*x[1]*y[1])/den,
                (x[1]*y[0]-x[0]*y[1])/den)

    def sum(self, terms):
        a = self.zero
        for b in terms:
            a = self.add(a, b)
        return a

    def sign(self, x):
        a, b = x
        if b == 0 or self.d == 0:
            return (a > 0)-(a < 0)
        if a == 0:
            return (b > 0)-(b < 0)
        if (a > 0) == (b > 0):
            return (a > 0)-(a < 0)
        sq = a*a-self.d*b*b
        return ((a > 0)-(a < 0))*((sq > 0)-(sq < 0))

    def expr(self, x):
        return sp.Rational(str(x[0]))+sp.Rational(str(x[1]))*sp.sqrt(self.d)

    def vecadd(self, x, y):
        return tuple(self.add(a,b) for a,b in zip(x,y))

    def vecsub(self, x, y):
        return tuple(self.sub(a,b) for a,b in zip(x,y))

    def scale(self, a, x):
        return tuple(self.mul(a,b) for b in x)

    def dot(self, x, y):
        return self.sum(self.mul(a,b) for a,b in zip(x,y))

    def solve(self, matrix, rhs):
        n = len(rhs)
        a = [list(row)+[b] for row,b in zip(matrix,rhs)]
        for j in range(n):
            k = next(k for k in range(j,n) if a[k][j] != self.zero)
            a[j],a[k] = a[k],a[j]
            v = a[j][j]
            a[j] = [self.div(x,v) for x in a[j]]
            for k in range(n):
                if k != j:
                    v = a[k][j]
                    a[k] = [self.sub(x,self.mul(v,y)) for x,y in zip(a[k],a[j])]
        return tuple(row[-1] for row in a)

    def rank(self, matrix):
        if not matrix:
            return 0
        a = [list(row) for row in matrix]
        k = 0
        for j in range(len(a[0])):
            pivot = next((i for i in range(k,len(a)) if a[i][j] != self.zero),None)
            if pivot is None:
                continue
            a[k],a[pivot] = a[pivot],a[k]
            v = a[k][j]
            a[k] = [self.div(x,v) for x in a[k]]
            for i in range(k+1,len(a)):
                v = a[i][j]
                a[i] = [self.sub(x,self.mul(v,y)) for x,y in zip(a[i],a[k])]
            k += 1
            if k == len(a):
                break
        return k
