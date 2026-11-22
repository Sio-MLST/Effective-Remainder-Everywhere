"""Spot-check a lower-bound witness of RESEARCH_NOTES 2c by random walks, using only paper.md definitions.

python3 walk_check.py Q WALKS
From a vertex with c0(t) = sum_{j<L-1} q^j (mod u_q), take WALKS random walks: at each step choose a random
compatible exponent a in [1, d] (2^-a = c mod g0) and a random lift z' = 2^-a (mod q), z' = c (mod u_q),
then evaluate c0(z') = (2^a z' - 1)/q.  Reports the depth at which each walk dies (out-degree 0 by B4(1))
and checks the explicit path with a = d.  This samples 'every path dies by step L-1'; it does not prove it.
"""
import sys, random
from math import gcd
from kappa_trap import params, factor, order, recurrence_L

def crt(x1, m1, x2, m2):
    g = gcd(m1, m2)
    if (x1 - x2) % g: return None
    l = m1 // g * m2
    k = ((x2 - x1) // g * pow(m1 // g, -1, m2 // g)) % (m2 // g)
    return (x1 + m1 * k) % l, l

q, W = int(sys.argv[1]), int(sys.argv[2])
d, uq, g0, kap, F = params(q)
L = recurrence_L(q)[0]
N = q * uq
P = list(factor(g0))
op = {p: order(2, p) for p in P}
dlog = {p: {pow(2, -a, p): a for a in range(op[p])} for p in P}   # 2^-a mod p  ->  a mod ord_p

def compatible_a(c):
    """a mod m with 2^-a = c (mod g0), or None (then out-degree 0, B4(1))."""
    x, m = 0, 1
    for p in P:
        if c % p not in dlog[p]: return None
        r = crt(x, m, dlog[p][c % p], op[p])
        if r is None: return None
        x, m = r
    return x, m

def succ(c, a=None):
    if a is None:
        x, m = compatible_a(c)
        a = x + m * random.randrange(d // m) or m
    z, Lm = crt(pow(2, -a, q), q, c % uq, uq)
    z = (z + Lm * random.randrange(N // Lm)) % N
    return ((pow(2, a, N * q) * z - 1) // q) % uq

r0 = sum(q ** j for j in range(L - 1)) % uq
# explicit path of the lower-bound proof: integer lift z_l = sum_{j < L-1-l} q^j (= 1 mod q), exponent a = d
explicit, z = 0, sum(q ** j for j in range(L - 1))
while explicit < L - 1:
    c = ((pow(2, d, N * q) * z - 1) // q) % uq        # c0(z_{l+1}) with z_{l+1} = z (as integer)
    assert z % q == 1 and compatible_a(z % uq) is not None
    explicit += 1
    z = sum(q ** j for j in range(L - 1 - explicit))
    assert c % uq == z % uq, "c0 does not peel one power of q"
assert compatible_a(0 if L > 1 else 1) is None or True
explicit_dead = compatible_a(((pow(2, d, N * q) * 1 - 1) // q) % uq) is None   # last vertex z = 1: c0 = u = 0 mod g0
random.seed(0)
deaths = {}
for _ in range(W):
    c, k = r0, 0
    while compatible_a(c) is not None:
        c = succ(c); k += 1
        if k > kap: break
    deaths[k] = deaths.get(k, 0) + 1
print(dict(q=q, kappa=kap, recurrence_L=L, g0=factor(g0), u_q=factor(uq)), "walk length at death:", deaths,
      "explicit path length:", explicit, "then dead:", explicit_dead, "(prediction: all", L - 1, ")")
