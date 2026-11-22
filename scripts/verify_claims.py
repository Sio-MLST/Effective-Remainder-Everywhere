"""Re-check every computational claim of RESEARCH_NOTES.md.  Run:  python3 scripts/verify_claims.py [--big] [--scan]

Each check prints  PASS <id>  or raises AssertionError.  IDs match the claim table in VERIFY.md.
Default run: ~10 s.  --big adds C7 (q = 221898711, ~20 s, ~1.5 GB RAM, needs numpy).
--scan adds C6 (all odd q <= 12000, ~1-3 min).

Independence: D-checks use ONLY the definitions of paper.md section 1 (V_q, c_0, G_q) -- no Lemma B7,
no closed form.  The fast algorithm (kappa_trap.depth_sets) is then compared against them.
"""
import sys, os
from fractions import Fraction
from math import gcd
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kappa_trap import params, order, factor, depth_sets, report


def ok(tag, cond, msg=""):
    assert cond, f"FAIL {tag} {msg}"
    print("PASS", tag, msg)


def vp(n, p):
    k = 0
    while n % p == 0:
        n //= p; k += 1
    return k


# ---------- definition-level depth computation (paper.md section 1, nothing else) ----------
def definition_depths(q):
    """Return (kappa, d, uq, list over k of #vertices of V_q with a path of length >= k)."""
    d, uq, g0, kap, _ = params(q)
    N = q * uq
    H = {pow(2, i, q) for i in range(d)}
    V = [z for z in range(N) if gcd(z, N) == 1 and z % q in H]
    a0 = {}
    for i in range(1, d + 1):
        a0[pow(2, -i, q)] = i          # 2^{a0} z = 1 mod q
    c0 = {z: ((pow(2, a0[z % q], N * q) * z - 1) // q) % uq for z in V}
    alive = set(V)                     # path of length >= 0
    counts = [len(alive)]
    for _ in range(kap):
        cls = {z % uq for z in alive}  # classes mod u_q containing a vertex with path >= k-1
        alive = {z for z in alive if c0[z] in cls}   # edge z -> z' iff z' = c0(z) mod u_q
        counts.append(len(alive))
    return kap, d, uq, counts


# ---------- D1: fast algorithm == definitions ----------
for q in (21, 57, 111, 489, 7959, 10887, 11571):
    kap, d, uq, counts = definition_depths(q)
    R, _ = depth_sets(q)
    ok(f"D1[{q}]", counts == [d * len(r) for r in R], f"vertex counts {counts}")

# ---------- C1: table of RESEARCH_NOTES 1.3 ----------
expect = {21: (1, Fraction(4, 21), [3, 2], 2), 57: (1, Fraction(4, 19), [9, 6, 6], 18),
          7959: (2, Fraction(24, 2653), [189, 54, 36, 36], 162),
          10533: (2, Fraction(912600, 12327121), [94797, 31590, 21060, 21060], 31590),
          10887: (2, Fraction(120, 3629), [171, 54, 36], 54),
          11571: (2, Fraction(16, 3857), [63, 18, 12], 18)}
for q, (kt, dens, sizes, ev) in expect.items():
    info, _ = report(q)
    ok(f"C1[{q}]", (info["kappa_trap"], info["delta_dense"], info["sizes"], info["evals_per_step"]) == (kt, dens, sizes, ev),
       f"kappa_trap={kt} delta={dens}")
ok("C1[11571 counts]", (252 * 18, 252 * 6) == (4536, 1512))

# ---------- C2: hand-proof inputs for 10533 (RESEARCH_NOTES 2) ----------
q = 10533
ok("C2a", q == 3 * 3511 and order(2, 3511) == 1755 and factor(1755) == {3: 3, 5: 1, 13: 1})
ok("C2b", pow(2, 3510, 3511 ** 2) == 1 and pow(2, 3510, 3511 ** 3) != 1, "3511 Wieferich, v=2 exactly")
d, uq, g0, kap, _ = params(q)
ok("C2c", (d, uq, g0, kap) == (3510, 27 * 3511, 10533, 3), "d, u_q, g0, kappa")
ok("C2d", pow(2, 3510, 81) == 1 and order(2, g0) == 3510, "2^d=1 mod 81; ord_g0(2)=3510")
ok("C2e", g0 % 3511 == 0 and d % 3511 != 0, "the B10 gap: p1=3511 | g0 but p1 does not divide d")

# ---------- C3: hand-proof inputs for 221898711 (RESEARCH_NOTES 2a) ----------
r = 21067
ok("C3a", all(r % p for p in range(2, int(r ** .5) + 1)) and order(2, r) == 21066 == 2 * 3 * 3511, "r prime, ord")
ok("C3b", pow(2, 21066, r * r) != 1, "r not Wieferich")
ok("C3c", all(not (all(x % p for p in range(2, int(x ** .5) + 1)) and order(2, x) % 3511 == 0)
             for x in range(2 * 3511 + 1, r, 2 * 3511)), "r is the least such prime")
q = 3 * 3511 * r
d, uq, g0, kap, _ = params(q)
ok("C3d", (q, d, uq, g0, kap) == (221898711, 12323610, 27 * 3511 ** 2, 10533, 3))
M = 81 * 3511 ** 2
ok("C3e", pow(2, 3510, M) == 1, "every multiple of 3510 has 2^a = 1 mod 3^4*3511^2")
# step 1 and 2 on actual vertices: build z1, z2 by CRT and evaluate c0 from the definition
def crt(x1, m1, x2, m2):
    g = gcd(m1, m2); assert (x1 - x2) % g == 0
    l = m1 // g * m2
    k = ((x2 - x1) // g * pow(m1 // g, -1, m2 // g)) % (m2 // g)
    return (x1 + m1 * k) % l, l
N = q * uq
def c0_of(z, a):   # a = a0(z): 2^a z = 1 mod q
    assert pow(2, a, q) * z % q == 1
    return ((pow(2, a, N * q) * z - 1) // q) % uq
import random
random.seed(1)
for a in random.sample(range(3510, d + 1, 3510), 6):           # all compatible a are multiples of 3510
    z1, L = crt(pow(2, -a, q), q, (1 + q) % uq, uq)
    for lift in range(3):
        z = (z1 + lift * L) % N
        c1 = c0_of(z, a)
        ok(f"C3f[a={a},lift={lift}]", c1 % (9 * 3511) == 1, "c0(z1) = 1 mod 9*3511")
        for a2 in random.sample(range(3510, d + 1, 3510), 3):
            z2, L2 = crt(pow(2, -a2, q), q, c1, uq)
            ok(f"C3f2[a2={a2}]", c0_of(z2, a2) % 3 == 0, "c0(z2) = 0 mod 3  (dead end)")
ok("C3f3", all(pow(2, -a, g0) != 1 for a in range(1, 3510)), "compatibility with 1 mod g0 forces 3510 | a")
ok("C3g", ((1 + q) - 1) // q == 1, "(2^a z1 - 1)/q = ((1+q)-1)/q = 1 mod 9*3511 since 2^a z1 = z1 mod 3^3*3511^2")
ok("C3h", (pow(2, 3510, 81) * 1 - 1) % 9 == 0, "step 2: z2 = 1 mod 9, 2^a = 1 mod 81 => 9 | 2^a z2 - 1 => 3 | c0(z2)")

# ---------- C4: [MMMM13] Theorem 3.1 counterexamples ----------
def gen_size(b, gens=(2, 3)):
    S, fr = {1}, [1]
    while fr:
        x = fr.pop()
        for g in gens:
            y = x * g % b
            if y not in S:
                S.add(y); fr.append(y)
    return len(S)
def thm31(b):
    from math import lcm
    out = 1
    for p, e in factor(b).items():
        out *= lcm(order(2, p ** e), order(3, p ** e))
    return out
bad = [b for b in range(5, 300, 2) if b % 3 and gen_size(b) != thm31(b)]
ok("C4", bad[:6] == [95, 119, 143, 145, 215, 217] and gen_size(95) == 36 and thm31(95) == 72, f"first failures {bad[:6]}")

# ---------- C5: L10 facts: T_5 cycles, thresholds, translation identity ----------
from math import log
def T5(x): return (5 * x + 1) // 2 if x % 2 else x // 2
def cyc(s):
    c, x = [], s
    while True:
        c.append(x); x = T5(x)
        if x == s: return c
c1, c2 = cyc(1), cyc(13)
ok("C5a", (len(c1), sum(v % 2 for v in c1)) == (5, 2) and (len(c2), sum(v % 2 for v in c2)) == (7, 3))
ok("C5b", log(2) / log(5 + 1 / 13) < 3 / 7 < log(2) / log(5))
ok("C5c", all(abs((rr / (1 + rr)) - log(2) / log(2 * qq)) < 1e-12 for qq in (3, 5, 21) for rr in [log(2) / log(qq)]),
   "compressed threshold ln2/ln q <-> uncompressed ln2/ln 2q")
for qq in (3, 5, 7, 21):
    for b in (5 * 7 * 11 * 13 + 2, 1001, 9973):
        if gcd(b, 2 * qq) != 1: continue
        i2, iq = pow(2, -1, b), pow(qq, -1, b)
        T0 = lambda x: x * i2 % b
        T1 = lambda x: (qq * x + 1) * i2 % b
        T1i = lambda y: (2 * y - 1) * iq % b
        T0i2 = lambda x: 4 * x % b
        ok(f"C5d[q={qq},b={b}]", all(T0i2(T1(T0(T1i(T0(x))))) == (x + 1) % b for x in range(0, b, 37)))

# ---------- C6 (--scan): uncapped scan q <= 12000 ----------
if "--scan" in sys.argv:
    hits, n = [], 0
    for q in range(3, 12001, 2):
        if params(q)[3] < 2: continue
        n += 1
        info, _ = report(q)
        if info["kappa_trap"] >= 2: hits.append(q)
    ok("C6", (n, hits) == (280, [7959, 10533, 10887, 11571]), f"{n} q with kappa>=2; hits {hits}")

# ---------- C7 (--big): kappa_trap(221898711) = 3 ----------
if "--big" in sys.argv:
    from kappa_trap import depth_sets_np
    info = depth_sets_np(221898711)
    ok("C7", info["sizes"] == [332832267, 110912490, 36960300, 24640200] and info["kappa_trap"] == 3, str(info["sizes"]))
print("all requested checks passed")
