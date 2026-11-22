"""Compute kappa_trap(q) and delta_dense(q) (SUPPLEMENTS_B, section 5; RESEARCH_NOTES, section 1).

Usage:
  python3 kappa_trap.py 11571 10887        # report for given q
  python3 kappa_trap.py --check 11571      # also compare with the independent residue-graph brute force
  python3 kappa_trap.py --np 221898711     # numpy version for large u_q
  python3 kappa_trap.py --scan 12000       # all odd q <= bound with kappa >= 2, list those with kappa_trap >= 2

No assumption of Rules 1-3 is made. 2^d - 1 is never formed as an integer.
"""
import sys
from fractions import Fraction
from math import gcd


def factor(n):
    f, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def order(a, n):
    """Multiplicative order of a mod n (gcd(a, n) = 1), via the Carmichael function."""
    if n == 1:
        return 1
    from math import lcm
    lam = 1
    for p, e in factor(n).items():
        lam = lcm(lam, (p - 1) * p ** (e - 1) if p != 2 else (1 if e == 1 else 2 if e == 2 else 2 ** (e - 2)))
    o = lam
    for p in factor(lam):
        while o % p == 0 and pow(a, o // p, n) == 1:
            o //= p
    return o


def params(q):
    """d, u_q, g_0, kappa, factorization of q."""
    d, F = order(2, q), factor(q)
    uq, kap = 1, 0
    for p, al in F.items():
        k = al  # v_p(2^d - 1) >= alpha_p since q | 2^d - 1
        while pow(2, d, p ** (k + 1)) == 1:
            k += 1
        nu = k - al
        uq *= p ** nu
        kap = max(kap, -(-nu // al))
    return d, uq, gcd(q, uq), kap, F


def depth_sets(q):
    """R_k = residues r = c_0(z) mod u_q of vertices with a path of length >= k, k = 0..kappa.

    Uses the closed form r*(a, b) of RESEARCH_NOTES 1.1 (from Lemma B7)."""
    d, uq, g0, kap, F = params(q)
    us = uq // g0
    qs = 1
    for p in factor(us):
        qs *= p ** F[p]
    qp, up, e0 = q // qs, qs * us, order(2, uq)
    R = [set(range(uq))]
    for _ in range(kap):
        proj = {r % us for r in R[-1]}
        new = set()
        for a in range(e0):
            b0 = pow(2, -a, g0)
            for j in range(us):
                b = (b0 + j * g0) % uq
                if b in R[-1]:
                    rs = ((((pow(2, a) * b - 1) % up) // qs) * pow(qp, -1, us)) % us if us > 1 else 0
                    if rs in proj:
                        new.add(b)
        R.append(new)
        if R[-1] == R[-2]:
            R.extend([new] * (kap + 1 - len(R)))
            break
    return R, (d, uq, g0, kap, e0 * us)


def depth_sets_np(q, truncate=False):
    """Same iteration as depth_sets, with numpy boolean arrays indexed by b in [0, u_q).

    For large u_q (e.g. 3^3 * 3511^2). Returns (sizes of R_0..R_kappa, info, last-step difference sizes)."""
    import numpy as np
    d, uq_full, g0, kap, F = params(q)
    uq = truncated_modulus(q) if truncate else uq_full
    us = uq // g0
    qs = 1
    for p in factor(us):
        qs *= p ** F[p]
    qp, up, e0 = q // qs, qs * us, order(2, uq)
    assert up < 2 ** 31
    inv = pow(qp, -1, us) if us > 1 else 0
    j = np.arange(us, dtype=np.int64)
    R = np.ones(uq, dtype=bool)
    sizes, diffs = [uq], []
    for _ in range(kap):
        proj = R.reshape(g0, us).any(axis=0)       # b = i*us + s  ->  b mod us = s
        new = np.zeros(uq, dtype=bool)
        for a in range(e0):
            b = (pow(2, -a, g0) + j * g0) % uq
            num = (pow(2, a, up) * (b % up) - 1) % up
            rs = ((num // qs) % us) * inv % us
            ok = R[b] & proj[rs]
            new[b[ok]] = True
        diffs.append(int((R & ~new).sum()))
        R = new
        sizes.append(int(R.sum()))
    kt = 1 + max([0] + [k for k in range(1, kap) if sizes[k] > sizes[k + 1]])
    return dict(q=q, d=d, u_q=uq_full, modulus_used=uq, g0=g0, kappa=kap, sizes=sizes, kappa_trap=kt,
                delta_dense=Fraction(d * sizes[-1], q * uq), evals_per_step=e0 * us)


def _vexp(p, e):
    """v_p(2^e - 1) without forming 2^e - 1."""
    k = 0
    while pow(2, e, p ** (k + 1)) == 1:
        k += 1
    return k


def formula_two_prime(q):
    """Gemini's closed form for kappa_trap when g0 = p0*p1 (distinct primes), RESEARCH_NOTES 2b.
    Returns (L*, s, omega) or None if g0 is not a product of two distinct primes or kappa = 0."""
    d, uq, g0, kap, F = params(q)
    G = factor(g0)
    if kap < 1 or len(G) != 2 or any(e != 1 for e in G.values()):
        return None
    o = order(2, g0)
    s, om = {}, {}
    for p in G:
        sig = max(0, _vexp(p, d) - 2 * F[p])          # nu - alpha
        om[p] = _vexp(p, order(2, p)) - 1             # Wieferich excess
        s[p] = 0 if sig == 0 else min(_vexp(p, o) - 1, sig)
    (p0, s0), (p1, s1) = s.items()
    L = 1 + min(s0, s1)
    if s0 != s1:
        hi = p0 if s0 > s1 else p1
        L += 1 + min(om[hi], abs(s0 - s1) - 1)
    return L, s, om


def truncated_modulus(q):
    """Gemini's locking-truncated modulus (RESEARCH_NOTES 2c): nu~_p = min(nu_p, alpha_p + delta_p),
    delta_p = v_p(2^o - 1) - alpha_p with o = ord_{g0}(2) (delta_p = 0 if nu_p <= alpha_p)."""
    d, uq, g0, kap, F = params(q)
    o = order(2, g0)
    out = 1
    for p in factor(uq):
        al, nu = F[p], _vexp(p, d) - F[p]
        de = max(0, _vexp(p, o) - al) if nu > al else 0
        out *= p ** min(nu, al + de)
    return out


def recurrence_L(q):
    """Gemini's general locking recurrence (RESEARCH_NOTES 2c), any g0: returns (L*, profile list)."""
    d, uq, g0, kap, F = params(q)
    if kap < 1:
        return None
    P = list(factor(g0))
    al = {p: F[p] for p in P}
    nu = {p: _vexp(p, d) - F[p] for p in P}
    ga = {p: min(al[p], nu[p]) for p in P}
    M = dict(nu)
    prof = [tuple(M[p] for p in P)]
    for l in range(1, 10 * kap + 10):
        m = {p: min(M[p], ga[p]) for p in P}
        mod = 1
        for p in P:
            mod *= p ** m[p]
        o = order(2, mod)
        lam = {p: (_vexp(p, o) if m[p] >= 1 else 0) for p in P}
        M = {p: max(0, min(lam[p] - al[p], M[p] - al[p])) for p in P}
        prof.append(tuple(M[p] for p in P))
        if all(v == 0 for v in M.values()):
            return l, P, prof
    raise RuntimeError("no termination")


def brute_depth_sets(q):
    """Independent check: residue graph on c_0 mod u_q by explicit CRT lifts (slow; small u_q only)."""
    d, uq, g0, kap, _ = params(q)
    N = q * uq
    succ = {}
    for r in range(uq):
        out = set()
        for a in range(1, d + 1):
            x = pow(2, -a, q)
            if (x - r) % g0:
                continue
            for z in range(x, N, q):
                if (z - r) % uq == 0:
                    out.add(((pow(2, a, N * q) * z - 1) // q) % uq)
        succ[r] = out
    R = [set(range(uq))]
    for _ in range(kap):
        R.append({r for r in R[-1] if succ[r] & R[-1]})
    return R


def report(q):
    R, (d, uq, g0, kap, evals) = depth_sets(q)
    kt = None
    if kap >= 1:
        kt = 1 + max([0] + [k for k in range(1, kap) if R[k] - R[k + 1]])
    dens = Fraction(d * len(R[kap]), q * uq)
    return dict(q=q, d=d, u_q=uq, g0=g0, kappa=kap, sizes=[len(x) for x in R],
                evals_per_step=evals, kappa_trap=kt, delta_dense=dens), R


if __name__ == "__main__":
    args = sys.argv[1:]
    if args and args[0] == "--np":
        for s_ in args[1:]:
            print(depth_sets_np(int(s_)))
    elif args and args[0] == "--scan":
        bound = int(args[1])
        n = 0
        for q in range(3, bound + 1, 2):
            if params(q)[3] < 2:
                continue
            n += 1
            info, _ = report(q)
            if info["kappa_trap"] >= 2:
                print(info)
        print(f"{n} odd q <= {bound} with kappa >= 2 examined")
    else:
        check = "--check" in args
        for s in args:
            if s.startswith("--"):
                continue
            info, R = report(int(s))
            if check:
                info["brute_agrees"] = (R == brute_depth_sets(int(s)))
            print(info)
