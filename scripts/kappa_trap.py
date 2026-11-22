"""Compute kappa_trap(q) and delta_dense(q) (SUPPLEMENTS_B, section 5; RESEARCH_NOTES, section 1).

Usage:
  python3 kappa_trap.py 11571 10887        # report for given q
  python3 kappa_trap.py --check 11571      # also compare with the independent residue-graph brute force
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
    if n == 1:
        return 1
    k, x = 1, a % n
    while x != 1:
        x = x * a % n
        k += 1
    return k


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
    if args and args[0] == "--scan":
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
