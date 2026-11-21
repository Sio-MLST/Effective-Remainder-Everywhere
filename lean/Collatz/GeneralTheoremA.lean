import Collatz.GeneralDefs

/-! Section 3 of generalAB.md: the parameters attached to a modulus m, the exponent
    bounds E*(a), E**, and the statement of Theorem A as a `Prop` (unproved).
    Everything is defined without Mathlib: valuations and prime lists are computed by
    bounded searches. Real-valued bounds are stated by cross-multiplication. -/

namespace Collatz

/-- p-adic valuation of n (n > 0): least k with p^(k+1) ∤ n. -/
def vp (p n : Nat) : Nat := srch (fun k => ¬ p ^ (k + 1) ∣ n) n 0

/-- Boolean primality. -/
def isPrimeB (p : Nat) : Bool := 2 ≤ p && (List.range p).all (fun a => a < 2 || p % a != 0)

/-- The primes dividing q. -/
def qprimes (q : Nat) : List Nat :=
  (List.range (q + 1)).filter (fun p => isPrimeB p && q % p == 0)

def αp (q p : Nat) : Nat := vp p q
def νp (q p : Nat) : Nat := vp p (uu q)

/-- E_p^* = ∏_{p' | q, p' ≠ p} p'^{max(α_p', (κ+1)α_p' - ν_p')}. -/
def Epstar (q p : Nat) : Nat :=
  ((qprimes q).filter (fun p' => p' != p)).foldl
    (fun acc p' => acc * p' ^ (max (αp q p') ((κq q + 1) * αp q p' - νp q p'))) 1

/-- J_0^*. -/
def J0star (q : Nat) : Nat :=
  if κq q = 0 then q - 1
  else (qprimes q).foldl (fun acc p => acc + (p ^ αp q p - 1) * Epstar q p) 0

/-- Parameters attached to m (Section 3). -/
def alphaM (m : Nat) : Nat := vp 2 m
def oddM (m : Nat) : Nat := m / 2 ^ alphaM m
def mqM (q m : Nat) : Nat := Nat.gcd (oddM m) (q ^ oddM m)
def mpM (q m : Nat) : Nat := oddM m / mqM q m
def MM (q m : Nat) : Nat := mqM q m * mpM q m
def eM (q m : Nat) : Nat := srch (fun k => 2 ^ k % mpM q m = 1 % mpM q m) (mpM q m) 1
def eQM (q m : Nat) : Nat := Nat.gcd (eM q m) (q ^ eM q m)
def KM (q m : Nat) : Nat := srch (fun k => eQM q m ∣ q ^ k) (eM q m) 0
def gammaM (q m : Nat) : Nat := leastCover q (mpM q m) (eM q m)
def PM (q m : Nat) : Nat := Nat.lcm (dq q * q ^ KM q m) (eM q m)
def sM (q m : Nat) : Nat :=
  if mpM q m = 1 then KM q m + κq q + 1 else KM q m + κq q + gammaM q m + 2

/-- W̃(n) = lcm(q^n m_q, q^K u_q) / (q^K u_q). -/
def Wt (q m n : Nat) : Nat :=
  Nat.lcm (q ^ n * mqM q m) (q ^ KM q m * uqq q) / (q ^ KM q m * uqq q)
/-- Q̃(n) = W̃(n) P. -/
def Qt (q m n : Nat) : Nat := Wt q m n * PM q m

def B0 (q m a : Nat) : Nat :=
  if mpM q m = 1 then κq q * a
  else (KM q m + κq q + 1) * a + gammaM q m * eM q m

/-- E^*(a) = α + Q̃_0 + max(⌈log₂(M+1)⌉, dq^K - 1 + (s-1)J_0^* P + B_0(a) - ⌊s log₂ q⌋). -/
def Estar (q m a : Nat) : Nat :=
  alphaM m + Qt q m (alphaM m) +
    max (ceilLog2 (MM q m + 1))
      (dq q * q ^ KM q m - 1 + (sM q m - 1) * J0star q * PM q m + B0 q m a
        - Nat.log2 (q ^ sM q m))

/-- E^** . -/
def Estar2 (q m : Nat) : Nat :=
  alphaM m + Qt q m (alphaM m) +
    max (ceilLog2 (MM q m + 1))
      (dq q * q ^ KM q m - 1 + (sM q m - 1) * J0star q * PM q m + B0 q m 1
        + (κq q + 1) * dq q * q - Nat.log2 (q ^ (sM q m + κq q + 1)))

/-- Theorem A (generalAB.md, Section 3), for fixed odd q > 1 and t ≥ 1 with some
    x ∈ R_q(t) satisfying (H).  For every m ≥ 1 there is a function `nf` of r mod 2^α
    with values in {0..α} such that for all r, B there is w with w → t, w ≡ r (mod m),
    w > B, and the displayed bounds (max(X, Y/Z) is split as the disjunction
    w < X ∨ w Z < Y, and the final ≤ as two inequalities).
    The closure/measure-one consequence is represented by the density statement itself
    (every residue class modulo every m contains elements of R_q(t) beyond every bound). -/
def TheoremA (q t : Nat) : Prop :=
  (∃ x, Reaches q x t ∧ HypH q x) →
  ∀ m, 1 ≤ m →
    ∃ nf : Nat → Nat,
      (∀ r r', r % 2 ^ alphaM m = r' % 2 ^ alphaM m → nf r = nf r') ∧
      (∀ r, nf r ≤ alphaM m) ∧
      ∀ r B, ∃ w, Reaches q w t ∧ w % m = r % m ∧ B < w ∧
        -- (1) t satisfies (H) with exponent a
        (∀ a, 1 ≤ a → a ≤ dq q → HypHa q a t →
          (w < 2 ^ (alphaM m + Qt q m (nf r)) * (B + MM q m + 1) ∨
            w * q ^ (nf r + sM q m) <
              2 ^ (alphaM m + Qt q m (nf r) + dq q * q ^ KM q m - 1
                + (sM q m - 1) * J0star q * PM q m + B0 q m a) * t) ∧
          2 ^ (alphaM m + Qt q m (nf r)) * (B + MM q m + 1) ≤ (B + 1) * t * 2 ^ Estar q m a ∧
          2 ^ (alphaM m + Qt q m (nf r) + dq q * q ^ KM q m - 1
                + (sM q m - 1) * J0star q * PM q m + B0 q m a) * t
            ≤ (B + 1) * t * 2 ^ Estar q m a * q ^ (nf r + sM q m)) ∧
        -- (2) in general (t does not satisfy (H))
        (¬ HypH q t →
          (w < 2 ^ (alphaM m + Qt q m (nf r)) * (B + MM q m + 1) ∨
            w * q ^ (nf r + sM q m + κq q + 1) <
              2 ^ (alphaM m + Qt q m (nf r) + dq q * q ^ KM q m - 1
                + (sM q m - 1) * J0star q * PM q m + B0 q m 1 + (κq q + 1) * dq q * q) * t) ∧
          2 ^ (alphaM m + Qt q m (nf r)) * (B + MM q m + 1) ≤ (B + 1) * t * 2 ^ Estar2 q m ∧
          2 ^ (alphaM m + Qt q m (nf r) + dq q * q ^ KM q m - 1
                + (sM q m - 1) * J0star q * PM q m + B0 q m 1 + (κq q + 1) * dq q * q) * t
            ≤ (B + 1) * t * 2 ^ Estar2 q m * q ^ (nf r + sM q m + κq q + 1))

end Collatz
