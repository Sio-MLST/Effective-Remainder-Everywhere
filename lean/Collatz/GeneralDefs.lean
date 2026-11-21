import Collatz.GeneralParams

/-! Section 1 of generalAB.md: hypothesis (H), V_q, R_core, the residue graph 𝒢_q,
    Proposition 1 and the statement of Theorem B, all as `Prop`s (no proofs here).
    Residues mod N_q are represented by natural-number representatives.
    The profinite/Haar-measure consequences are not expressible in core Lean; their
    concrete content is stated instead (see `TheoremB`, part 2). -/

namespace Collatz

/-- d = ord_q(2): least k ≥ 1 with 2^k ≡ 1 (mod q) (found by `srch`, fuel q). -/
def dq (q : Nat) : Nat := srch (fun k => 2 ^ k % q = 1 % q) q 1

/-- u = (2^d - 1)/q. -/
def uu (q : Nat) : Nat := (2 ^ dq q - 1) / q

/-- N_q and κ for the canonical (d, u) of q. -/
def Nqq (q : Nat) : Nat := Nq q (uu q)
def uqq (q : Nat) : Nat := uq q (uu q)
def κq (q : Nat) : Nat := kappaQ q (uu q)

/-- (H) with exponent a: ∃ i₀ < d, 2^{i₀} x (2^a - q) ≡ 1 (mod N_q). -/
def HypHa (q a x : Nat) : Prop :=
  ∃ i0, i0 < dq q ∧ ((Nqq q : Nat) : Int) ∣ (2 : Int) ^ i0 * (x : Int) * ((2 : Int) ^ a - (q : Int)) - 1

/-- Hypothesis (H). -/
def HypH (q x : Nat) : Prop := ∃ a, 1 ≤ a ∧ a ≤ dq q ∧ HypHa q a x

/-- V_q: units mod N_q whose reduction mod q lies in ⟨2⟩. -/
def Vq (q y : Nat) : Prop := Nat.Coprime y (Nqq q) ∧ ∃ i, y % q = 2 ^ i % q

/-- R_core. -/
def Rcore (q z : Nat) : Prop := Nat.Coprime z (Nqq q) ∧ HypH q z

/-- a₀(y): the unique a ∈ {1..d} with 2^a y ≡ 1 (mod q). -/
def a0 (q y : Nat) : Nat := srch (fun a => 2 ^ a * y % q = 1 % q) (dq q) 1

/-- c₀(y) = (2^{a₀(y)} y - 1)/q. -/
def c0 (q y : Nat) : Nat := (2 ^ a0 q y * y - 1) / q

/-- Edge z → z' in 𝒢_q (on representatives): both in V_q and z' ≡ c₀(z) (mod u_q). -/
def Edge (q z z' : Nat) : Prop := Vq q z ∧ Vq q z' ∧ z' % uqq q = c0 q z % uqq q

/-- Directed path of length n in 𝒢_q from (the class of) z to (the class of) z'. -/
def GPath (q : Nat) : Nat → Nat → Nat → Prop
  | 0, z, z' => Vq q z ∧ z % Nqq q = z' % Nqq q
  | n + 1, z, z' => ∃ z'', Edge q z z'' ∧ GPath q n z'' z'

/-- Backward orbit membership x ∈ R_q(t) is `Reaches q x t`.
    Proposition 1 (Exact Partition Criterion), including the size bound
    x ≤ (2^{dq}/q)^{κ+1} t written as x q^{κ+1} ≤ 2^{dq(κ+1)} t, and the (a=1, i₀=0) refinement. -/
def Prop1 (q t : Nat) : Prop :=
  ((∃ x, Reaches q x t ∧ HypH q x) ↔
    (Vq q t ∧ ∃ n z, GPath q n t z ∧ Rcore q z)) ∧
  ((Vq q t ∧ ∃ n z, GPath q n t z ∧ Rcore q z) ↔
    (∃ z, GPath q (κq q) t z)) ∧
  ((∃ z, GPath q (κq q) t z) →
    ∃ x, Reaches q x t ∧ HypH q x ∧
      x * q ^ (κq q + 1) ≤ 2 ^ (dq q * q * (κq q + 1)) * t ∧
      (κq q = 0 → x = t ∧ HypHa q 1 t) ∧
      (1 ≤ κq q → ((Nqq q : Nat) : Int) ∣ (x : Int) * (2 - (q : Int)) - 1))

/-- A backward chain of m odd steps in R_q(t) (generalAB.md, Section 1). -/
def Chain (q t m : Nat) (w k : Nat → Nat) : Prop :=
  (∀ l, 1 ≤ l → l ≤ m → w l % 2 = 1 ∧ 1 ≤ w l) ∧
  q * w 1 + 1 = 2 ^ k 1 * t ∧
  (∀ l, 1 ≤ l → l < m → q * w (l + 1) + 1 = 2 ^ k (l + 1) * w l ∧ 1 ≤ k (l + 1))

/-- x is periodic under Col_q. -/
def Periodic (q x : Nat) : Prop := ∃ k, 0 < k ∧ iter (collatz q) k x = x

/-- No element of R_q(t) satisfies (H). -/
def NoH (q t : Nat) : Prop := ∀ x, Reaches q x t → ¬ HypH q x

/-- Theorem B (generalAB.md, Section 3).
    Part 2's measure-zero/closure consequence is represented by its concrete content,
    the bound |R_q(t) mod 2^n| ≤ (n+1)^{κ+1}. Part 3's O_q((log X)^{κ+1}) is
    ∃ C (depending on q only) with the stated count bound, uniform in t. -/
def TheoremB (q : Nat) : Prop :=
  (∀ t, 1 ≤ t → NoH q t →
    -- (1) bounded odd depth
    (∀ m w k, 1 ≤ m → Chain q t m w k → m ≤ κq q) ∧
    -- (2) sparsity modulo 2^n
    (∀ n, 1 ≤ n → ∀ L : List Nat, L.Nodup →
      (∀ r ∈ L, r < 2 ^ n ∧ ∃ x, Reaches q x t ∧ x % 2 ^ n = r) →
      L.length ≤ (n + 1) ^ (κq q + 1)) ∧
    -- (3a) non-periodicity
    (∀ x, Reaches q x t → ¬ Periodic q x)) ∧
  -- (3b) polylogarithmic growth, uniform in t
  (∃ C, ∀ t, 1 ≤ t → NoH q t → ∀ X, 2 ≤ X → ∀ L : List Nat, L.Nodup →
      (∀ x ∈ L, 1 ≤ x ∧ x ≤ X ∧ Reaches q x t) →
      L.length ≤ C * (Nat.log2 X + 1) ^ (κq q + 1))

end Collatz
