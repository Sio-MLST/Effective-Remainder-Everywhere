import Collatz.TheoremB

/-! Section 1 structural parameters for general odd q > 1 (generalAB.md, Section 1).
    New definitions only; nothing above is modified.
    u_q = gcd(u, q^(log₂ u + 1)) is the largest divisor of u whose prime factors divide q
    (its p-part is p^{ν_p(u)} since ν_p(u) ≤ log₂ u < (log₂ u + 1)·α_p).
    κ = least k with u_q ∣ q^k, which equals max_p ⌈ν_p/α_p⌉. -/

namespace Collatz

/-- u_q = ∏_{p | q} p^{ν_p(u)}, written without factorizations. -/
def uq (q u : Nat) : Nat := Nat.gcd u (q ^ (Nat.log2 u + 1))

/-- N_q = q · u_q. -/
def Nq (q u : Nat) : Nat := q * uq q u

theorem uq_dvd_pow (q u : Nat) : uq q u ∣ q ^ (Nat.log2 u + 1) :=
  Nat.gcd_dvd_right u (q ^ (Nat.log2 u + 1))

/-- κ = least k with u_q ∣ q^k, found by `srch` over 0..log₂ u + 1 (k = log₂ u + 1 always works). -/
def kappaQ (q u : Nat) : Nat := srch (fun k => uq q u ∣ q ^ k) (Nat.log2 u + 1) 0

theorem kappaQ_spec (q u : Nat) : uq q u ∣ q ^ kappaQ q u ∧
    ∀ k, k < kappaQ q u → ¬ uq q u ∣ q ^ k := by
  have h := srch_spec (fun k => uq q u ∣ q ^ k) (Nat.log2 u + 1) 0
    ⟨Nat.log2 u + 1, Nat.zero_le _, by omega, uq_dvd_pow q u⟩
  exact ⟨h.1, fun k hk => h.2 k (Nat.zero_le k) hk⟩

/-- κ = 0 exactly when u_q = 1 (the non-Wieferich case g_0 = 1 of the note). -/
theorem kappaQ_zero_iff (q u : Nat) : kappaQ q u = 0 ↔ uq q u = 1 := by
  constructor
  · intro h
    have hs := (kappaQ_spec q u).1
    rw [h, Nat.pow_zero] at hs
    exact Nat.dvd_one.mp hs
  · intro h
    have hs := (kappaQ_spec q u).2
    match Nat.eq_zero_or_pos (kappaQ q u) with
    | Or.inl h0 => exact h0
    | Or.inr hp => exact absurd (by rw [h, Nat.pow_zero]; exact Nat.one_dvd _) (hs 0 hp)

end Collatz
