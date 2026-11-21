import Collatz.GeneralTheoremA

/-! First proofs for the general development (generalAB.md, Sections 1-2):
    `dq q` is the multiplicative order of 2 mod q, and `a0 q y` is the unique
    a ∈ {1..d} with 2^a y ≡ 1 (mod q) for y with y mod q ∈ ⟨2⟩. -/

namespace Collatz

theorem srch_ge (p : Nat → Prop) [DecidablePred p] : ∀ f n, n ≤ srch p f n
  | 0, n => by simp [srch]
  | f + 1, n => by
    unfold srch
    by_cases h : p n
    · simp only [h, ↓reduceIte]; exact Nat.le_refl n
    · simp only [h, ↓reduceIte]; have := srch_ge p f (n + 1); omega

/-- `dq q` is ord_q(2) for odd q > 1. -/
theorem dq_isOrder2 {q : Nat} (hq : 1 < q) (hodd : q % 2 = 1) : IsOrder2 q (dq q) := by
  obtain ⟨D, hD0, hDq, hD⟩ := exists_pow2_period q (by omega) (coprime_two_of_odd hodd)
  have h := srch_spec (fun k => 2 ^ k % q = 1 % q) q 1 ⟨D, hD0, by omega, hD⟩
  have hge := srch_ge (fun k => 2 ^ k % q = 1 % q) q 1
  exact ⟨Nat.lt_of_lt_of_le Nat.zero_lt_one hge, h.1, fun i hi hid hi' => h.2 i hi hid hi'⟩

/-- Multiplying by y ≡ 2^i (mod q) shifts the exponent. -/
theorem pow_mul_mod_shift {q y i : Nat} (hi : y % q = 2 ^ i % q) (a : Nat) :
    2 ^ a * y % q = 2 ^ (a + i) % q := by
  rw [Nat.mul_mod, hi, ← Nat.mul_mod, ← Nat.pow_add]

theorem a0_spec {q y : Nat} (hq : 1 < q) (hodd : q % 2 = 1)
    (hH : ∃ i, y % q = 2 ^ i % q) :
    1 ≤ a0 q y ∧ a0 q y ≤ dq q ∧ 2 ^ a0 q y * y % q = 1 % q ∧
    ∀ a, 1 ≤ a → a ≤ dq q → 2 ^ a * y % q = 1 % q → a = a0 q y := by
  have hd := dq_isOrder2 hq hodd
  obtain ⟨i, hi⟩ := hH
  have hd0 := hd.1
  -- a witness a₁ = d - i % d ∈ [1, d]
  have hmod := Nat.mod_lt i hd0
  have hw : 2 ^ (dq q - i % dq q) * y % q = 1 % q := by
    rw [pow_mul_mod_shift hi]
    have := pow_two_mod_period q (dq q) hd.2.1 (dq q - i % dq q + i) 0
      (by
        have h1 := Nat.mod_add_div i (dq q)
        have h2 : dq q - i % dq q + i = dq q * (1 + i / dq q) := by
          rw [Nat.mul_add, Nat.mul_one]
          omega
        rw [h2, Nat.mul_mod_right, Nat.zero_mod])
    rw [this]
  have hsp := srch_spec (fun a => 2 ^ a * y % q = 1 % q) (dq q) 1
    ⟨dq q - i % dq q, by omega, by omega, hw⟩
  have hge := srch_ge (fun a => 2 ^ a * y % q = 1 % q) (dq q) 1
  have hpa : 2 ^ a0 q y * y % q = 1 % q := hsp.1
  have hge1 : 1 ≤ a0 q y := hge
  have hle : a0 q y ≤ dq q - i % dq q := by
    match Nat.lt_or_ge (dq q - i % dq q) (a0 q y) with
    | Or.inl hlt => exact absurd hw (hsp.2 _ (by omega) hlt)
    | Or.inr hge' => exact hge'
  refine ⟨hge1, by omega, hpa, ?_⟩
  intro a ha1 ha2 hpa'
  have e1 : 2 ^ (a + i) % q = 1 % q := by rw [← pow_mul_mod_shift hi]; exact hpa'
  have e2 : 2 ^ (a0 q y + i) % q = 1 % q := by rw [← pow_mul_mod_shift hi]; exact hpa
  have d1 := order_dvd hd e1
  have d2 := order_dvd hd e2
  obtain ⟨c1, hc1⟩ := d1
  obtain ⟨c2, hc2⟩ := d2
  have hA : a0 q y ≤ dq q := by omega
  -- both a and a0 lie in [1, d] and a + i ≡ a0 + i ≡ 0 (mod d)
  rcases Nat.lt_trichotomy a (a0 q y) with hlt | heq | hgt
  · exfalso
    have hlt' : dq q * c1 < dq q * c2 := by omega
    match Nat.lt_or_ge c1 c2 with
    | Or.inl hc =>
      have : dq q * (c1 + 1) ≤ dq q * c2 := Nat.mul_le_mul_left _ hc
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    | Or.inr hc =>
      have : dq q * c2 ≤ dq q * c1 := Nat.mul_le_mul_left _ hc
      omega
  · exact heq
  · exfalso
    have hlt' : dq q * c2 < dq q * c1 := by omega
    match Nat.lt_or_ge c2 c1 with
    | Or.inl hc =>
      have : dq q * (c2 + 1) ≤ dq q * c1 := Nat.mul_le_mul_left _ hc
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    | Or.inr hc =>
      have : dq q * c1 ≤ dq q * c2 := Nat.mul_le_mul_left _ hc
      omega

end Collatz
