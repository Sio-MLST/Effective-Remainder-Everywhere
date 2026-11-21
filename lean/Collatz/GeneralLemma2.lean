import Collatz.GeneralBasics

/-! Lemma 2(1) of generalAB.md (odd backward steps), for y ≥ 1 with y mod q ∈ ⟨2⟩. -/

namespace Collatz

/-- S_j = Σ_{l<j} 2^{dl}. -/
def Ssum (d : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => Ssum d j + 2 ^ (d * j)

/-- (2^d - 1) S_j = 2^{dj} - 1, in the form q u S_j + 1 = 2^{dj}. -/
theorem qu_Ssum (q d u : Nat) (hd : 2 ^ d = 1 + q * u) :
    ∀ j, q * u * Ssum d j + 1 = 2 ^ (d * j)
  | 0 => by simp [Ssum]
  | j + 1 => by
    have ih := qu_Ssum q d u hd j
    show q * u * (Ssum d j + 2 ^ (d * j)) + 1 = 2 ^ (d * (j + 1))
    rw [Nat.mul_add, Nat.mul_succ, Nat.pow_add, hd, Nat.mul_add, Nat.mul_one,
      Nat.mul_comm (2 ^ (d * j)) (q * u)]
    omega

/-- c_j(y) = (2^{a₀ + dj} y - 1)/q. -/
def cj (q y j : Nat) : Nat := (2 ^ (a0 q y + dq q * j) * y - 1) / q

theorem cj_spec {q y : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hH : ∃ i, y % q = 2 ^ i % q)
    (hy1 : 1 ≤ y) (j : Nat) :
    q * cj q y j + 1 = 2 ^ (a0 q y + dq q * j) * y ∧ 1 ≤ cj q y j ∧ cj q y j % 2 = 1 := by
  have hd := dq_isOrder2 hq hodd
  obtain ⟨ha1, haD, hapa, _⟩ := a0_spec hq hodd hH
  obtain ⟨i, hi⟩ := hH
  have hpos : 1 ≤ 2 ^ (a0 q y + dq q * j) * y :=
    Nat.mul_pos (Nat.pow_pos (by omega)) hy1
  -- 2^ℓ y ≡ 1 (mod q)
  have h1 : 2 ^ (a0 q y + dq q * j) * y % q = 1 % q := by
    rw [pow_mul_mod_shift hi]
    have e : a0 q y + dq q * j + i = (a0 q y + i) + dq q * j := by omega
    rw [e, pow_mod_period hd.2.1 (a0 q y + i) j, ← pow_mul_mod_shift hi]
    exact hapa
  have hz : (2 ^ (a0 q y + dq q * j) * y - 1) % q = 0 := Nat.sub_mod_eq_zero_of_mod_eq h1
  have hdm := Nat.div_add_mod (2 ^ (a0 q y + dq q * j) * y - 1) q
  unfold cj
  have hc : q * ((2 ^ (a0 q y + dq q * j) * y - 1) / q) + 1 = 2 ^ (a0 q y + dq q * j) * y := by
    rw [hz] at hdm; omega
  refine ⟨hc, ?_, ?_⟩
  · -- positivity: 2^ℓ y ≥ 2
    have h2 : 2 ≤ 2 ^ (a0 q y + dq q * j) * y := by
      have : 2 ^ 1 ≤ 2 ^ (a0 q y + dq q * j) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : 2 ^ (a0 q y + dq q * j) * 1 ≤ 2 ^ (a0 q y + dq q * j) * y :=
        Nat.mul_le_mul_left _ hy1
      omega
    match Nat.eq_zero_or_pos ((2 ^ (a0 q y + dq q * j) * y - 1) / q) with
    | Or.inl h0 => rw [h0] at hc; omega
    | Or.inr hp => exact hp
  · -- oddness: q c + 1 even, q odd
    have hev : 2 ^ (a0 q y + dq q * j) * y % 2 = 0 := by
      have e : a0 q y + dq q * j = (a0 q y + dq q * j - 1) + 1 := by omega
      rw [e, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
      exact Nat.mul_mod_right _ _
    have hm := Nat.mul_mod q ((2 ^ (a0 q y + dq q * j) * y - 1) / q) 2
    rw [hodd] at hm
    omega

/-- Every odd backward step has the form c_j(y). -/
theorem step_form {q y : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hH : ∃ i, y % q = 2 ^ i % q)
    (hy1 : 1 ≤ y) {w l : Nat} (hl : 1 ≤ l) (h : q * w + 1 = 2 ^ l * y) :
    ∃ j, l = a0 q y + dq q * j ∧ w = cj q y j := by
  have hd := dq_isOrder2 hq hodd
  obtain ⟨_, _, _, hun⟩ := a0_spec hq hodd hH
  obtain ⟨i, hi⟩ := hH
  -- reduce l into [1, d]
  have red : ∀ n, 1 ≤ n → ∃ a c, 1 ≤ a ∧ a ≤ dq q ∧ n = a + dq q * c := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro hn
      match Nat.lt_or_ge (dq q) n with
      | Or.inl hlt =>
        obtain ⟨a, c, h1, h2, h3⟩ := ih (n - dq q) (by have := hd.1; omega) (by omega)
        exact ⟨a, c + 1, h1, h2, by rw [Nat.mul_succ]; omega⟩
      | Or.inr hge => exact ⟨n, 0, hn, hge, by omega⟩
  obtain ⟨a, c, ha1, haD, hlac⟩ := red l hl
  have hm1 : 2 ^ l * y % q = 1 % q := by
    rw [← h, Nat.mul_add_mod]
  have hm2 : 2 ^ a * y % q = 1 % q := by
    rw [pow_mul_mod_shift hi]
    have e : l + i = (a + i) + dq q * c := by omega
    have h3 := pow_mul_mod_shift hi l
    rw [e, pow_mod_period hd.2.1 (a + i) c] at h3
    rw [← h3]; exact hm1
  have haeq := hun a ha1 haD hm2
  refine ⟨c, by rw [← haeq]; exact hlac, ?_⟩
  have hspec := (cj_spec hq hodd ⟨i, hi⟩ hy1 c).1
  have hl' : l = a0 q y + dq q * c := by rw [← haeq]; exact hlac
  rw [← hl'] at hspec
  have : q * w = q * cj q y c := by omega
  exact Nat.eq_of_mul_eq_mul_left (by omega) this

/-- c_0 agrees with c_j at j = 0. -/
theorem c0_eq_cj0 (q y : Nat) : c0 q y = cj q y 0 := by
  unfold c0 cj; rw [Nat.mul_zero, Nat.add_zero]

/-- c_j(y) = c_0(y) + 2^{a₀} y u S_j. -/
theorem cj_formula {q y : Nat} (hq : 1 < q) (hodd : q % 2 = 1)
    (hH : ∃ i, y % q = 2 ^ i % q) (hy1 : 1 ≤ y) (j : Nat) :
    cj q y j = c0 q y + 2 ^ a0 q y * y * uu q * Ssum (dq q) j := by
  have hd := dq_isOrder2 hq hodd
  have hu := pow_eq_of_order hq hd
  have hS := qu_Ssum q (dq q) (uu q) hu j
  have hj := (cj_spec hq hodd hH hy1 j).1
  have h0 := (cj_spec hq hodd hH hy1 0).1
  clear hH
  simp only [Nat.mul_zero, Nat.add_zero] at h0
  rw [← c0_eq_cj0] at h0
  rw [Nat.pow_add] at hj
  apply Nat.eq_of_mul_eq_mul_left (show 0 < q by omega)
  rw [Nat.mul_add]
  have e : q * (2 ^ a0 q y * y * uu q * Ssum (dq q) j) =
      2 ^ a0 q y * y * (q * uu q * Ssum (dq q) j) := by
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hj' : q * cj q y j + 1 = (2 ^ a0 q y * y) * 2 ^ (dq q * j) := by
    rw [hj]; simp only [Nat.mul_assoc, Nat.mul_comm]
  have hAT : (2 ^ a0 q y * y) * 2 ^ (dq q * j) =
      (2 ^ a0 q y * y) * (q * uu q * Ssum (dq q) j) + 2 ^ a0 q y * y := by
    rw [← hS, Nat.mul_add, Nat.mul_one]
  rw [e]
  clear hd hu
  omega

end Collatz
