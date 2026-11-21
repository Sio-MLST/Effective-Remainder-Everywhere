import Collatz.GeneralLemma2b

/-! Lemma 2(2) of generalAB.md, second part: as j runs over {0..q-1}, c_j(y) mod N_q visits
    every residue class (mod N_q) that is ≡ c_0(y) (mod u_q), exactly once. -/

namespace Collatz

theorem coprime_of_mod_pow2 {q y i : Nat} (hq : q % 2 = 1) (hi : y % q = 2 ^ i % q) :
    Nat.Coprime y q := by
  have h2 : Nat.Coprime q (2 ^ i) := Nat.Coprime.pow_right i (coprime_two_of_odd hq)
  show Nat.gcd y q = 1
  rw [Nat.gcd_comm y q, Nat.gcd_rec q y, hi, ← Nat.gcd_rec q (2 ^ i)]
  exact h2

theorem mod_eq_of_sub_mod_zero {x y N : Nat} (h : y ≤ x) (hz : (x - y) % N = 0) :
    x % N = y % N := by
  have e : x = y + (x - y) := by omega
  conv => lhs; rw [e]
  rw [Nat.add_mod, hz, Nat.add_zero, Nat.mod_mod]

theorem mod_eq_of_add_mod_eq {c x y N : Nat} (h : (c + x) % N = (c + y) % N) :
    x % N = y % N := by
  match Nat.le_total x y with
  | Or.inl hxy =>
    have h1 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    have e : c + y - (c + x) = y - x := by omega
    rw [e] at h1
    exact (mod_eq_of_sub_mod_zero hxy h1).symm
  | Or.inr hyx =>
    have h1 := Nat.sub_mod_eq_zero_of_mod_eq h
    have e : c + x - (c + y) = x - y := by omega
    rw [e] at h1
    exact mod_eq_of_sub_mod_zero hyx h1

theorem uqq_pos {q : Nat} (hq : 1 < q) (hodd : q % 2 = 1) : 0 < uqq q := by
  have hu := (uu_spec hq hodd).2
  exact Nat.gcd_pos_of_pos_left _ (by omega)

theorem Nqq_eq (q : Nat) : Nqq q = q * uqq q := rfl

/-- c_j(y) = c_0(y) + u_q · (2^{a₀} y (u/u_q) S_j). -/
theorem cj_uq_form {q y : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hH : ∃ i, y % q = 2 ^ i % q)
    (hy1 : 1 ≤ y) (j : Nat) :
    cj q y j = c0 q y + uqq q * (2 ^ a0 q y * y * (uu q / uqq q) * Ssum (dq q) j) := by
  have hf := cj_formula hq hodd hH hy1 j
  have hd : uqq q ∣ uu q := Nat.gcd_dvd_left _ _
  have hmul : uqq q * (uu q / uqq q) = uu q := Nat.mul_div_cancel' hd
  rw [hf]
  congr 1
  conv => lhs; rw [← hmul]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- B = 2^{a₀} y (u/u_q) is coprime to q. -/
theorem visitB_coprime {q y : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hH : ∃ i, y % q = 2 ^ i % q) :
    Nat.Coprime (2 ^ a0 q y * y * (uu q / uqq q)) q := by
  obtain ⟨i, hi⟩ := hH
  have hu1 := (uu_spec hq hodd).2
  have h2 : Nat.Coprime (2 ^ a0 q y) q :=
    Nat.Coprime.pow_left _ (Nat.Coprime.symm (coprime_two_of_odd hodd))
  exact Nat.Coprime.mul_left (Nat.Coprime.mul_left h2 (coprime_of_mod_pow2 hodd hi))
    (uq_cofactor_coprime hq hu1)

/-- Existence: every class ≡ c_0(y) (mod u_q) is hit by some c_j(y), j < q. -/
theorem visit_exists {q y : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hH : ∃ i, y % q = 2 ^ i % q)
    (hy1 : 1 ≤ y) (t : Nat) (ht : t % uqq q = c0 q y % uqq q) :
    ∃ j, j < q ∧ cj q y j % Nqq q = t % Nqq q := by
  have hU := uqq_pos hq hodd
  have hBc := visitB_coprime hq hodd hH
  have hper := (dq_isOrder2 hq hodd).2.1
  have hform := fun j => cj_uq_form hq hodd hH hy1 j
  clear hH
  generalize hB : 2 ^ a0 q y * y * (uu q / uqq q) = B at hBc hform
  generalize hU' : uqq q = U at *
  have hN : Nqq q = q * U := by rw [Nqq_eq, hU']
  rw [hN]
  have hNpos : 0 < q * U := Nat.mul_pos (by omega) hU
  obtain ⟨k, w, hkw⟩ := nat_bez B q hq hBc
  -- shift the target above c_0
  have hge : c0 q y ≤ t + q * U * c0 q y := by
    have := Nat.le_mul_of_pos_left (c0 q y) hNpos
    omega
  have hmod : (t + q * U * c0 q y) % U = c0 q y % U := by
    have e : q * U * c0 q y = U * (q * c0 q y) := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    rw [e, Nat.add_mul_mod_self_left]; exact ht
  have hz := Nat.sub_mod_eq_zero_of_mod_eq hmod
  obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hz
  have ht' : t + q * U * c0 q y = c0 q y + U * m := by omega
  refine ⟨(k * m) % q, Nat.mod_lt _ (by omega), ?_⟩
  -- B * S_j ≡ m (mod q)
  have hS := Ssum_mod hper ((k * m) % q)
  have hBS : (B * Ssum (dq q) ((k * m) % q)) % q = m % q := by
    rw [Nat.mul_mod, hS, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, hkw]
    have e : (q * w + 1) * m = q * (w * m) + m := by
      simp only [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
    rw [e, Nat.mul_add_mod]
  have hX : U * (B * Ssum (dq q) ((k * m) % q)) % (q * U) = U * m % (q * U) := by
    rw [Nat.mul_comm q U, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hBS]
  rw [hform, Nat.add_mod, hX, ← Nat.add_mod, ← ht']
  rw [Nat.add_mul_mod_self_left]


end Collatz
