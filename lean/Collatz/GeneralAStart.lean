import Collatz.GeneralAVal

/-! Theorem A, Step 1 (generalAB.md Lemmas 5–6): the inverse c_* of 2^a − q mod Λ,
    the starting point y₀ = 2^{λ₀} x ≡ c_* (mod Λ) with λ₀ ≤ d q^K − 1, and the primer
    y_l ≡ c_* (mod q^{K+1−l} u_q) for l ≤ K + 1 (any shifts). Choice-free. -/

namespace Collatz

theorem LamA_eq (q m : Nat) : LamA q m = Nqq q * q ^ KM q m := by
  unfold LamA; rw [Nqq_eq, Nat.pow_succ]; simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem LamA_pos {q m : Nat} (hq : 1 < q) (hodd : q % 2 = 1) : 0 < LamA q m :=
  Nat.mul_pos (Nat.pow_pos (by omega)) (uqq_pos hq hodd)

theorem LamA_gt {q m : Nat} (hq : 1 < q) (hodd : q % 2 = 1) : 1 < LamA q m := by
  rw [LamA_eq]
  have := Nqq_gt hq hodd
  have : 1 ≤ q ^ KM q m := Nat.pow_pos (by omega)
  have : Nqq q ≤ Nqq q * q ^ KM q m := Nat.le_mul_of_pos_right _ this
  omega

theorem q_le_LamA {q m : Nat} (hq : 1 < q) (hodd : q % 2 = 1) : q ≤ LamA q m := by
  unfold LamA
  have h1 : q ≤ q ^ (KM q m + 1) := by
    have := Nat.pow_le_pow_right (show 0 < q by omega) (Nat.succ_pos (KM q m)); rwa [Nat.pow_one] at this
  exact Nat.le_trans h1 (Nat.le_mul_of_pos_right _ (uqq_pos hq hodd))

theorem prime_dvd_q_of_dvd_LamA {q m p : Nat} (hp : IsPrime p) (h : p ∣ LamA q m) : p ∣ q :=
  prime_dvd_q_of_dvd_qU hp h

/-- 2^a + Λ − q is a unit mod Λ: an inverse c_* exists. -/
theorem cstar_exists {q m : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (a : Nat) :
    ∃ c, (2 ^ a + LamA q m - q) * c % LamA q m = 1 % LamA q m := by
  have hL := LamA_gt (m := m) hq hodd
  have hqL := q_le_LamA (m := m) hq hodd
  have hcop : Nat.gcd (2 ^ a + LamA q m - q) (LamA q m) = 1 := by
    apply coprime_of_no_prime
    intro p hp hpb hpL
    have hpq := prime_dvd_q_of_dvd_LamA hp hpL
    have h2 : p ∣ 2 ^ a := by
      have h2a : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      have e : 2 ^ a + LamA q m = (2 ^ a + LamA q m - q) + q := by omega
      have : p ∣ 2 ^ a + LamA q m := by rw [e]; exact Nat.dvd_add hpb hpq
      exact (Nat.dvd_add_right hpL).mp (by rw [Nat.add_comm]; exact this)
    have h22 := isPrime_dvd_pow hp a h2
    have := Nat.le_of_dvd (by omega) h22
    have := hp.1
    have hp2 : p = 2 := by omega
    rw [hp2] at hpq
    obtain ⟨c, hc⟩ := hpq
    omega
  obtain ⟨k, w, hkw⟩ := nat_bez _ _ hL hcop
  exact ⟨k, by rw [hkw, Nat.mul_add_mod]⟩

/-- Lemma 5 (starting point). -/
theorem start_point {q m a x i0 c : Nat} (hq : 1 < q) (hodd : q % 2 = 1)
    (_hx1 : 1 ≤ x) (hH : 2 ^ i0 * x * bco q a % Nqq q = 1 % Nqq q) (hi0 : i0 < dq q)
    (hc : (2 ^ a + LamA q m - q) * c % LamA q m = 1 % LamA q m) :
    ∃ lam0, lam0 + 1 ≤ dq q * q ^ KM q m ∧ 2 ^ lam0 * x % LamA q m = c % LamA q m := by
  have hN := Nqq_gt hq hodd
  have hL := LamA_gt (m := m) hq hodd
  have hd := dq_isOrder2 hq hodd
  generalize hX : 2 ^ i0 * x = X at hH
  -- X is a unit mod Λ
  have hXN : Nat.gcd X (Nqq q) = 1 := by
    apply coprime_of_no_prime
    intro p hp hpX hpN
    have h1 : X * bco q a % p = 1 % p := by
      rw [← Nat.mod_mod_of_dvd _ hpN, hH, Nat.mod_mod_of_dvd _ hpN]
    have h2 : X * bco q a % p = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right_of_dvd hpX _)
    have := Nat.mod_eq_of_lt hp.1
    omega
  have hXL : Nat.gcd X (LamA q m) = 1 := by
    apply coprime_of_no_prime
    intro p hp hpX hpL
    have hpN : p ∣ Nqq q := Nat.dvd_trans (prime_dvd_q_of_dvd_LamA hp hpL) (Nqq_dvd q)
    have := Nat.dvd_gcd hpX hpN
    rw [hXN] at this
    have := Nat.le_of_dvd Nat.one_pos this; have := hp.1; omega
  obtain ⟨k, w, hkw⟩ := nat_bez X _ hL hXL
  -- χ = c·k ≡ 1 (mod N)
  have hNL : Nqq q ∣ LamA q m := by rw [LamA_eq]; exact Nat.dvd_mul_right _ _
  have hbN : (2 ^ a + LamA q m - q) % Nqq q = bco q a % Nqq q := by
    have h2 := q_le_LamA (m := m) hq hodd
    have h2a : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    obtain ⟨t, ht⟩ := hNL
    apply mod_eq_of_add_mod_eq (c := q)
    have e1 : q + (2 ^ a + LamA q m - q) = 2 ^ a + LamA q m := by omega
    have e2 : q + bco q a = 2 ^ a + Nqq q := by rw [Nat.add_comm]; exact bco_add_q q a hq hodd
    rw [e1, e2, ht, Nat.add_mul_mod_self_left, Nat.add_mod_right]
  have hcN : bco q a * c % Nqq q = 1 % Nqq q := by
    rw [Nat.mul_mod, ← hbN, ← Nat.mul_mod, ← Nat.mod_mod_of_dvd _ hNL, hc,
      Nat.mod_mod_of_dvd _ hNL]
  have hχ : c * k % Nqq q = 1 % Nqq q := by
    -- c ≡ c (bco X) = X (bco c) ≡ X, and X k ≡ 1
    have hXk : X * k % Nqq q = 1 % Nqq q := by
      rw [hkw, ← Nat.mod_mod_of_dvd _ hNL, Nat.mul_add_mod, Nat.mod_mod_of_dvd _ hNL]
    have e1 : c * k % Nqq q = (bco q a * X) * (c * k) % Nqq q := by
      rw [Nat.mul_mod (bco q a * X), Nat.mul_comm (bco q a) X, hH, ← Nat.mul_mod, Nat.one_mul]
    have e2 : (bco q a * X) * (c * k) = (bco q a * c) * (X * k) := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    rw [e1, e2, Nat.mul_mod, hcN, hXk, ← Nat.mul_mod, Nat.one_mul]
  -- geometric visit with g = 2^d, L0 = N, W = q^K
  obtain ⟨m0, hm0, hm0e⟩ := geom_visit (g := 2 ^ dq q) (L0 := Nqq q) (W := q ^ KM q m) hq
    (by omega) (Nqq_dvd q) (Nat.pow_pos (by omega))
    (fun r hr h => prime_dvd_q_of_dvd_qU (k := 1) hr (by rw [Nat.pow_one]; exact h))
    (fun r hr h => isPrime_dvd_pow hr _ h) Nat.one_le_two_pow (pow_d_mod_Nqq hq hodd)
    (fun p Δ hp hpq hΔ => by
      have hv := val_2dN hq hodd hp hpq hΔ
      have hvN := val_qkU (k := 1) hq hodd hp hpq
      rw [Nat.pow_one, Nat.one_mul] at hvN
      rw [val_unique (val_vp hp.1 (Nat.lt_trans Nat.zero_lt_one hN)) hvN, ← Nat.pow_mul]
      exact hv)
    (c * k) hχ
  rw [← LamA_eq] at hm0e
  refine ⟨dq q * m0 + i0, ?_, ?_⟩
  · have h1 : dq q * m0 + dq q ≤ dq q * q ^ KM q m := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hm0
    omega
  · rw [Nat.pow_add, Nat.mul_assoc, hX, Nat.mul_mod, Nat.pow_mul, hm0e, ← Nat.mul_mod,
      Nat.mul_assoc, Nat.mul_mod, Nat.mul_comm k X, hkw, Nat.mul_add_mod, ← Nat.mul_mod,
      Nat.mul_one]

/-- Primer (uniform part of Lemma 6): with b_l = a for l ≤ K+1 and any shifts, the path is
    integral up to K+1 and y_l ≡ c_* (mod q^{K+1−l} u_q). -/
theorem primer {q m a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) {c y0 : Int}
    (hc : (LamA q m : Int) ∣ ((2 : Int) ^ a - q) * c - 1) (hy0 : (LamA q m : Int) ∣ y0 - c)
    {b J : Nat → Nat} (hb : ∀ l, 1 ≤ l → l ≤ KM q m + 1 → b l = a) :
    ∀ l, l ≤ KM q m + 1 → Integral (q : Int) (PM q m) y0 b J l ∧
      ((q ^ (KM q m + 1 - l) * uqq q : Nat) : Int) ∣ chain (q : Int) (PM q m) y0 b J l - c
  | 0, _ => ⟨fun i hi => absurd hi (Nat.not_lt_zero i), by
      rw [Nat.sub_zero]; exact hy0⟩
  | l + 1, hl => by
    obtain ⟨hI, hD⟩ := primer hq hodd hm hc hy0 hb l (by omega)
    have hG : (LamA q m : Int) ∣ (2 : Int) ^ (J (l + 1) * PM q m) - 1 := by
      have := Lam_dvd (m := m) hq hodd hm (J (l + 1))
      have h1 : 1 ≤ 2 ^ (J (l + 1) * PM q m) := Nat.one_le_two_pow
      have e : ((2 ^ (J (l + 1) * PM q m) - 1 : Nat) : Int) = (2 : Int) ^ (J (l + 1) * PM q m) - 1 := by
        rw [Int.ofNat_sub h1]; push_cast; rfl
      rw [← e]; exact Int.ofNat_dvd.mpr this
    have hML : ((q ^ (KM q m + 1 - l) * uqq q : Nat) : Int) ∣ (LamA q m : Int) := by
      apply Int.ofNat_dvd.mpr
      unfold LamA
      exact Nat.mul_dvd_mul_right (Nat.pow_dvd_pow q (by omega)) _
    have hba : b (l + 1) = a := hb (l + 1) (by omega) hl
    generalize hy : chain (q : Int) (PM q m) y0 b J l = y at hD
    generalize hGv : (2 : Int) ^ (J (l + 1) * PM q m) = G at hG
    have hX : ((q ^ (KM q m + 1 - l) * uqq q : Nat) : Int) ∣ (2 : Int) ^ a * G * y - 1 - (q : Int) * c := by
      have e : (2 : Int) ^ a * G * y - 1 - (q : Int) * c
          = (2 : Int) ^ a * y * (G - 1) + (2 : Int) ^ a * (y - c) + (((2 : Int) ^ a - q) * c - 1) := by
        int_ring
      rw [e]
      exact Int.dvd_add (Int.dvd_add (Int.dvd_trans (Int.dvd_trans hML hG) (Int.dvd_mul_left _ _))
        (Int.dvd_trans hD (Int.dvd_mul_left _ _))) (Int.dvd_trans hML hc)
    have eM : ((q ^ (KM q m + 1 - l) * uqq q : Nat) : Int)
        = (q : Int) * ((q ^ (KM q m + 1 - (l + 1)) * uqq q : Nat) : Int) := by
      have e1 : KM q m + 1 - l = (KM q m + 1 - (l + 1)) + 1 := by omega
      rw [e1, Nat.pow_succ]; push_cast; int_ring
    rw [eM] at hX
    obtain ⟨t, ht⟩ := hX
    have hnum : (2 : Int) ^ a * G * y - 1
        = (q : Int) * (c + ((q ^ (KM q m + 1 - (l + 1)) * uqq q : Nat) : Int) * t) := by
      rw [Int.mul_add, ← Int.mul_assoc, ← ht]; omega
    have hq0 : (q : Int) ≠ 0 := by omega
    have hchain : chain (q : Int) (PM q m) y0 b J (l + 1)
        = c + ((q ^ (KM q m + 1 - (l + 1)) * uqq q : Nat) : Int) * t := by
      show ((2 : Int) ^ (b (l + 1)) * 2 ^ (J (l + 1) * PM q m) * chain (q : Int) (PM q m) y0 b J l - 1)
        / (q : Int) = _
      rw [hba, hGv, hy, hnum, Int.mul_ediv_cancel_left _ hq0]
    refine ⟨fun i hi => ?_, ⟨t, by rw [hchain]; omega⟩⟩
    rcases Nat.lt_or_ge i l with h1 | h1
    · exact hI i h1
    · have : i = l := by omega
      subst this
      rw [hba, hGv, hy, hnum]
      exact Int.dvd_mul_right _ _

end Collatz
