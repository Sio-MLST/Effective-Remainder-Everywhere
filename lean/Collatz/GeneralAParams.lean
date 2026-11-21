import Collatz.GeneralCRT

/-! Theorem A, Section 3 parameters attached to m (generalAB.md): structural facts about
    α, m_q, m', e, K, P used throughout Section 4. Choice-free. -/

namespace Collatz

theorem coprime_of_no_prime {a b : Nat} (h : ∀ p, IsPrime p → p ∣ a → p ∣ b → False) :
    Nat.Coprime a b := by
  unfold Nat.Coprime
  match Nat.lt_or_ge 1 (Nat.gcd a b) with
  | Or.inl hg =>
    obtain ⟨p, hp, hpg⟩ := exists_prime_dvd _ hg
    exact absurd (h p hp (Nat.dvd_trans hpg (Nat.gcd_dvd_left _ _))
      (Nat.dvd_trans hpg (Nat.gcd_dvd_right _ _))) id
  | Or.inr hle =>
    match Nat.eq_zero_or_pos (Nat.gcd a b) with
    | Or.inr hp => exact Nat.le_antisymm hle hp
    | Or.inl h0 =>
      exfalso
      have ha : a = 0 := Nat.eq_zero_of_gcd_eq_zero_left h0
      have hb : b = 0 := Nat.eq_zero_of_gcd_eq_zero_right h0
      exact h 2 ⟨Nat.le_refl 2, fun c hc => by
        have := Nat.le_of_dvd (by omega) hc
        rcases Nat.lt_or_ge c 2 with h1 | h1
        · rcases Nat.eq_zero_or_pos c with h0 | h0
          · subst h0; have := Nat.eq_zero_of_zero_dvd hc; omega
          · exact Or.inl (by omega)
        · exact Or.inr (by omega)⟩ (ha ▸ Nat.dvd_zero 2) (hb ▸ Nat.dvd_zero 2)

theorem pow_dvd_pow_of_dvd' {a b : Nat} (h : a ∣ b) (n : Nat) : a ^ n ∣ b ^ n := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c ^ n, Nat.mul_pow a c n⟩

theorem alpha_spec {m : Nat} (hm : 1 ≤ m) :
    m = 2 ^ alphaM m * oddM m ∧ oddM m % 2 = 1 := by
  have hv := val_vp (p := 2) (n := m) (by omega) (by omega)
  have hdv : 2 ^ alphaM m ∣ m := hv.1
  have e : m = 2 ^ alphaM m * oddM m := (Nat.mul_div_cancel' hdv).symm
  refine ⟨e, ?_⟩
  match Nat.mod_two_eq_zero_or_one (oddM m) with
  | Or.inr h => exact h
  | Or.inl h =>
    exfalso
    apply hv.2
    obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h
    refine ⟨c, ?_⟩
    show m = 2 ^ (vp 2 m + 1) * c
    conv => lhs; rw [e]
    rw [hc, Nat.pow_succ, Nat.mul_assoc]; rfl

theorem oddM_pos {m : Nat} (hm : 1 ≤ m) : 1 ≤ oddM m := by
  have := (alpha_spec hm).2; omega

theorem mq_dvd_oddM (q m : Nat) : mqM q m ∣ oddM m := Nat.gcd_dvd_left _ _

theorem MM_eq (q m : Nat) : MM q m = oddM m := Nat.mul_div_cancel' (mq_dvd_oddM q m)

theorem m_decomp {q m : Nat} (hm : 1 ≤ m) : m = 2 ^ alphaM m * (mqM q m * mpM q m) := by
  have h := (alpha_spec hm).1
  rw [show mqM q m * mpM q m = MM q m from rfl, MM_eq]; exact h

theorem mq_dvd_pow (q m : Nat) : mqM q m ∣ q ^ oddM m := Nat.gcd_dvd_right _ _

theorem mp_coprime_q {q m : Nat} (_hq : 1 < q) (hm : 1 ≤ m) : Nat.Coprime (mpM q m) q := by
  apply coprime_of_no_prime
  intro p hp hpm hpq
  have hO := oddM_pos hm
  have hv := val_vp hp.1 (Nat.lt_of_lt_of_le Nat.zero_lt_one hO)
  generalize hvd : vp p (oddM m) = v at hv
  have hvle : v ≤ oddM m := Nat.le_trans (val_le_log2 hp.1 hO hv.1) (Nat.log2_le_self _)
  have h1 : p ^ v ∣ q ^ oddM m :=
    Nat.dvd_trans (pow_dvd_pow_of_dvd' hpq v) (Nat.pow_dvd_pow q hvle)
  have h2 : p ^ v ∣ mqM q m := Nat.dvd_gcd hv.1 h1
  apply hv.2
  rw [Nat.pow_succ, ← MM_eq q m]
  exact Nat.mul_dvd_mul h2 hpm

theorem mp_pos {q m : Nat} (hm : 1 ≤ m) : 1 ≤ mpM q m := by
  have h := MM_eq q m
  have hO := oddM_pos hm
  rcases Nat.eq_zero_or_pos (mpM q m) with h0 | h0
  · unfold MM at h; rw [h0, Nat.mul_zero] at h; omega
  · exact h0

theorem mp_odd {q m : Nat} (hm : 1 ≤ m) : mpM q m % 2 = 1 :=
  odd_of_dvd_odd ⟨mqM q m, by rw [← MM_eq q m]; unfold MM; rw [Nat.mul_comm]⟩ (alpha_spec hm).2

theorem mp_coprime_2q {q m : Nat} (hq : 1 < q) (hm : 1 ≤ m) : Nat.Coprime (mpM q m) (2 * q) :=
  Nat.Coprime.mul_right (coprime_two_of_odd (mp_odd hm)) (mp_coprime_q hq hm)

theorem eM_isOrder2 {q m : Nat} (_hq : 1 < q) (hm : 1 ≤ m) : IsOrder2 (mpM q m) (eM q m) := by
  obtain ⟨D, hD0, hDq, hD⟩ :=
    exists_pow2_period (mpM q m) (mp_pos hm) (coprime_two_of_odd (mp_odd hm))
  have h := srch_spec (fun k => 2 ^ k % mpM q m = 1 % mpM q m) (mpM q m) 1 ⟨D, hD0, by omega, hD⟩
  have hge := srch_ge (fun k => 2 ^ k % mpM q m = 1 % mpM q m) (mpM q m) 1
  exact ⟨Nat.lt_of_lt_of_le Nat.zero_lt_one hge, h.1, fun i hi hid hi' => h.2 i hi hid hi'⟩

theorem KM_spec (q m : Nat) : eQM q m ∣ q ^ KM q m := by
  have h := srch_spec (fun k => eQM q m ∣ q ^ k) (eM q m) 0
    ⟨eM q m, Nat.zero_le _, by omega, Nat.gcd_dvd_right _ _⟩
  exact h.1

/-- P = lcm(d q^K, e) = d q^K f with f prime to q. -/
theorem PM_struct {q m : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) :
    ∃ f, PM q m = dq q * q ^ KM q m * f ∧ Nat.Coprime f q := by
  have hd0 := (dq_isOrder2 hq hodd).1
  have he0 := (eM_isOrder2 (q := q) hq hm).1
  have hA : 0 < dq q * q ^ KM q m := Nat.mul_pos hd0 (Nat.pow_pos (by omega))
  obtain ⟨f, hf⟩ : Nat.gcd (dq q * q ^ KM q m) (eM q m) ∣ eM q m := Nat.gcd_dvd_right _ _
  have hg0 : 0 < Nat.gcd (dq q * q ^ KM q m) (eM q m) := Nat.gcd_pos_of_pos_right _ he0
  have hgl := Nat.gcd_mul_lcm (dq q * q ^ KM q m) (eM q m)
  refine ⟨f, ?_, ?_⟩
  · unfold PM
    apply Nat.eq_of_mul_eq_mul_left hg0
    rw [hgl]
    conv => lhs; rw [hf]
    simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  · apply coprime_of_no_prime
    intro p hp hpf hpq
    have hv := val_vp hp.1 he0
    generalize hvd : vp p (eM q m) = v at hv
    have hvle : v ≤ eM q m := Nat.le_trans (val_le_log2 hp.1 he0 hv.1) (Nat.log2_le_self _)
    have h1 : p ^ v ∣ q ^ eM q m :=
      Nat.dvd_trans (pow_dvd_pow_of_dvd' hpq v) (Nat.pow_dvd_pow q hvle)
    have h2 : p ^ v ∣ eQM q m := Nat.dvd_gcd hv.1 h1
    have h3 : p ^ v ∣ dq q * q ^ KM q m :=
      Nat.dvd_trans (Nat.dvd_trans h2 (KM_spec q m)) (Nat.dvd_mul_left _ _)
    have h4 : p ^ v ∣ Nat.gcd (dq q * q ^ KM q m) (eM q m) := Nat.dvd_gcd h3 hv.1
    apply hv.2
    rw [Nat.pow_succ, hf]
    exact Nat.mul_dvd_mul h4 hpf

theorem dK_dvd_PM (q m : Nat) : dq q * q ^ KM q m ∣ PM q m := Nat.dvd_lcm_left _ _
theorem e_dvd_PM (q m : Nat) : eM q m ∣ PM q m := Nat.dvd_lcm_right _ _

theorem PM_pos {q m : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) : 0 < PM q m :=
  Nat.lcm_pos (Nat.mul_pos (dq_isOrder2 hq hodd).1 (Nat.pow_pos (by omega)))
    (eM_isOrder2 (q := q) hq hm).1

/-- When m' = 1: e = 1 and K = 0. -/
theorem mp_one_params {q m : Nat} (hmp : mpM q m = 1) : eM q m = 1 ∧ KM q m = 0 := by
  have he : eM q m = 1 := by
    unfold eM; rw [hmp]; rfl
  refine ⟨he, ?_⟩
  unfold KM; rw [he]
  unfold eQM; rw [he]
  simp [srch]

end Collatz
