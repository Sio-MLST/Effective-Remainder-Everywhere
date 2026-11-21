import Collatz.GeneralCRT

/-! Proposition 1, (3) ⇒ (1) (generalAB.md, Section 2), and the assembled `general_prop1`.
    The p-adic digit induction of the note is carried out uniformly with the moduli
    D_m = u_q / gcd(u_q, q^m): D_0 = u_q, D_κ = 1, D_m ∣ q·D_{m+1}. At each step the next
    class is X = z + q·T, for which c₀(X) = c₀(z) + 2^a·T exactly. Choice-free. -/

namespace Collatz

/-- D_m = u_q / gcd(u_q, q^m). -/
def Dm (q m : Nat) : Nat := uqq q / Nat.gcd (uqq q) (q ^ m)

theorem Dm_mul (q m : Nat) : Dm q m * Nat.gcd (uqq q) (q ^ m) = uqq q :=
  Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)

theorem Dm_dvd (q m : Nat) : Dm q m ∣ uqq q :=
  ⟨Nat.gcd (uqq q) (q ^ m), (Dm_mul q m).symm⟩

theorem Dm_zero (q : Nat) : Dm q 0 = uqq q := by
  unfold Dm; rw [Nat.pow_zero, Nat.gcd_one_right, Nat.div_one]

theorem Dm_kappa {q : Nat} (hq : 1 < q) (hodd : q % 2 = 1) : Dm q (κq q) = 1 := by
  have h : uqq q ∣ q ^ κq q := (kappaQ_spec q (uu q)).1
  unfold Dm
  rw [Nat.gcd_eq_left h]
  exact Nat.div_self (uqq_pos hq hodd)

theorem Dm_step {q : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (m : Nat) :
    Dm q m ∣ q * Dm q (m + 1) := by
  have hU := uqq_pos hq hodd
  have hg : Nat.gcd (uqq q) (q ^ (m + 1)) ∣ q * Nat.gcd (uqq q) (q ^ m) := by
    have h1 : Nat.gcd (uqq q) (q ^ (m + 1)) ∣ Nat.gcd (q * uqq q) (q * q ^ m) := by
      rw [Nat.pow_succ, Nat.mul_comm (q ^ m) q]
      exact Nat.gcd_dvd_gcd_of_dvd_left _ (Nat.dvd_mul_left _ _)
    rw [Nat.gcd_mul_left] at h1
    exact h1
  obtain ⟨h, hh⟩ := hg
  refine ⟨h, ?_⟩
  have hgm : 0 < Nat.gcd (uqq q) (q ^ m) := Nat.gcd_pos_of_pos_left _ hU
  apply Nat.eq_of_mul_eq_mul_left hgm
  have e1 := Dm_mul q m
  have e2 := Dm_mul q (m + 1)
  calc Nat.gcd (uqq q) (q ^ m) * (q * Dm q (m + 1))
      = Dm q (m + 1) * (q * Nat.gcd (uqq q) (q ^ m)) := by
        simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    _ = Dm q (m + 1) * (Nat.gcd (uqq q) (q ^ (m + 1)) * h) := by rw [hh]
    _ = uqq q * h := by rw [← Nat.mul_assoc, e2]
    _ = Nat.gcd (uqq q) (q ^ m) * (Dm q m * h) := by
        rw [← Nat.mul_assoc, Nat.mul_comm (Nat.gcd (uqq q) (q ^ m)) (Dm q m), e1]

/-- 2^d ≡ 1 (mod u_q). -/
theorem pow_d_mod_U {q : Nat} (hq : 1 < q) (hodd : q % 2 = 1) :
    2 ^ dq q % uqq q = 1 % uqq q := by
  have hdu : 2 ^ dq q = 1 + q * uu q := (uu_spec hq hodd).1
  obtain ⟨r, hr⟩ : uqq q ∣ uu q := Nat.gcd_dvd_left _ _
  rw [hdu, hr, Nat.mul_left_comm, Nat.add_mul_mod_self_left]

/-- 2^a · 2^{a(d−1)} ≡ 1 (mod u_q). -/
theorem pow_inv_mod_U {q : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (a : Nat) :
    2 ^ a * 2 ^ (a * (dq q - 1)) % uqq q = 1 % uqq q := by
  have hd1 : 1 ≤ dq q := (dq_isOrder2 hq hodd).1
  have e : 2 ^ a * 2 ^ (a * (dq q - 1)) = (2 ^ dq q) ^ a := by
    rw [← Nat.pow_add, ← Nat.pow_mul]
    congr 1
    have : dq q = dq q - 1 + 1 := by omega
    conv => rhs; rw [this]
    rw [Nat.mul_comm (dq q - 1 + 1) a, Nat.mul_succ]
    omega
  rw [e]
  exact pow_mod_one _ _ _ (pow_d_mod_U hq hodd)

/-- One lifting step: for z ∈ V_q and Y ≡ c₀(z) (mod D_{m+1}) there is a class X with
    X ≡ z (mod D_m), X ∈ V_q and c₀(X) ≡ Y (mod u_q). -/
theorem glift_step {q z Y m : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hz : Vq q z) (hz1 : 1 ≤ z)
    (hY : Y % Dm q (m + 1) = c0 q z % Dm q (m + 1)) :
    ∃ X, 1 ≤ X ∧ Vq q X ∧ X % Dm q m = z % Dm q m ∧ c0 q X % uqq q = Y % uqq q := by
  have hU := uqq_pos hq hodd
  obtain ⟨i, hi⟩ := hz.2
  have hspz := a0_spec hq hodd ⟨i, hi⟩
  generalize hS : Y + (uqq q - 1) * c0 q z = S
  generalize hT : 2 ^ (a0 q z * (dq q - 1)) * S = T
  have hXq : (z + q * T) % q = z % q := Nat.add_mul_mod_self_left z q T
  have hiX : (z + q * T) % q = 2 ^ i % q := hXq.trans hi
  have hVX : Vq q (z + q * T) :=
    ⟨coprime_Nqq_of_coprime hq (coprime_of_mod_pow2 hodd hiX), i, hiX⟩
  have hspX := a0_spec hq hodd ⟨i, hiX⟩
  have ha : a0 q (z + q * T) = a0 q z := by
    have h3 : 2 ^ a0 q z * (z + q * T) % q = 1 % q := by
      rw [Nat.mul_mod, hXq, ← Nat.mul_mod]; exact hspz.2.2.1
    exact (hspX.2.2.2 _ hspz.1 hspz.2.1 h3).symm
  have hX1 : 1 ≤ z + q * T := by omega
  have hc0 : c0 q (z + q * T) = c0 q z + 2 ^ a0 q z * T := by
    have hA := c0_spec hq hodd hVX hX1
    have hB := c0_spec hq hodd hz hz1
    rw [ha] at hA
    have e : 2 ^ a0 q z * (z + q * T) = 2 ^ a0 q z * z + q * (2 ^ a0 q z * T) := by
      rw [Nat.mul_add, Nat.mul_left_comm]
    rw [e] at hA
    apply Nat.eq_of_mul_eq_mul_left (show 0 < q by omega)
    rw [Nat.mul_add]
    omega
  refine ⟨z + q * T, hX1, hVX, ?_, ?_⟩
  · -- D_m ∣ q T
    have hUc : (uqq q - 1) * c0 q z + c0 q z = uqq q * c0 q z := by
      have e : uqq q = uqq q - 1 + 1 := by omega
      conv => rhs; rw [e]
      rw [Nat.add_mul, Nat.one_mul]
    have hSD : Dm q (m + 1) ∣ S := by
      apply Nat.dvd_of_mod_eq_zero
      rw [← hS, Nat.add_mod, hY, ← Nat.add_mod, Nat.add_comm, hUc]
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Dm_dvd q (m + 1)) (Nat.dvd_mul_right _ _))
    have hqT : Dm q m ∣ q * T := by
      rw [← hT]
      exact Nat.dvd_trans (Dm_step hq hodd m)
        (Nat.mul_dvd_mul_left q (Nat.dvd_trans hSD (Nat.dvd_mul_left _ _)))
    obtain ⟨c, hc⟩ := hqT
    rw [hc, Nat.add_mul_mod_self_left]
  · rw [hc0, ← hT, ← Nat.mul_assoc]
    have hPS : 2 ^ a0 q z * 2 ^ (a0 q z * (dq q - 1)) * S % uqq q = S % uqq q := by
      rw [Nat.mul_mod, pow_inv_mod_U hq hodd, ← Nat.mul_mod, Nat.one_mul]
    rw [Nat.add_mod, hPS, ← Nat.add_mod, ← hS]
    have e : c0 q z + (Y + (uqq q - 1) * c0 q z) = Y + uqq q * c0 q z := by
      have e1 : uqq q = uqq q - 1 + 1 := by omega
      conv => rhs; rw [e1]
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [e, Nat.add_mul_mod_self_left]

/-- Size bound for one odd step c_j(x) with j < q. -/
theorem step_bound {q x c j m t : Nat} (hq : 1 < q) (hodd : q % 2 = 1)
    (hx : ∃ i, x % q = 2 ^ i % q) (hj : j < q)
    (hcs : q * c + 1 = 2 ^ (a0 q x + dq q * j) * x)
    (hb : x * q ^ m ≤ 2 ^ (dq q * q * m) * t) :
    c * q ^ (m + 1) ≤ 2 ^ (dq q * q * (m + 1)) * t := by
  have ha0 := (a0_spec hq hodd hx).2.1
  clear hx
  have hdq : dq q * q = dq q * (q - 1) + dq q := by
    rw [← Nat.mul_succ]; congr 1; omega
  have hdj : dq q * j ≤ dq q * (q - 1) := Nat.mul_le_mul_left _ (by omega)
  have he : a0 q x + dq q * j ≤ dq q * q := by omega
  have hp : 2 ^ (a0 q x + dq q * j) ≤ 2 ^ (dq q * q) := Nat.pow_le_pow_right (by omega) he
  have h1 : q * c ≤ 2 ^ (dq q * q) * x := by
    have := Nat.mul_le_mul_right x hp
    omega
  calc c * q ^ (m + 1) = (q * c) * q ^ m := by
        rw [Nat.pow_succ]; simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    _ ≤ (2 ^ (dq q * q) * x) * q ^ m := Nat.mul_le_mul_right _ h1
    _ = 2 ^ (dq q * q) * (x * q ^ m) := Nat.mul_assoc _ _ _
    _ ≤ 2 ^ (dq q * q) * (2 ^ (dq q * q * m) * t) := Nat.mul_le_mul_left _ hb
    _ = 2 ^ (dq q * q * (m + 1)) * t := by
        rw [Nat.mul_succ, Nat.pow_add]; simp only [Nat.mul_comm, Nat.mul_left_comm]

/-- The digit induction: a 𝒢_q-path of length m from t lets us realize, by an integer chain of
    m odd steps c_j (j < q) from t, every value of c₀ mod u_q that is ≡ c₀(z_m) (mod D_m). -/
theorem lift_chain {q t : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (ht : 1 ≤ t) :
    ∀ m z, GPath q m t z → ∀ Y, Y % Dm q m = c0 q z % Dm q m →
      ∃ x, 1 ≤ x ∧ Vq q x ∧ Reaches q x t ∧ x * q ^ m ≤ 2 ^ (dq q * q * m) * t ∧
        c0 q x % uqq q = Y % uqq q
  | 0, z, hP, Y, hY => by
    have hVz : Vq q z := Vq_congr hP.1 hP.2
    have hc := c0_mod_congr hq hodd hP.1 ht hVz (Vq_pos hq hodd hVz) hP.2
    rw [Dm_zero] at hY
    refine ⟨t, ht, hP.1, ⟨0, rfl⟩, by simp, ?_⟩
    rw [hc, hY]
  | m + 1, z, hP, Y, hY => by
    obtain ⟨c, hc, h1⟩ := GPath_split hq hodd m 1 t z hP
    obtain ⟨z1, hE, hz1z⟩ := h1
    have hVz1 : Vq q z1 := hE.2.1
    have hz11 := Vq_pos hq hodd hVz1
    have hVz := Vq_congr hVz1 hz1z.2
    have hcc := c0_mod_congr hq hodd hVz1 hz11 hVz (Vq_pos hq hodd hVz) hz1z.2
    have hD1 := Dm_dvd q (m + 1)
    have hY' : Y % Dm q (m + 1) = c0 q z1 % Dm q (m + 1) := by
      rw [hY, ← Nat.mod_mod_of_dvd (c0 q z) hD1, ← hcc, Nat.mod_mod_of_dvd _ hD1]
    obtain ⟨X, hX1, hVX, hXD, hXc⟩ := glift_step hq hodd hVz1 hz11 hY'
    have hD0 := Dm_dvd q m
    have hXc' : X % Dm q m = c0 q c % Dm q m := by
      rw [hXD, ← Nat.mod_mod_of_dvd z1 hD0, hE.2.2, Nat.mod_mod_of_dvd _ hD0]
    obtain ⟨x, hx1, hVx, hRx, hbx, hcx⟩ := lift_chain hq hodd ht m c hc X hXc'
    obtain ⟨j, hj, hjN⟩ := visit_exists hq hodd hVx.2 hx1 X hcx.symm
    obtain ⟨hcs, hc1, hcodd⟩ := cj_spec hq hodd hVx.2 hx1 j
    have hVx' : Vq q (cj q x j) := Vq_congr hVX hjN.symm
    have hcc' := c0_mod_congr hq hodd hVx' hc1 hVX hX1 hjN
    refine ⟨cj q x j, hc1, hVx', reaches_trans q (reaches_of_step hcodd hcs) hRx,
      step_bound hq hodd hVx.2 hj hcs hbx, ?_⟩
    rw [hcc', hXc]

/-- Int form of (H) from its ℕ form, for a given exponent i0. -/
theorem hdvd_of_nat {q a y i0 : Nat} (hq : 1 < q) (hodd : q % 2 = 1)
    (hi : 2 ^ i0 * y * bco q a % Nqq q = 1 % Nqq q) :
    ((Nqq q : Nat) : Int) ∣ (2 : Int) ^ i0 * (y : Int) * ((2 : Int) ^ a - (q : Int)) - 1 := by
  have hN := Nqq_gt hq hodd
  have hmod1 : 2 ^ i0 * y * bco q a % Nqq q = 1 := by rw [hi, Nat.mod_eq_of_lt hN]
  have hdiv := Nat.div_add_mod (2 ^ i0 * y * bco q a) (Nqq q)
  rw [hmod1] at hdiv
  generalize (2 ^ i0 * y * bco q a) / Nqq q = c at hdiv
  have hI : (2 : Int) ^ i0 * (y : Int) * ((bco q a : Nat) : Int) = (Nqq q : Int) * (c : Int) + 1 := by
    exact_mod_cast hdiv.symm
  rw [bco_cast q a hq hodd] at hI
  exact ⟨(c : Int) - (2 : Int) ^ i0 * (y : Int), by int_ring⟩

/-- Proposition 1, (3) ⇒ (1), with the size bound and the (a = 1, i₀ = 0) refinement. -/
theorem prop1_three_to_one {q t : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (ht : 1 ≤ t)
    (h3 : ∃ z, GPath q (κq q) t z) :
    ∃ x, Reaches q x t ∧ HypH q x ∧
      x * q ^ (κq q + 1) ≤ 2 ^ (dq q * q * (κq q + 1)) * t ∧
      (κq q = 0 → x = t ∧ HypHa q 1 t) ∧
      (1 ≤ κq q → ((Nqq q : Nat) : Int) ∣ (x : Int) * (2 - (q : Int)) - 1) := by
  obtain ⟨z, hP⟩ := h3
  have hd := dq_isOrder2 hq hodd
  match Nat.eq_zero_or_pos (κq q) with
  | Or.inl h0 =>
    rw [h0] at hP
    have hVt : Vq q t := hP.1
    have hU1 : uqq q = 1 := (kappaQ_zero_iff q (uu q)).mp h0
    have hNq : Nqq q = q := by rw [Nqq_eq, hU1, Nat.mul_one]
    obtain ⟨ha1, haD, hpa, _⟩ := a0_spec hq hodd hVt.2
    have hnat : 2 ^ (a0 q t - 1) * t * bco q 1 % Nqq q = 1 % Nqq q := by
      rw [hNq, Nat.mul_mod, bco_mod_q q 1 hq hodd, ← Nat.mul_mod]
      have e : 2 ^ (a0 q t - 1) * t * 2 ^ 1 = 2 ^ a0 q t * t := by
        have e1 : a0 q t = a0 q t - 1 + 1 := by omega
        conv => rhs; rw [e1]
        rw [Nat.pow_one, Nat.pow_succ]; simp only [Nat.mul_comm, Nat.mul_left_comm]
      rw [e]; exact hpa
    have hHa : HypHa q 1 t := hypha_of_nat hq hodd ht (by omega) hnat
    have hqd : q ≤ 2 ^ (dq q * q) := by
      have h1 : q < 2 ^ q := Nat.lt_two_pow_self
      have h2 : 2 ^ q ≤ 2 ^ (dq q * q) :=
        Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_left q hd.1)
      omega
    refine ⟨t, ⟨0, rfl⟩, ⟨1, Nat.le_refl 1, hd.1, hHa⟩, ?_, fun _ => ⟨rfl, hHa⟩,
      fun h1 => absurd h1 (by rw [h0]; exact Nat.not_succ_le_zero 0)⟩
    rw [h0, Nat.zero_add, Nat.pow_one, Nat.mul_one, Nat.mul_comm t q]
    exact Nat.mul_le_mul_right t hqd
  | Or.inr hpos =>
    have hY : ca q 1 % Dm q (κq q) = c0 q z % Dm q (κq q) := by
      rw [Dm_kappa hq hodd, Nat.mod_one, Nat.mod_one]
    obtain ⟨x, hx1, hVx, hRx, hbx, hcx⟩ := lift_chain hq hodd ht (κq q) z hP (ca q 1) hY
    obtain ⟨j, hj, hjN⟩ := visit_exists hq hodd hVx.2 hx1 (ca q 1) hcx.symm
    obtain ⟨hcs, hc1, hcodd⟩ := cj_spec hq hodd hVx.2 hx1 j
    have hnat : 2 ^ 0 * cj q x j * bco q 1 % Nqq q = 1 % Nqq q := by
      rw [Nat.pow_zero, Nat.one_mul, Nat.mul_mod, hjN, ← Nat.mul_mod, Nat.mul_comm]
      exact ca_inv hq hodd
    have hdv := hdvd_of_nat hq hodd hnat
    refine ⟨cj q x j, reaches_trans q (reaches_of_step hcodd hcs) hRx,
      ⟨1, Nat.le_refl 1, hd.1, hypha_of_nat hq hodd hc1 hd.1 hnat⟩,
      step_bound hq hodd hVx.2 hj hcs hbx, fun h0 => absurd h0 (by omega), fun _ => ?_⟩
    simpa using hdv

/-- Proposition 1 (Exact Partition Criterion), all parts. -/
theorem general_prop1 {q t : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (ht : 1 ≤ t) : Prop1 q t := by
  have two_three : (Vq q t ∧ ∃ n z, GPath q n t z ∧ Rcore q z) → ∃ z, GPath q (κq q) t z := by
    intro ⟨_, n, z, hP, hR⟩
    match Nat.lt_or_ge n (κq q) with
    | Or.inl hlt => exact prop1_two_to_three_short hq hodd hlt hP hR
    | Or.inr hge => exact prop1_two_to_three_long hq hodd hge hP
  have three_one : (∃ z, GPath q (κq q) t z) → ∃ x, Reaches q x t ∧ HypH q x := by
    intro h
    obtain ⟨x, hR, hH, _⟩ := prop1_three_to_one hq hodd ht h
    exact ⟨x, hR, hH⟩
  refine ⟨⟨fun ⟨x, hR, hH⟩ => prop1_one_to_two hq hodd ht hR hH,
    fun h => three_one (two_three h)⟩, ⟨two_three, fun h => ?_⟩,
    prop1_three_to_one hq hodd ht⟩
  obtain ⟨x, hR, hH⟩ := three_one h
  exact prop1_one_to_two hq hodd ht hR hH

end Collatz
