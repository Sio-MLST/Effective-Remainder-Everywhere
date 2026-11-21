import Collatz.GeneralHyp

/-! Edge z → c_a for z ∈ Rcore (markdown Prop 1, (2)⇒(3) short-path case), choice-free.
    Route: 2^{i0} z ≡ c_a (mod N); exponents of 2 agree mod d, hence mod N;
    so 2^{a0(z)} z ≡ 1 + q c_a (mod N), giving c_0(z) ≡ c_a (mod u_q). -/

namespace Collatz

/-- 2^d ≡ 1 (mod N_q). -/
theorem pow_d_mod_Nqq {q : Nat} (hq : 1 < q) (hodd : q % 2 = 1) :
    2 ^ dq q % Nqq q = 1 % Nqq q := by
  have hdu : 2 ^ dq q = 1 + q * uu q := (uu_spec hq hodd).1
  have hdvd : Nqq q ∣ q * uu q := Nat.mul_dvd_mul_left q (Nat.gcd_dvd_left _ _)
  obtain ⟨t, ht⟩ := hdvd
  rw [hdu, ht, Nat.add_mul_mod_self_left]

/-- Exponents congruent mod d give equal powers mod N_q. -/
theorem pow_Nqq_of_dvd {q k : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (y : Nat) :
    2 ^ (y + dq q * k) % Nqq q = 2 ^ y % Nqq q :=
  pow_mod_period (pow_d_mod_Nqq hq hodd) y k

/-- 2^x ≡ 2^y (mod q) with y ≤ x forces d ∣ x − y. -/
theorem dvd_of_pow_mod_eq {q x y : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hyx : y ≤ x)
    (h : 2 ^ x % q = 2 ^ y % q) : dq q ∣ x - y := by
  have hd := dq_isOrder2 hq hodd
  have e : 2 ^ x = 2 ^ y * 2 ^ (x - y) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hyx]
  have hcop : Nat.Coprime q (2 ^ y) := Nat.Coprime.pow_right y (coprime_two_of_odd hodd)
  have h1 : 2 ^ (x - y) % q = 1 % q := by
    apply mod_cancel_mul_left hcop (Nat.one_le_two_pow)
    rw [← e, Nat.mul_one]
    exact h
  exact order_dvd hd h1

/-- 2^m z ≡ 1 (mod q) gives z ≡ 2^{m(d−1)} (mod q), so z ∈ ⟨2⟩ mod q. -/
theorem z_mod_pow_of_inv {q m z : Nat} (hq : 1 < q) (hodd : q % 2 = 1)
    (h : 2 ^ m * z % q = 1 % q) : z % q = 2 ^ (m * (dq q - 1)) % q := by
  have hd := dq_isOrder2 hq hodd
  have hd1 : 1 ≤ dq q := hd.1
  have hdq1 : 2 ^ dq q % q = 1 % q := hd.2.1
  have e : 2 ^ (m * dq q) * z = 2 ^ (m * (dq q - 1)) * (2 ^ m * z) := by
    rw [← Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    rw [Nat.mul_sub, Nat.mul_one]
    have : m ≤ m * dq q := Nat.le_mul_of_pos_right m hd1
    omega
  have hA : 2 ^ (m * dq q) * z % q = z % q := by
    rw [Nat.mul_mod, Nat.mul_comm m (dq q), Nat.pow_mul, pow_mod_one q _ m hdq1, Nat.mod_mul_mod, Nat.one_mul, Nat.mod_mod]
  have hB : 2 ^ (m * (dq q - 1)) * (2 ^ m * z) % q = 2 ^ (m * (dq q - 1)) % q := by
    rw [Nat.mul_mod, h, ← Nat.mul_mod, Nat.mul_one]
  rw [← hA, e, hB]

theorem bco_add_q (q a : Nat) (hq : 1 < q) (hodd : q % 2 = 1) :
    bco q a + q = 2 ^ a + Nqq q := by
  have h1 : q ≤ Nqq q := Nat.le_mul_of_pos_right q (uqq_pos hq hodd)
  have h2 : q ≤ 2 ^ a + Nqq q := Nat.le_trans h1 (Nat.le_add_left _ _)
  unfold bco; omega

/-- 2^a·c_a ≡ 1 + q·c_a (mod N_q). -/
theorem two_pow_ca_mod_Nqq {q a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) :
    2 ^ a * ca q a % Nqq q = (1 + q * ca q a) % Nqq q := by
  have hs : 2 ^ a * ca q a + Nqq q * ca q a = bco q a * ca q a + q * ca q a := by
    have := bco_add_q q a hq hodd
    have e : (bco q a + q) * ca q a = (2 ^ a + Nqq q) * ca q a := by rw [this]
    rw [Nat.add_mul, Nat.add_mul] at e
    omega
  calc 2 ^ a * ca q a % Nqq q
      = (2 ^ a * ca q a + Nqq q * ca q a) % Nqq q := by
        rw [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod]
    _ = (bco q a * ca q a + q * ca q a) % Nqq q := by rw [hs]
    _ = ((bco q a * ca q a) % Nqq q + (q * ca q a) % Nqq q) % Nqq q := Nat.add_mod _ _ _
    _ = (1 % Nqq q + (q * ca q a) % Nqq q) % Nqq q := by rw [ca_inv hq hodd]
    _ = (1 + q * ca q a) % Nqq q := (Nat.add_mod _ _ _).symm

/-- 2^{i0} z ≡ c_a (mod N_q), from 2^{i0} z · bco ≡ 1 and bco · c_a ≡ 1. -/
theorem two_pow_mul_eq_ca {q a i0 z : Nat} (hq : 1 < q) (hodd : q % 2 = 1)
    (hX : 2 ^ i0 * z * bco q a % Nqq q = 1 % Nqq q) :
    2 ^ i0 * z % Nqq q = ca q a % Nqq q := by
  have hN := Nqq_gt hq hodd
  have hC := ca_inv (a := a) hq hodd
  calc 2 ^ i0 * z % Nqq q
      = (2 ^ i0 * z * (bco q a * ca q a)) % Nqq q := by
        rw [Nat.mul_mod (2 ^ i0 * z) (bco q a * ca q a), hC, Nat.mod_eq_of_lt hN,
          Nat.mul_one, Nat.mod_mod]
    _ = (2 ^ i0 * z * bco q a % Nqq q * (ca q a % Nqq q)) % Nqq q := by
        rw [show 2 ^ i0 * z * (bco q a * ca q a) = (2 ^ i0 * z * bco q a) * ca q a by
          simp only [Nat.mul_assoc]]
        exact Nat.mul_mod _ _ _
    _ = (1 % Nqq q * (ca q a % Nqq q)) % Nqq q := by rw [hX]
    _ = ca q a % Nqq q := by rw [Nat.mod_eq_of_lt hN, Nat.one_mul, Nat.mod_mod]

/-- From 2^{x} z ≡ 1 ≡ 2^{y} z (mod q) with z coprime to q: 2^x ≡ 2^y (mod N_q). -/
theorem pow_Nqq_of_inv_pair {q x y z : Nat} (hq : 1 < q) (hodd : q % 2 = 1)
    (hcopq : Nat.Coprime q z) (hx : 2 ^ x * z % q = 1 % q) (hy : 2 ^ y * z % q = 1 % q) :
    2 ^ x % Nqq q = 2 ^ y % Nqq q := by
  have hmq : 2 ^ x % q = 2 ^ y % q :=
    mod_cancel_mul_right hcopq (by rw [hx, hy])
  match Nat.le_total y x with
  | Or.inl hyx =>
    have hd := dvd_of_pow_mod_eq hq hodd hyx hmq
    obtain ⟨k, hk⟩ := hd
    have e : x = y + dq q * k := by omega
    rw [e]
    exact pow_Nqq_of_dvd hq hodd y
  | Or.inr hxy =>
    have hd := dvd_of_pow_mod_eq hq hodd hxy hmq.symm
    obtain ⟨k, hk⟩ := hd
    have e : y = x + dq q * k := by omega
    rw [e]
    exact (pow_Nqq_of_dvd hq hodd x).symm

/-- Edge z → c_a for z ∈ R_core (some exponent a ∈ 1..d). -/
theorem edge_to_ca {q z : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hz1 : 1 ≤ z)
    (hcop : Nat.Coprime z (Nqq q)) (hH : HypH q z) :
    ∃ a, 1 ≤ a ∧ a ≤ dq q ∧ Edge q z (ca q a) := by
  obtain ⟨a, ha1, haD, hHa⟩ := hH
  refine ⟨a, ha1, haD, ?_⟩
  obtain ⟨i0, hi0, hX⟩ := hypha_nat hq hodd hz1 hHa
  have hNq := Nqq_gt hq hodd
  have hinvq : 2 ^ (i0 + a) * z % q = 1 % q := by
    have h1 : 2 ^ i0 * z * bco q a % q = 1 % q := mod_q_of_mod_N (Nqq_dvd q) hX
    have h2 : 2 ^ i0 * z * bco q a % q = 2 ^ (i0 + a) * z % q := by
      rw [Nat.mul_mod, bco_mod_q q a hq hodd, ← Nat.mul_mod, Nat.pow_add]
      congr 1
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    rw [← h2]; exact h1
  have hVz : Vq q z := ⟨hcop, _, z_mod_pow_of_inv hq hodd hinvq⟩
  have hVc := ca_Vq hq hodd ha1 haD
  refine ⟨hVz, hVc, ?_⟩
  have hc0 := c0_spec hq hodd hVz hz1
  have hcopq : Nat.Coprime q z := (Nat.Coprime.coprime_dvd_right (Nqq_dvd q) hcop).symm
  have hA := (a0_spec hq hodd hVz.2).2.2.1
  have hpow := pow_Nqq_of_inv_pair hq hodd hcopq hA hinvq
  have hz_mod : 2 ^ a0 q z * z % Nqq q = 2 ^ (i0 + a) * z % Nqq q := by
    rw [Nat.mul_mod, hpow, ← Nat.mul_mod]
  have hmid : 2 ^ (i0 + a) * z % Nqq q = 2 ^ a * ca q a % Nqq q := by
    have e : 2 ^ (i0 + a) * z = 2 ^ a * (2 ^ i0 * z) := by
      rw [Nat.pow_add]
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    rw [e, Nat.mul_mod, two_pow_mul_eq_ca hq hodd hX, ← Nat.mul_mod]
  have hfin : 2 ^ a0 q z * z % Nqq q = (1 + q * ca q a) % Nqq q :=
    hz_mod.trans (hmid.trans (two_pow_ca_mod_Nqq hq hodd))
  have hq1 : (1 + q * c0 q z) % Nqq q = (1 + q * ca q a) % Nqq q := by
    rw [Nat.add_comm, hc0]; exact hfin
  have hmq : q * c0 q z % Nqq q = q * ca q a % Nqq q := mod_eq_of_add_mod_eq hq1
  have h2 : q * (c0 q z % uqq q) = q * (ca q a % uqq q) := by
    rw [← Nat.mul_mod_mul_left, ← Nat.mul_mod_mul_left]
    exact hmq
  exact (Nat.eq_of_mul_eq_mul_left (by omega) h2).symm

/-- Rcore points have z ≥ 1. -/
theorem rcore_pos {q z : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hcop : Nat.Coprime z (Nqq q)) :
    1 ≤ z := by
  match Nat.eq_zero_or_pos z with
  | Or.inl h0 =>
    exfalso
    rw [h0] at hcop
    unfold Nat.Coprime at hcop
    rw [Nat.gcd_zero_left] at hcop
    have := Nqq_gt hq hodd
    omega
  | Or.inr h => exact h

/-- (2)⇒(3), the short case n < κ: an Rcore-path of length n extends to length κ. -/
theorem prop1_two_to_three_short {q t z n κ : Nat} (hq : 1 < q) (hodd : q % 2 = 1)
    (hn : n < κ) (hP : GPath q n t z) (hR : Rcore q z) : ∃ c, GPath q κ t c := by
  obtain ⟨hcop, hH⟩ := hR
  have hz1 := rcore_pos hq hodd hcop
  obtain ⟨a, ha1, haD, hE⟩ := edge_to_ca hq hodd hz1 hcop hH
  have h1 : GPath q 1 z (ca q a) := ⟨ca q a, hE, ca_gpath_loop hq hodd ha1 haD 0⟩
  have hP' : GPath q (n + 1) t (ca q a) := GPath_trans hq hodd n 1 t z (ca q a) hP h1
  have hfin := GPath_trans hq hodd (n + 1) (κ - (n + 1)) t (ca q a) (ca q a) hP'
    (ca_gpath_loop hq hodd ha1 haD (κ - (n + 1)))
  have e : n + 1 + (κ - (n + 1)) = κ := by omega
  rw [e] at hfin
  exact ⟨ca q a, hfin⟩

end Collatz
