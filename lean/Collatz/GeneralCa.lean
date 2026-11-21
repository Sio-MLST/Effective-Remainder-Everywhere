import Collatz.GeneralInvariance

/-! The residue c_a of generalAB.md, Section 1: (2^a − q)·c_a ≡ 1 (mod N_q).
    Built with the Bezout lemma `nat_bez`, on the natural number 2^a + N_q − q ≡ 2^a − q. -/

namespace Collatz

theorem Nqq_gt {q : Nat} (hq : 1 < q) (hodd : q % 2 = 1) : 1 < Nqq q := by
  have hu := uqq_pos hq hodd
  rw [show Nqq q = q * uqq q from rfl]
  have : q ≤ q * uqq q := Nat.le_mul_of_pos_right q hu
  omega

/-- Primes of u_q divide q: a coprime-to-q number is coprime to u_q. -/
theorem coprime_uq_of_coprime {q u b : Nat} (hq : 1 < q) (hb : Nat.Coprime b q) :
    Nat.Coprime b (uq q u) := by
  unfold Nat.Coprime
  match Nat.lt_or_ge 1 (Nat.gcd b (uq q u)) with
  | Or.inr hle =>
    match Nat.eq_zero_or_pos (Nat.gcd b (uq q u)) with
    | Or.inl h0 =>
      have hb0 : Nat.gcd b (uq q u) ∣ uq q u := Nat.gcd_dvd_right _ _
      rw [h0] at hb0
      have hu0 : uq q u = 0 := Nat.eq_zero_of_zero_dvd hb0
      have hdpow := uq_dvd_pow q u
      rw [hu0] at hdpow
      have : 0 ∣ q ^ (Nat.log2 u + 1) := hdpow
      have hz := Nat.eq_zero_of_zero_dvd this
      have : 0 < q ^ (Nat.log2 u + 1) := Nat.pow_pos (by omega)
      omega
    | Or.inr hp => exact Nat.le_antisymm hle hp
  | Or.inl hg =>
    exfalso
    obtain ⟨p, hp, hpg⟩ := exists_prime_dvd _ hg
    have hpU : p ∣ uq q u := Nat.dvd_trans hpg (Nat.gcd_dvd_right _ _)
    have hpb : p ∣ b := Nat.dvd_trans hpg (Nat.gcd_dvd_left _ _)
    have hpq : p ∣ q := isPrime_dvd_pow hp _ (Nat.dvd_trans hpU (uq_dvd_pow q u))
    have hpg1 : p ∣ Nat.gcd b q := Nat.dvd_gcd hpb hpq
    rw [hb] at hpg1
    have := Nat.le_of_dvd Nat.one_pos hpg1
    have := hp.1
    omega

/-- Coprime to q implies coprime to N_q. -/
theorem coprime_Nqq_of_coprime {q b : Nat} (hq : 1 < q) (hb : Nat.Coprime b q) :
    Nat.Coprime b (Nqq q) :=
  Nat.Coprime.mul_right hb (coprime_uq_of_coprime hq hb)

/-- The natural-number representative 2^a + N_q − q of 2^a − q. -/
def bco (q a : Nat) : Nat := 2 ^ a + Nqq q - q

theorem bco_eq (q a : Nat) (hq : 1 < q) (hodd : q % 2 = 1) :
    bco q a = 2 ^ a + q * (uqq q - 1) := by
  have hU := uqq_pos hq hodd
  unfold bco
  have h1 : q ≤ q * uqq q := Nat.le_mul_of_pos_right q hU
  rw [show Nqq q = q * uqq q from rfl, Nat.mul_sub, Nat.mul_one, Nat.add_sub_assoc h1]

theorem bco_mod_q (q a : Nat) (hq : 1 < q) (hodd : q % 2 = 1) : bco q a % q = 2 ^ a % q := by
  rw [bco_eq q a hq hodd, Nat.add_mul_mod_self_left]

theorem coprime_bco {q a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) :
    Nat.Coprime (bco q a) (Nqq q) := by
  have h2 : Nat.Coprime (2 ^ a) q := Nat.Coprime.pow_left a (Nat.Coprime.symm (coprime_two_of_odd hodd))
  have hq' : Nat.Coprime (bco q a) q := coprime_congr_N (bco_mod_q q a hq hodd).symm h2
  exact coprime_Nqq_of_coprime hq hq'

/-- c_a candidate: least k ≤ N_q with bco·k ≡ 1 (mod N_q), found by `srch` (no choice). -/
def caSearch (q a : Nat) : Nat := srch (fun k => bco q a * k % Nqq q = 1 % Nqq q) (Nqq q) 0

theorem caSearch_exists {q a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) :
    ∃ j, 0 ≤ j ∧ j ≤ 0 + Nqq q ∧ bco q a * j % Nqq q = 1 % Nqq q := by
  obtain ⟨k, w, hkw⟩ := nat_bez (bco q a) (Nqq q) (Nqq_gt hq hodd) (coprime_bco hq hodd)
  have hlt := Nat.mod_lt k (show Nqq q > 0 by have := Nqq_gt hq hodd; omega)
  refine ⟨k % Nqq q, Nat.zero_le _, by omega, ?_⟩
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, hkw, Nat.mul_add_mod]

theorem srch_le (p : Nat → Prop) [DecidablePred p] : ∀ f n, srch p f n ≤ n + f
  | 0, n => by simp [srch]
  | f + 1, n => by
    unfold srch
    by_cases h : p n
    · simp only [h, ↓reduceIte]; omega
    · simp only [h, ↓reduceIte]
      have := srch_le p f (n + 1); omega

theorem caSearch_spec {q a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) :
    bco q a * caSearch q a % Nqq q = 1 % Nqq q ∧ caSearch q a < Nqq q := by
  have hs := srch_spec (fun k => bco q a * k % Nqq q = 1 % Nqq q) (Nqq q) 0
    (caSearch_exists hq hodd)
  have hN := Nqq_gt hq hodd
  have hs1 : bco q a * caSearch q a % Nqq q = 1 % Nqq q := hs.1
  refine ⟨hs1, ?_⟩
  have hle : caSearch q a ≤ 0 + Nqq q := srch_le _ (Nqq q) 0
  match Nat.lt_or_ge (caSearch q a) (Nqq q) with
  | Or.inl h => exact h
  | Or.inr hge =>
    exfalso
    have heq : caSearch q a = Nqq q := by omega
    rw [heq, Nat.mul_mod_left] at hs1
    have : 1 % Nqq q = 1 := Nat.mod_eq_of_lt hN
    omega

/-- c_a := the search result. -/
def ca (q a : Nat) : Nat := caSearch q a


/-- (2^a − q)·c_a ≡ 1 (mod N_q), in the natural-number form bco·c_a. -/
theorem ca_inv {q a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) :
    bco q a * ca q a % Nqq q = 1 % Nqq q := (caSearch_spec hq hodd).1

/-- 2^a c_a ≡ 1 (mod q). -/
theorem ca_mod_q {q a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) :
    2 ^ a * ca q a % q = 1 % q := by
  have h1 : bco q a * ca q a % q = 1 % q := by
    rw [← mod_q_of_mod_N (Nqq_dvd q) (ca_inv hq hodd)]
  rw [Nat.mul_mod, ← bco_mod_q q a hq hodd, ← Nat.mul_mod]
  exact h1

/-- c_a is coprime to N_q (from bco·c_a = N·w + 1). -/
theorem coprime_ca {q a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) :
    Nat.Coprime (ca q a) (Nqq q) := by
  have hN := Nqq_gt hq hodd
  have hX : bco q a * ca q a % Nqq q = 1 := by
    rw [(ca_inv hq hodd), Nat.mod_eq_of_lt hN]
  have hdiv := Nat.div_add_mod (bco q a * ca q a) (Nqq q)
  rw [hX] at hdiv
  unfold Nat.Coprime
  have hg1 : Nat.gcd (ca q a) (Nqq q) ∣ Nqq q := Nat.gcd_dvd_right _ _
  have hg2 : Nat.gcd (ca q a) (Nqq q) ∣ bco q a * ca q a :=
    Nat.dvd_mul_left_of_dvd (Nat.gcd_dvd_left _ _) _
  have hg3 : Nat.gcd (ca q a) (Nqq q) ∣ Nqq q * (bco q a * ca q a / Nqq q) :=
    Nat.dvd_trans hg1 (Nat.dvd_mul_right _ _)
  rw [← hdiv] at hg2
  have hg4 := (Nat.dvd_add_right hg3).mp hg2
  exact Nat.dvd_one.mp hg4

/-- c_a mod q = 2^{d−a} mod q, for 1 ≤ a ≤ d. -/
theorem ca_mod_q_pow {q a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (_ha1 : 1 ≤ a) (haD : a ≤ dq q) :
    ca q a % q = 2 ^ (dq q - a) % q := by
  have hd := dq_isOrder2 hq hodd
  have hdq1 : 2 ^ dq q % q = 1 % q := hd.2.1
  have hinv := ca_mod_q hq hodd (a := a)
  have e : 2 ^ dq q * ca q a = 2 ^ (dq q - a) * (2 ^ a * ca q a) := by
    rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel haD]
  have h1 : 2 ^ dq q * ca q a % q = ca q a % q := by
    rw [Nat.mul_mod, hdq1, ← Nat.mul_mod, Nat.one_mul]
  have h2 : 2 ^ dq q * ca q a % q = 2 ^ (dq q - a) % q := by
    rw [e, Nat.mul_mod, hinv, ← Nat.mul_mod, Nat.mul_one]
  rw [← h1, h2]

/-- c_a ∈ V_q, witnessed by i = d − a. -/
theorem ca_Vq {q a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (ha1 : 1 ≤ a) (haD : a ≤ dq q) :
    Vq q (ca q a) :=
  ⟨coprime_ca hq hodd, dq q - a, ca_mod_q_pow hq hodd ha1 haD⟩

/-- a₀(c_a) = a. -/
theorem a0_ca {q a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (ha1 : 1 ≤ a) (haD : a ≤ dq q) :
    a0 q (ca q a) = a := by
  have hi := (ca_Vq hq hodd ha1 haD).2
  have hs := a0_spec hq hodd hi
  exact (hs.2.2.2 a ha1 haD (ca_mod_q hq hodd)).symm

end Collatz
