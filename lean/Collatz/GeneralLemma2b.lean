import Collatz.GeneralVal

/-! Lemma 2(2) of generalAB.md: S_j ≡ j (mod q) and v_p(S_j) = v_p(j) for primes p | q. -/

namespace Collatz

/-- S_j ≡ j (mod q), since 2^d ≡ 1 (mod q). -/
theorem Ssum_mod {q d : Nat} (hd : 2 ^ d % q = 1 % q) : ∀ j, Ssum d j % q = j % q
  | 0 => by simp [Ssum]
  | j + 1 => by
    show (Ssum d j + 2 ^ (d * j)) % q = (j + 1) % q
    have h1 : 2 ^ (d * j) % q = 1 % q := by
      rw [Nat.pow_mul]; exact pow_mod_one q (2 ^ d) j hd
    rw [Nat.add_mod, Nat.add_mod j 1 q, Ssum_mod hd j, h1]

theorem odd_of_dvd_odd {p q : Nat} (hpq : p ∣ q) (hq : q % 2 = 1) : p % 2 = 1 := by
  match Nat.mod_two_eq_zero_or_one p with
  | Or.inl h0 =>
    have h2 : 2 ∣ p := Nat.dvd_of_mod_eq_zero h0
    have h3 := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h2 hpq)
    omega
  | Or.inr h1 => exact h1

theorem uu_spec {q : Nat} (hq : 1 < q) (hodd : q % 2 = 1) :
    2 ^ dq q = 1 + q * uu q ∧ 1 ≤ uu q := by
  have hd := dq_isOrder2 hq hodd
  have hu : 2 ^ dq q = 1 + q * uu q := pow_eq_of_order hq hd
  refine ⟨hu, ?_⟩
  have h2 : 2 ^ 1 ≤ 2 ^ dq q := Nat.pow_le_pow_right (by omega) hd.1
  match Nat.eq_zero_or_pos (uu q) with
  | Or.inl h0 => rw [h0, Nat.mul_zero] at hu; omega
  | Or.inr hp => exact hp


/-- Every n > 1 has a prime divisor (least divisor ≥ 2). -/
theorem exists_prime_dvd (n : Nat) (h : 1 < n) : ∃ p, IsPrime p ∧ p ∣ n := by
  obtain ⟨d, ⟨hd2, hdn⟩, hmin⟩ := exists_least (fun d => 2 ≤ d ∧ d ∣ n) ⟨n, by omega, Nat.dvd_refl n⟩
  refine ⟨d, ⟨hd2, fun a ha => ?_⟩, hdn⟩
  have han : a ∣ n := Nat.dvd_trans ha hdn
  have hale : a ≤ d := Nat.le_of_dvd (by omega) ha
  match Nat.lt_or_ge a 2 with
  | Or.inl hlt =>
    match Nat.eq_zero_or_pos a with
    | Or.inl h0 => rw [h0] at ha; have := Nat.eq_zero_of_zero_dvd ha; omega
    | Or.inr hp => exact Or.inl (by omega)
  | Or.inr hge =>
    match Nat.lt_or_ge a d with
    | Or.inl hlt => exact absurd ⟨hge, han⟩ (hmin a hlt)
    | Or.inr hge' => exact Or.inr (by omega)

theorem one_le_vp {p n : Nat} (hp : 1 < p) (hn : 0 < n) (h : p ∣ n) : 1 ≤ vp p n := by
  have hv := val_vp hp hn
  match Nat.eq_zero_or_pos (vp p n) with
  | Or.inl h0 => exfalso; apply hv.2; rw [h0, Nat.zero_add, Nat.pow_one]; exact h
  | Or.inr h => exact h

/-- p^v | u with p^v ≤ u gives v ≤ log₂ u. -/
theorem val_le_log2 {p v u : Nat} (hp : 1 < p) (hu : 0 < u) (hd : p ^ v ∣ u) : v ≤ Nat.log2 u := by
  have h1 : p ^ v ≤ u := Nat.le_of_dvd hu hd
  have h2 : 2 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp v
  exact (Nat.le_log2 (by omega)).2 (Nat.le_trans h2 h1)

/-- u / u_q is coprime to q. -/
theorem uq_cofactor_coprime {q u : Nat} (hq : 1 < q) (hu : 1 ≤ u) :
    Nat.Coprime (u / uq q u) q := by
  have hdu : uq q u ∣ u := Nat.gcd_dvd_left u (q ^ (Nat.log2 u + 1))
  have hdq : uq q u ∣ q ^ (Nat.log2 u + 1) := Nat.gcd_dvd_right u _
  have hupos : 0 < uq q u := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0] at hdu; have := Nat.eq_zero_of_zero_dvd hdu; omega)
  have hmul : uq q u * (u / uq q u) = u := Nat.mul_div_cancel' hdu
  have hr : 0 < u / uq q u := Nat.pos_of_ne_zero (fun h0 => by rw [h0, Nat.mul_zero] at hmul; omega)
  -- the gcd is 1, else a prime divides both
  match Nat.lt_or_ge 1 (Nat.gcd (u / uq q u) q) with
  | Or.inr hle =>
    have hg0 : 0 < Nat.gcd (u / uq q u) q := Nat.gcd_pos_of_pos_right _ (by omega)
    exact Nat.le_antisymm hle hg0
  | Or.inl hg =>
    exfalso
    obtain ⟨p, hp, hpg⟩ := exists_prime_dvd _ hg
    have hpr : p ∣ u / uq q u := Nat.dvd_trans hpg (Nat.gcd_dvd_left _ _)
    have hpq : p ∣ q := Nat.dvd_trans hpg (Nat.gcd_dvd_right _ _)
    have hp1 : 1 < p := by have := hp.1; omega
    have hvu := val_vp (p := p) (n := u) hp1 (by omega)
    have hvq' := val_vp (p := p) (n := uq q u) hp1 hupos
    have hvr := val_vp (p := p) (n := u / uq q u) hp1 hr
    have hr1 := one_le_vp hp1 hr hpr
    -- p^ν | q^L, hence p^ν | uq
    have hνL : vp p u ≤ Nat.log2 u + 1 := by
      have := val_le_log2 hp1 (by omega) hvu.1; omega
    obtain ⟨c, hc⟩ := hpq
    have h1 : p ^ vp p u ∣ q ^ (Nat.log2 u + 1) := by
      have e : q ^ vp p u = p ^ vp p u * c ^ vp p u := by rw [hc, Nat.mul_pow]
      have h2 : p ^ vp p u ∣ q ^ vp p u := ⟨c ^ vp p u, e⟩
      exact Nat.dvd_trans h2 (Nat.pow_dvd_pow q hνL)
    have h3 : p ^ vp p u ∣ uq q u := Nat.dvd_gcd hvu.1 h1
    -- so ν ≤ ν'
    have hle : vp p u ≤ vp p (uq q u) := by
      match Nat.lt_or_ge (vp p (uq q u)) (vp p u) with
      | Or.inl hlt =>
        exact absurd (Nat.dvd_trans (Nat.pow_dvd_pow p hlt) h3) hvq'.2
      | Or.inr h => exact h
    -- valuations add: u = uq * r
    have hprod := val_mul hp hvq' hvr
    rw [hmul] at hprod
    have := val_unique hvu hprod
    omega

end Collatz
