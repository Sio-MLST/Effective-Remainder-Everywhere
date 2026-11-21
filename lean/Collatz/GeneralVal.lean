import Collatz.GeneralLemma2

/-! A small choice-free valuation library: `Val p k n` says p^k ∥ n exactly. -/

namespace Collatz

def Val (p k n : Nat) : Prop := p ^ k ∣ n ∧ ¬ p ^ (k + 1) ∣ n

theorem val_unique {p k k' n : Nat} (h : Val p k n) (h' : Val p k' n) : k = k' := by
  match Nat.lt_trichotomy k k' with
  | Or.inl hlt =>
    exact absurd (Nat.dvd_trans (Nat.pow_dvd_pow p hlt) h'.1) h.2
  | Or.inr (Or.inl heq) => exact heq
  | Or.inr (Or.inr hgt) =>
    exact absurd (Nat.dvd_trans (Nat.pow_dvd_pow p hgt) h.1) h'.2

/-- `vp p n` is the exact valuation (p > 1, n > 0). -/
theorem val_vp {p n : Nat} (hp : 1 < p) (hn : 0 < n) : Val p (vp p n) n := by
  have hw : n < p ^ (n + 1) := by
    have h1 : n < 2 ^ n := Nat.lt_two_pow_self
    have h2 : 2 ^ n ≤ p ^ n := Nat.pow_le_pow_left hp n
    have h3 : p ^ n ≤ p ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hsp := srch_spec (fun k => ¬ p ^ (k + 1) ∣ n) n 0
    ⟨n, Nat.zero_le _, by omega, fun hd => by
      have := Nat.le_of_dvd hn hd; omega⟩
  refine ⟨?_, hsp.1⟩
  match Nat.eq_zero_or_pos (srch (fun k => ¬ p ^ (k + 1) ∣ n) n 0) with
  | Or.inl h0 => unfold vp; rw [h0]; exact Nat.one_dvd _
  | Or.inr hpos =>
    have := hsp.2 (srch (fun k => ¬ p ^ (k + 1) ∣ n) n 0 - 1) (Nat.zero_le _) (by omega)
    have e : srch (fun k => ¬ p ^ (k + 1) ∣ n) n 0 - 1 + 1 = srch (fun k => ¬ p ^ (k + 1) ∣ n) n 0 := by
      omega
    rw [e] at this
    exact Decidable.of_not_not this

theorem isPrime_coprime {p x : Nat} (hp : IsPrime p) (h : ¬ p ∣ x) : Nat.Coprime p x := by
  rcases hp.2 _ (Nat.gcd_dvd_left p x) with h1 | h1
  · exact h1
  · exact absurd (h1 ▸ Nat.gcd_dvd_right p x) h

/-- Product rule: valuations add. -/
theorem val_mul {p a b x y : Nat} (hp : IsPrime p) (hx : Val p a x) (hy : Val p b y) :
    Val p (a + b) (x * y) := by
  obtain ⟨⟨x', hx'⟩, hnx⟩ := hx
  obtain ⟨⟨y', hy'⟩, hny⟩ := hy
  have hpx : ¬ p ∣ x' := fun ⟨c, hc⟩ => hnx ⟨c, by rw [hx', hc, Nat.pow_succ]; simp only [Nat.mul_assoc]⟩
  have hpy : ¬ p ∣ y' := fun ⟨c, hc⟩ => hny ⟨c, by rw [hy', hc, Nat.pow_succ]; simp only [Nat.mul_assoc]⟩
  have e : x * y = p ^ (a + b) * (x' * y') := by
    rw [hx', hy', Nat.pow_add]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  refine ⟨⟨x' * y', e⟩, fun hd => ?_⟩
  rw [e, Nat.pow_succ] at hd
  have hd' := Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos (by have := hp.1; omega)) hd
  rcases isPrime_dvd_mul hp hd' with h | h
  · exact hpx h
  · exact hpy h

/-- Cancellation: if p^a ∥ x and p^(a+b) ∥ x y then p^b ∥ y. -/
theorem val_cancel {p a b x y : Nat} (hp : IsPrime p) (hx : Val p a x) (hxy : Val p (a + b) (x * y)) :
    Val p b y := by
  obtain ⟨⟨x', hx'⟩, hnx⟩ := hx
  have hpx : ¬ p ∣ x' := fun ⟨c, hc⟩ => hnx ⟨c, by rw [hx', hc, Nat.pow_succ]; simp only [Nat.mul_assoc]⟩
  have hp0 : 0 < p ^ a := Nat.pow_pos (by have := hp.1; omega)
  have hcop : Nat.Coprime (p ^ b) x' := Nat.Coprime.pow_left b (isPrime_coprime hp hpx)
  constructor
  · have h1 := hxy.1
    rw [hx', Nat.pow_add, Nat.mul_assoc] at h1
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop (Nat.dvd_of_mul_dvd_mul_left hp0 h1)
  · intro ⟨c, hc⟩
    apply hxy.2
    refine ⟨x' * c, ?_⟩
    have e : p ^ (a + b + 1) = p ^ a * p ^ (b + 1) := by rw [← Nat.pow_add, Nat.add_assoc]
    rw [hx', hc, e]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem pow2_expand (a : Nat) : a ^ 2 = a * a := Nat.pow_two a
theorem pow3_expand (a : Nat) : a ^ 3 = a * a * a := by
  rw [show 3 = 2 + 1 from rfl, Nat.pow_succ, pow2_expand]

/-- Key step of Lemma 1(2): p^(k+1) ∥ x implies p^(k+2) ∥ (1+x)^p - 1, for odd prime p. -/
theorem pow_prime_val {p k x : Nat} (hp : IsPrime p) (hodd : p % 2 = 1)
    (hx : Val p (k + 1) x) : Val p (k + 2) ((1 + x) ^ p - 1) := by
  obtain ⟨⟨w, hw⟩, hnw⟩ := hx
  have e1 : p ^ (k + 1 + 1) = p ^ (k + 1) * p := Nat.pow_succ p (k + 1)
  have hpw : ¬ p ∣ w := fun ⟨c, hc⟩ => hnw ⟨c, by
    rw [hw, hc, e1]; simp only [Nat.mul_assoc]⟩
  obtain ⟨z, hz⟩ := binom_cubic x p
  have hp3 : 3 ≤ p := by have := hp.1; omega
  have htri : p ∣ triangle p := by
    have h2 := triangle_two p
    have : p ∣ 2 * triangle p := ⟨p - 1, h2⟩
    rcases isPrime_dvd_mul hp this with h | h
    · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
    · exact h
  obtain ⟨c, hc⟩ := htri
  have hsub : (1 + x) ^ p - 1 = p * x + triangle p * x ^ 2 + x ^ 3 * z := by omega
  have hx' : x = p ^ k * p * w := by rw [hw, Nat.pow_succ]
  have ident : ∀ P : Nat, p * (P * p * w) + (p * c) * (P * p * w) ^ 2 + (P * p * w) ^ 3 * z =
      P * p * p * (w + p * (P * c * w ^ 2 + P * P * w ^ 3 * z)) := by
    intro P
    simp only [pow2_expand, pow3_expand, Nat.mul_add, Nat.add_assoc,
      Nat.mul_comm, Nat.mul_left_comm]
  have e2 : p ^ (k + 2) = p ^ k * p * p := by
    rw [show k + 2 = k + 1 + 1 from rfl, Nat.pow_succ, Nat.pow_succ]
  have key : (1 + x) ^ p - 1 = p ^ (k + 2) * (w + p * (p ^ k * c * w ^ 2 + p ^ k * p ^ k * w ^ 3 * z)) := by
    rw [hsub, hc, e2, hx']
    exact ident (p ^ k)
  rw [key]
  refine ⟨⟨_, rfl⟩, fun hd => ?_⟩
  have e : p ^ (k + 2 + 1) = p ^ (k + 2) * p := Nat.pow_succ p (k + 2)
  rw [e] at hd
  have hd' := Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos (by omega)) hd
  obtain ⟨m, hm⟩ := hd'
  apply hpw
  refine ⟨m - (p ^ k * c * w ^ 2 + p ^ k * p ^ k * w ^ 3 * z), ?_⟩
  rw [Nat.mul_sub]
  omega

/-- Iterating the key step: p^(k+1) ∥ x gives p^(k+1+η) ∥ (1+x)^(p^η) - 1. -/
theorem pow_prime_pow_val {p k x : Nat} (hp : IsPrime p) (hodd : p % 2 = 1)
    (hx : Val p (k + 1) x) : ∀ η, Val p (k + 1 + η) ((1 + x) ^ (p ^ η) - 1)
  | 0 => by
    rw [Nat.pow_zero, Nat.pow_one, Nat.add_comm 1 x, Nat.add_sub_cancel]
    exact hx
  | η + 1 => by
    have ih := pow_prime_pow_val hp hodd hx η
    have hg : 0 < (1 + x) ^ (p ^ η) := Nat.pow_pos (by omega)
    have ih' : Val p (k + η + 1) ((1 + x) ^ (p ^ η) - 1) := by
      have e : k + η + 1 = k + 1 + η := by omega
      rw [e]; exact ih
    have h := pow_prime_val hp hodd ih'
    have e1 : 1 + ((1 + x) ^ (p ^ η) - 1) = (1 + x) ^ (p ^ η) := by omega
    rw [e1, ← Nat.pow_mul, ← Nat.pow_succ] at h
    have e2 : k + η + 2 = k + 1 + (η + 1) := by omega
    rw [e2] at h
    exact h

/-- If p^m ∥ A and p^(m+1) | B then p^m ∥ A + B. -/
theorem val_add_high {p m A B : Nat} (hA : Val p m A) (hB : p ^ (m + 1) ∣ B) :
    Val p m (A + B) := by
  obtain ⟨⟨a, ha⟩, hna⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have e : p ^ (m + 1) = p ^ m * p := Nat.pow_succ p m
  refine ⟨⟨a + p * b, ?_⟩, fun ⟨c, hc⟩ => hna ⟨c - b, ?_⟩⟩
  · rw [ha, hb, e, Nat.mul_add]; simp only [Nat.mul_assoc]
  · rw [Nat.mul_sub]
    omega

/-- For b coprime to p: p^m ∥ x (m ≥ 1) gives p^m ∥ (1+x)^b - 1. -/
theorem pow_unit_val {p m x b : Nat} (hp : IsPrime p) (hm : 1 ≤ m) (hx : Val p m x)
    (hb : ¬ p ∣ b) : Val p m ((1 + x) ^ b - 1) := by
  obtain ⟨z, hz⟩ := binom_quadratic x b
  have hsub : (1 + x) ^ b - 1 = b * x + x ^ 2 * z := by omega
  have hb0 : Val p 0 b := ⟨by rw [Nat.pow_zero]; exact Nat.one_dvd _, by
    rw [Nat.zero_add, Nat.pow_one]; exact hb⟩
  have hbx : Val p m (b * x) := by
    have := val_mul hp hb0 hx
    rwa [Nat.zero_add] at this
  have hhigh : p ^ (m + 1) ∣ x ^ 2 * z := by
    have h1 : p ^ m * p ^ m ∣ x * x := Nat.mul_dvd_mul hx.1 hx.1
    have h2 : p ^ (m + 1) ∣ p ^ m * p ^ m := by
      rw [← Nat.pow_add]; exact Nat.pow_dvd_pow p (by omega)
    rw [pow2_expand]
    exact Nat.dvd_trans (Nat.dvd_trans h2 h1) (Nat.dvd_mul_right _ _)
  rw [hsub]
  exact val_add_high hbx hhigh

/-- Lemma 1(2): for odd prime p, p^(k+1) ∥ x and N ≥ 1 give
    p^(k+1+v_p(N)) ∥ (1+x)^N - 1. -/
theorem lemma1_val {p k x N : Nat} (hp : IsPrime p) (hodd : p % 2 = 1)
    (hx : Val p (k + 1) x) (hN : 0 < N) :
    Val p (k + 1 + vp p N) ((1 + x) ^ N - 1) := by
  have hv := val_vp (p := p) (n := N) (by have := hp.1; omega) hN
  generalize vp p N = v at hv ⊢
  obtain ⟨⟨b, hb⟩, hnb⟩ := hv
  have hpb : ¬ p ∣ b := fun ⟨c, hc⟩ => hnb ⟨c, by
    rw [hb, hc, Nat.pow_succ]; simp only [Nat.mul_assoc]⟩
  have h1 := pow_prime_pow_val hp hodd hx v
  have hg : 0 < (1 + x) ^ (p ^ v) := Nat.pow_pos (by omega)
  have h2 := pow_unit_val hp (by omega) h1 hpb
  have e1 : 1 + ((1 + x) ^ (p ^ v) - 1) = (1 + x) ^ (p ^ v) := by omega
  rw [e1, ← Nat.pow_mul, ← hb] at h2
  exact h2

end Collatz
