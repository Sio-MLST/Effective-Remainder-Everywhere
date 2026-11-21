import Collatz.Arithmetic

namespace Collatz

section Map
variable (q : Nat)

def collatz (n : Nat) : Nat := if n % 2 = 0 then n / 2 else q * n + 1

def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter f k (f n)

theorem iter_add (f : Nat → Nat) (m n : Nat) : ∀ x, iter f (m + n) x = iter f m (iter f n x) := by
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; exact ih (f x)

def Reaches (n v : Nat) : Prop := ∃ k, iter (collatz q) k n = v

theorem collatz_double (a : Nat) : collatz q (2 * a) = a := by
  unfold collatz; split <;> omega

theorem reaches_trans {a b c : Nat} (h1 : Reaches q a b) (h2 : Reaches q b c) : Reaches q a c := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  exact ⟨k2 + k1, by rw [iter_add, hk1, hk2]⟩

end Map

class NonWieferich (q : Nat) : Prop where
  one_lt : 1 < q
  unit : ∃ d u, 2 ^ d = 1 + q * u ∧ Nat.Coprime q u

theorem pow_mod_period {b y n : Nat} (h : b ^ y % n = 1 % n) (x : Nat) :
    ∀ N, b ^ (x + y * N) % n = b ^ x % n
  | 0 => by simp
  | N + 1 => by
    rw [Nat.mul_succ, ← Nat.add_assoc, Nat.pow_add, Nat.mul_mod, pow_mod_period h x N, h,
      ← Nat.mul_mod, Nat.mul_one]

theorem mod_cancel_mul_right {m c x y : Nat} (hcop : Nat.Coprime m c)
    (h : (x * c) % m = (y * c) % m) : x % m = y % m := by
  rcases Nat.le_total y x with hle | hle
  · exact mod_cancel_mul_left hcop hle (by rwa [Nat.mul_comm c x, Nat.mul_comm c y])
  · exact (mod_cancel_mul_left hcop hle (by rw [Nat.mul_comm c x, Nat.mul_comm c y]; exact h.symm)).symm

theorem exists_least (P : Nat → Prop) [DecidablePred P] :
    (∃ n, P n) → ∃ n, P n ∧ ∀ r, r < n → ¬ P r := by
  have aux : ∀ N, (∀ r, r < N → ¬ P r) ∨ ∃ n, P n ∧ ∀ r, r < n → ¬ P r := by
    intro N
    induction N with
    | zero => exact Or.inl (fun r hr _ => absurd hr (Nat.not_lt_zero r))
    | succ N ih =>
      rcases ih with h | h
      · match (inferInstance : Decidable (P N)) with
        | isTrue hN =>
          exact Or.inr ⟨N, hN, h⟩
        | isFalse hN =>
          refine Or.inl (fun r hr hPr => ?_)
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr) with hlt | heq
          · exact h r hlt hPr
          · exact hN (by rw [← heq]; exact hPr)
      · exact Or.inr h
  rintro ⟨n, hn⟩
  rcases aux (n + 1) with h | h
  · exact absurd hn (h n (Nat.lt_succ_self n))
  · exact h

theorem exists_pow2_period (m' : Nat) (hM : 0 < m') (hc : Nat.Coprime m' 2) :
    ∃ D, 0 < D ∧ D ≤ m' ∧ 2 ^ D % m' = 1 % m' := by
  cases hf : (List.range (m' + 1)).find? (fun D => decide (0 < D ∧ D ≤ m' ∧ 2 ^ D % m' = 1 % m')) with
  | some D =>
    have hD := List.find?_some hf
    simp only [decide_eq_true_eq] at hD
    exact ⟨D, hD⟩
  | none =>
    exfalso
    have hno : ¬ ∃ D, 0 < D ∧ D ≤ m' ∧ 2 ^ D % m' = 1 % m' := by
      rintro ⟨D, hD0, hDm, hDe⟩
      have hn := List.find?_eq_none.1 hf D (List.mem_range.2 (by omega))
      simp only [decide_eq_true_eq] at hn
      exact hn ⟨hD0, hDm, hDe⟩
    have hinj : ∀ a b, a < b → b ≤ m' → 2 ^ a % m' ≠ 2 ^ b % m' := by
      intro a b hab hb heq
      apply hno
      refine ⟨b - a, by omega, by omega, ?_⟩
      have hcop : Nat.Coprime m' (2 ^ a) := Nat.Coprime.pow_right _ hc
      exact mod_cancel_mul_right (x := 2 ^ (b - a)) (y := 1) hcop
        (by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega), Nat.one_mul]; exact heq.symm)
    have hnd : ((List.range (m' + 1)).map (fun i => 2 ^ i % m')).Nodup := by
      apply List.pairwise_map.2
      apply List.Pairwise.imp_of_mem _ (my_nodup_range _)
      intro a b ha hb hab
      rw [List.mem_range] at ha hb
      rcases Nat.lt_or_gt_of_ne hab with h | h
      · exact hinj a b h (by omega)
      · exact fun h' => hinj b a h (by omega) h'.symm
    have hsub : ((List.range (m' + 1)).map (fun i => 2 ^ i % m')) ⊆ List.range m' := by
      intro v hv
      rw [List.mem_map] at hv
      obtain ⟨i, _, rfl⟩ := hv
      rw [List.mem_range]; exact Nat.mod_lt _ hM
    have := my_len_le' hnd hsub
    simp at this
    omega

theorem NonWieferich.odd {q : Nat} [NonWieferich q] : q % 2 = 1 := by
  obtain ⟨d, u, hd, hu⟩ := NonWieferich.unit (q := q)
  have h1 := NonWieferich.one_lt (q := q)
  rcases d with _ | d
  · have hu0 : u = 0 := by
      rcases Nat.eq_zero_or_pos u with h | h
      · exact h
      · have : q * u ≥ 1 * 1 := Nat.mul_le_mul (by omega) h
        rw [Nat.pow_zero] at hd; omega
    rw [hu0, Nat.Coprime, Nat.gcd_zero_right] at hu; omega
  · rcases Nat.mod_two_eq_zero_or_one q with h | h
    · have e1 : (2 ^ (d + 1)) % 2 = 0 := by rw [Nat.pow_succ]; omega
      rw [hd, Nat.add_mod, Nat.mul_mod, h] at e1; omega
    · exact h

theorem NonWieferich.three_le {q : Nat} [NonWieferich q] : 3 ≤ q := by
  have := NonWieferich.odd (q := q); have := NonWieferich.one_lt (q := q); omega

theorem NonWieferich.gen {q : Nat} [NonWieferich q] : ∃ d u, 0 < d ∧ 2 ^ d = 1 + q * u ∧ Nat.Coprime q u := by
  obtain ⟨d, u, hd, hu⟩ := NonWieferich.unit (q := q)
  have hp3 := NonWieferich.three_le (q := q)
  have hodd := NonWieferich.odd (q := q)
  obtain ⟨D0, hD0, hD0p, hD0m⟩ := exists_pow2_period q (by omega) (coprime_two_of_odd hodd)
  obtain ⟨D, ⟨hD, hDm⟩, hmin⟩ := exists_least (fun D => 0 < D ∧ 2 ^ D % q = 1 % q) ⟨D0, hD0, hD0m⟩
  have hdm : 2 ^ d % q = 1 % q := by rw [hd, Nat.add_mul_mod_self_left]
  have hr : d % D = 0 := by
    match (inferInstance : Decidable (d % D = 0)) with
    | isTrue hg => exact hg
    | isFalse h =>
    exfalso
    have e := pow_mod_period hDm (d % D) (d / D)
    rw [Nat.mod_add_div] at e
    exact hmin (d % D) (Nat.mod_lt _ hD) ⟨by omega, by rw [← e]; exact hdm⟩
  have hp1 : 1 % q = 1 := Nat.mod_eq_of_lt (by omega)
  have hv : 2 ^ D = 1 + q * (2 ^ D / q) := by
    have := Nat.mod_add_div (2 ^ D) q; rw [hDm, hp1] at this; omega
  have hdD : d = D * (d / D) := by have := Nat.mod_add_div d D; omega
  obtain ⟨z, hz⟩ := binom_quadratic (q * (2 ^ D / q)) (d / D)
  have hpu : q * u = q * ((2 ^ D / q) * (d / D + q * (2 ^ D / q) * z)) := by
    have e : 2 ^ d = (2 ^ D) ^ (d / D) := by rw [← Nat.pow_mul, ← hdD]
    rw [e, hv, hz] at hd; (generalize 2 ^ D / q = W at *; rw [Nat.pow_two] at hd; nat_ring)
  have hu' := Nat.eq_of_mul_eq_mul_left (by omega) hpu
  refine ⟨D, 2 ^ D / q, hD, hv, ?_⟩
  exact Nat.Coprime.coprime_dvd_right ⟨_, hu'⟩ hu

theorem p_dvd_pow (q K : Nat) : q ∣ q ^ (K + 1) := ⟨q ^ K, by rw [Nat.pow_succ, Nat.mul_comm]⟩

section Basics
variable (q : Nat) [NonWieferich q]

theorem one_lt_powp (K : Nat) : 1 < q ^ (K + 1) :=
  Nat.one_lt_pow (Nat.succ_ne_zero K) (by have := NonWieferich.three_le (q := q); omega)

theorem powp_pos (K : Nat) : 0 < q ^ K := Nat.pow_pos (by have := NonWieferich.three_le (q := q); omega)

theorem coprime_p_two : Nat.Coprime q 2 := coprime_two_of_odd NonWieferich.odd

theorem powp_odd (n : Nat) : q ^ n % 2 = 1 := by
  rw [Nat.pow_mod, NonWieferich.odd (q := q), Nat.one_pow]

theorem one_mod_P (K : Nat) : 1 % q ^ (K + 1) = 1 := Nat.mod_eq_of_lt (one_lt_powp q K)

theorem period (K : Nat) : ∃ T, 0 < T ∧ 2 ^ T % q ^ (K + 1) = 1 % q ^ (K + 1) := by
  obtain ⟨d, u, hd0, hd, hu⟩ := NonWieferich.gen (q := q)
  refine ⟨d * q ^ K, Nat.mul_pos hd0 (powp_pos q K), ?_⟩
  rw [Nat.pow_mul, hd, one_mod_P]
  simpa [Nat.pow_one, Nat.add_comm] using (order_iff NonWieferich.odd NonWieferich.three_le (Nat.le_refl 1) hu K _).2 (Nat.dvd_refl _)

theorem two_gen (K x : Nat) (hx : x % q = 1) : ∃ s, 2 ^ s % q ^ (K + 1) = x % q ^ (K + 1) := by
  obtain ⟨d, u, _, hd, hu⟩ := NonWieferich.gen (q := q)
  obtain ⟨t, _, ht⟩ := unit_power_cover NonWieferich.odd NonWieferich.three_le (Nat.le_refl 1) hu K x (by rw [Nat.pow_one]; exact hx)
  exact ⟨d * t, by rw [Nat.pow_mul, hd]; simpa [Nat.pow_one, Nat.add_comm] using ht⟩

def InPowTwo (K a : Nat) : Prop := ∃ m, 2 ^ m % q ^ (K + 1) = a % q ^ (K + 1)

theorem inPowTwo_ratio {K a b : Nat} (ha : InPowTwo q K a) (hb : InPowTwo q K b) :
    ∃ j, (2 ^ j * a) % q ^ (K + 1) = b % q ^ (K + 1) := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  obtain ⟨T, hT0, hT⟩ := period q K
  refine ⟨n + m * (T - 1), ?_⟩
  rw [Nat.mul_mod, ← hm, ← Nat.mul_mod, ← Nat.pow_add, ← hn]
  have e : n + m * (T - 1) + m = n + T * m := by
    rw [Nat.add_assoc, Nat.mul_comm T m]
    have : m * (T - 1) + m = m * T := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega
  rw [e]; exact pow_mod_period hT n m

theorem target_inPowTwo {w i : Nat} (hw : w % q = 2 ^ i % q) (K : Nat) : InPowTwo q K w := by
  obtain ⟨T, hT0, hT⟩ := period q K
  have hTp : 2 ^ T % q = 1 := by
    rw [← Nat.mod_mod_of_dvd _ (p_dvd_pow q K), hT, one_mod_P,
      Nat.mod_eq_of_lt (by have := NonWieferich.three_le (q := q); omega)]
  have h1 : (2 ^ (i * (T - 1)) * w) % q = 1 := by
    rw [Nat.mul_mod, hw, ← Nat.mul_mod, ← Nat.pow_add,
      show i * (T - 1) + i = T * i by rw [Nat.mul_comm T i, ← Nat.mul_succ]; congr 1; omega,
      Nat.pow_mul, Nat.pow_mod, hTp, Nat.one_pow]
    exact Nat.mod_eq_of_lt (by have := NonWieferich.three_le (q := q); omega)
  obtain ⟨s, hs⟩ := two_gen q K _ h1
  refine ⟨s + i, ?_⟩
  rw [Nat.pow_add, Nat.mul_mod, hs, ← Nat.mul_mod, Nat.mul_assoc, Nat.mul_comm w, ← Nat.mul_assoc,
    ← Nat.pow_add, show i * (T - 1) + i = 0 + T * i by
      rw [Nat.zero_add, Nat.mul_comm T i, ← Nat.mul_succ]; congr 1; omega,
    Nat.mul_mod, pow_mod_period hT 0 i, ← Nat.mul_mod, Nat.pow_zero, Nat.one_mul]

end Basics

end Collatz
