import Collatz.DecompTheoremA

namespace Collatz

def Trapped (qg g x : Nat) : Prop := (∃ k, x % qg = 2 ^ k % qg) ∨ x % g = 0

theorem trapped_step (q g D x : Nat) (ha : 0 < q) (hg : 1 < g) (hga : g ∣ q)
    (hQ : 2 ^ D % (q * g) = 1 % (q * g))
    (hmin : ∀ k, 2 ^ k % q = 1 % q → D ∣ k)
    (h : Trapped (q * g) g (collatz q x)) : Trapped (q * g) g x := by
  unfold collatz at h
  by_cases hx : x % 2 = 0
  · simp only [hx, ite_true] at h
    have e : x = 2 * (x / 2) := by omega
    rcases h with ⟨k, hk⟩ | h
    · left; refine ⟨k + 1, ?_⟩
      rw [e, Nat.mul_mod, hk, ← Nat.mul_mod, Nat.pow_succ, Nat.mul_comm]
    · right; rw [e, Nat.mul_mod, h]; simp
  · simp only [hx, ite_false] at h
    rcases h with ⟨k, hk⟩ | h
    · have hka : 2 ^ k % q = 1 % q := by
        have := mod_of_dvd_mod (Nat.dvd_mul_right q g) hk
        rw [← this, Nat.add_mod, Nat.mul_mod_right]; simp
      obtain ⟨c, hc⟩ := hmin k hka
      have h1 : 2 ^ k % (q * g) = 1 % (q * g) := by
        rw [hc, Nat.pow_mul, Nat.pow_mod, hQ, ← Nat.pow_mod, Nat.one_pow]
      rw [h1] at hk
      have h2 : (q * g) ∣ q * x := by
        have h4 : (q * x + 1 - 1) % (q * g) = 0 := Nat.sub_mod_eq_zero_of_mod_eq hk
        rw [Nat.add_sub_cancel] at h4
        exact Nat.dvd_of_mod_eq_zero h4
      right
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mul_dvd_mul_left ha h2)
    · exfalso
      obtain ⟨t, ht⟩ := hga
      rw [ht, Nat.add_mod, Nat.mul_assoc, Nat.mul_mod_right] at h
      simp at h <;> omega

theorem trapped_of_iter (q g d t : Nat) (hq : 0 < q) (hg : 1 < g) (hgq : g ∣ q)
    (hQ : 2 ^ d % (q * g) = 1 % (q * g))
    (hmin : ∀ k, 2 ^ k % q = 1 % q → d ∣ k)
    (ht : Trapped (q * g) g t) : ∀ k x, iter (collatz q) k x = t → Trapped (q * g) g x := by
  intro k
  induction k with
  | zero => intro x h; simp [iter] at h; subst h; exact ht
  | succ k ih =>
    intro x h
    exact trapped_step q g d x hq hg hgq hQ hmin (ih _ h)

theorem order_dvd {n d k : Nat} (hd : IsOrder2 n d) (hk : 2 ^ k % n = 1 % n) : d ∣ k := by
  obtain ⟨hd0, hdm, hmin⟩ := hd
  have h := pow_mod_period hdm (k % d) (k / d)
  rw [Nat.mod_add_div] at h
  rcases Nat.eq_zero_or_pos (k % d) with h0 | h0
  · exact Nat.dvd_of_mod_eq_zero h0
  · exact absurd (h.symm.trans hk) (hmin _ h0 (Nat.mod_lt _ hd0))

theorem theorem_B (q g d t : Nat) (hq : 1 < q) (hg : 1 < g) (hgq : g ∣ q)
    (hd : IsOrder2 q d) (hdg : IsOrder2 (q * g) d) (ht : Trapped (q * g) g t) :
    ∀ x, Reaches q x t → Trapped (q * g) g x := by
  intro x hx
  obtain ⟨k, hk⟩ := hx
  exact trapped_of_iter q g d t (Nat.lt_trans Nat.zero_lt_one hq) hg hgq hdg.2.1
    (fun k' hk' => order_dvd hd hk') ht k x hk

theorem two_pow_mul_unique {a b x y : Nat} (hx : x % 2 = 1) (hy : y % 2 = 1)
    (h : 2 ^ a * x = 2 ^ b * y) : a = b ∧ x = y := by
  have key : ∀ a b x y : Nat, x % 2 = 1 → 2 ^ a * x = 2 ^ (a + b + 1) * y → False := by
    intro a b x y hx h
    have h1 : 2 ^ (a + b + 1) * y = 2 ^ a * (2 ^ (b + 1) * y) := by
      rw [Nat.add_assoc, Nat.pow_add, Nat.mul_assoc]
    rw [h1] at h
    have h2 : x = 2 ^ (b + 1) * y := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a) h
    have h3 : x = 2 * (2 ^ b * y) := by
      rw [h2, Nat.pow_succ, Nat.mul_comm (2 ^ b) 2, Nat.mul_assoc]
    rw [h3, Nat.mul_mod_right] at hx
    exact absurd hx (by decide)
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · obtain ⟨c, hc⟩ : ∃ c, b = a + c + 1 := ⟨b - a - 1, by omega⟩
    subst hc
    exact (key a c x y hx h).elim
  · subst hab
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a) h⟩
  · obtain ⟨c, hc⟩ : ∃ c, a = b + c + 1 := ⟨a - b - 1, by omega⟩
    subst hc
    exact (key b c y x hy h.symm).elim

theorem odd_of_dvd_pow {q a k : Nat} (hq : q % 2 = 1) (h : a ∣ q ^ k) : a % 2 = 1 := by
  have hqk : q ^ k % 2 = 1 := by rw [Nat.pow_mod, hq, Nat.one_pow]
  rcases Nat.mod_two_eq_zero_or_one a with h0 | h0
  · have h2 : 2 ∣ a := Nat.dvd_of_mod_eq_zero h0
    have h3 : 2 ∣ q ^ k := Nat.dvd_trans h2 h
    have h4 := Nat.mod_eq_zero_of_dvd h3
    rw [hqk] at h4
    exact absurd h4 (by decide)
  · exact h0

theorem smooth_part_unique {q a a' b b' k k' : Nat} (hq : 0 < q) (ha : a ∣ q ^ k)
    (ha' : a' ∣ q ^ k') (hb : Nat.Coprime b q) (hb' : Nat.Coprime b' q)
    (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have hapos : 0 < a := Nat.pos_of_dvd_of_pos ha (Nat.pow_pos hq)
  have hcop1 : Nat.Coprime a b' :=
    (Nat.Coprime.coprime_dvd_right ha (Nat.Coprime.pow_right k hb')).symm
  have hcop2 : Nat.Coprime a' b :=
    (Nat.Coprime.coprime_dvd_right ha' (Nat.Coprime.pow_right k' hb)).symm
  have hd1 : a ∣ a' := Nat.Coprime.dvd_of_dvd_mul_right hcop1 (h ▸ Nat.dvd_mul_right a b)
  have hd2 : a' ∣ a := Nat.Coprime.dvd_of_dvd_mul_right hcop2 (h.symm ▸ Nat.dvd_mul_right a' b')
  have hEq : a = a' := Nat.dvd_antisymm hd1 hd2
  subst hEq
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hapos h⟩

theorem order2_unique {n d d' : Nat} (h : IsOrder2 n d) (h' : IsOrder2 n d') : d = d' := by
  rcases Nat.lt_trichotomy d d' with hlt | heq | hgt
  · exact absurd h.2.1 (h'.2.2 d h.1 hlt)
  · exact heq
  · exact absurd h'.2.1 (h.2.2 d' h'.1 hgt)

theorem covering_length_unique {q m' γ γ' : Nat} (h : Covers q m' γ)
    (hmin : ∀ j, j < γ → ¬ Covers q m' j) (h' : Covers q m' γ')
    (hmin' : ∀ j, j < γ' → ¬ Covers q m' j) : γ = γ' := by
  rcases Nat.lt_trichotomy γ γ' with hlt | heq | hgt
  · exact absurd h (hmin' γ hlt)
  · exact heq
  · exact absurd h' (hmin γ' hgt)

theorem decomp_unique {q m α mq m' β d e eQ e' K α2 mq2 mp2 β2 d2 e2 eQ2 ep2 K2 : Nat}
    (hq : OddNonWieferich q) (hD : Decomp q m α mq m' β d e eQ e' K)
    (hD2 : Decomp q m α2 mq2 mp2 β2 d2 e2 eQ2 ep2 K2) :
    α = α2 ∧ mq = mq2 ∧ m' = mp2 ∧ β = β2 ∧ d = d2 ∧ e = e2 ∧ eQ = eQ2 ∧ e' = ep2 ∧ K = K2 := by
  obtain ⟨hq1, hodd, -⟩ := hq
  have hq0 : 0 < q := Nat.lt_trans Nat.zero_lt_one hq1
  obtain ⟨hm, hM, -, hA, hAmin, hdo, heo, hee, -, he'q, hKe, hKmin⟩ := hD
  obtain ⟨hm2, hM2, -, hA2, hAmin2, hdo2, heo2, hee2, -, he'q2, hKe2, hKmin2⟩ := hD2
  have hmq : mq % 2 = 1 := odd_of_dvd_pow hodd hA
  have hmq2 : mq2 % 2 = 1 := odd_of_dvd_pow hodd hA2
  have hm'2 : m' % 2 = 1 := odd_of_coprime_two (coprime_two_of_coprime_two_mul hM)
  have hmp2 : mp2 % 2 = 1 := odd_of_coprime_two (coprime_two_of_coprime_two_mul hM2)
  have hx : (mq * m') % 2 = 1 := by rw [Nat.mul_mod, hmq, hm'2]
  have hy : (mq2 * mp2) % 2 = 1 := by rw [Nat.mul_mod, hmq2, hmp2]
  have e1 : 2 ^ α * (mq * m') = 2 ^ α2 * (mq2 * mp2) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← hm, ← hm2]
  obtain ⟨hα, hprod⟩ := two_pow_mul_unique hx hy e1
  obtain ⟨hmqe, hm'e⟩ := smooth_part_unique hq0 hA hA2 (coprime_p_of_coprime_two_mul hM)
    (coprime_p_of_coprime_two_mul hM2) hprod
  subst hmqe
  subst hm'e
  have hβ : β = β2 := Nat.le_antisymm (hAmin β2 hA2) (hAmin2 β hA)
  have hd : d = d2 := order2_unique hdo hdo2
  have he : e = e2 := order2_unique heo heo2
  have hee3 : eQ * e' = eQ2 * ep2 := hee.symm.trans (he.trans hee2)
  obtain ⟨heQ, hep⟩ := smooth_part_unique hq0 hKe hKe2 he'q he'q2 hee3
  subst heQ
  subst hep
  have hK : K = K2 := Nat.le_antisymm (hKmin K2 hKe2) (hKmin2 K hKe)
  exact ⟨hα, rfl, rfl, hβ, hd, he, rfl, rfl, hK⟩

theorem params_unique {q m α mq m' β d e eQ e' K γ α2 mq2 mp2 β2 d2 e2 eQ2 ep2 K2 γ2 : Nat}
    (hq : OddNonWieferich q) (hD : Decomp q m α mq m' β d e eQ e' K) (hγ : Covers q m' γ)
    (hmin : ∀ j, j < γ → ¬ Covers q m' j)
    (hD2 : Decomp q m α2 mq2 mp2 β2 d2 e2 eQ2 ep2 K2) (hγ2 : Covers q mp2 γ2)
    (hmin2 : ∀ j, j < γ2 → ¬ Covers q mp2 j) :
    α = α2 ∧ mq = mq2 ∧ m' = mp2 ∧ β = β2 ∧ d = d2 ∧ e = e2 ∧ eQ = eQ2 ∧ e' = ep2 ∧ K = K2 ∧
      γ = γ2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := decomp_unique hq hD hD2
  subst h3
  exact ⟨h1, h2, rfl, h4, h5, h6, h7, h8, h9, covering_length_unique hγ hmin hγ2 hmin2⟩


end Collatz
