import Collatz.Steer

namespace Collatz

theorem fixed_point_int (q K : Nat) (hq3 : 3 ≤ q) (hp : Nat.Coprime q 2) :
    ∃ c : Nat, (q : Int) ^ (K + 1) ∣ (2 - (q : Int)) * (c : Int) - 1 := by
  have hpP : q ≤ q ^ (K + 1) := by
    have := Nat.pow_le_pow_right (show 0 < q by omega) (show 1 ≤ K + 1 by omega)
    simpa using this
  obtain ⟨n, hn⟩ : ∃ n, n = q ^ (K + 1) + 2 - q := ⟨_, rfl⟩
  have hnp : n + q = q ^ (K + 1) + 2 := by omega
  have hgp : Nat.Coprime q n := by
    have h1 : Nat.gcd q n ∣ 2 := by
      have d1 : Nat.gcd q n ∣ q := Nat.gcd_dvd_left q n
      have d2 : Nat.gcd q n ∣ n := Nat.gcd_dvd_right q n
      have d3 : Nat.gcd q n ∣ q ^ (K + 1) :=
        Nat.dvd_trans d1 (by simpa using Nat.pow_dvd_pow q (show 1 ≤ K + 1 by omega))
      have d4 : Nat.gcd q n ∣ q ^ (K + 1) + 2 := by
        rw [← hnp]; exact Nat.dvd_add d2 d1
      exact (Nat.dvd_add_right d3).1 d4
    have h2 : Nat.gcd (Nat.gcd q n) 2 = 1 := Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left q n) hp
    rw [Nat.gcd_eq_left h1] at h2
    exact h2
  have hm1 : 1 < q ^ (K + 1) := Nat.lt_of_lt_of_le (by omega) hpP
  obtain ⟨k, w, hkw⟩ := nat_bez n (q ^ (K + 1)) hm1 (Nat.Coprime.symm (Nat.Coprime.pow_left (K + 1) hgp))
  refine ⟨k, w - k, ?_⟩
  have hn' : (n : Int) + (q : Int) = (q : Int) ^ (K + 1) + 2 := by exact_mod_cast hnp
  have hkw' : (n : Int) * (k : Int) = (q : Int) ^ (K + 1) * (w : Int) + 1 := by exact_mod_cast hkw
  have h2q : (2 : Int) - (q : Int) = (n : Int) - (q : Int) ^ (K + 1) := by omega
  rw [h2q, Int.sub_mul, Int.mul_sub]
  omega

theorem exists_nu (q : Nat) [NonWieferich q] (K d u : Nat) (hd : 2 ^ d = 1 + q * u)
    (hu : Nat.Coprime q u) (t i : Nat) (hi : t % q = 2 ^ i % q) (c : Nat)
    (hc : (q : Int) ^ (K + 1) ∣ (2 - (q : Int)) * (c : Int) - 1) :
    ∃ ν : Nat, ν < d * q ^ K ∧ (q : Int) ^ (K + 1) ∣ (2 : Int) ^ ν * (t : Int) - (c : Int) := by
  have hodd := NonWieferich.odd (q := q)
  have hq3 := NonWieferich.three_le (q := q)
  have hP1 : 1 % q ^ (K + 1) = 1 := one_mod_P q K
  have hqpos : 0 < q := by omega
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; rw [Nat.pow_zero] at hd
      have : q * u = 0 := by omega
      rcases Nat.mul_eq_zero.1 this with h1 | h1
      · omega
      · subst h1; simp [Nat.Coprime] at hu; omega
    · exact h
  have hcq : (2 * c) % q = 1 := by
    have hdvd : (q : Int) ∣ (2 - (q : Int)) * (c : Int) - 1 :=
      Int.dvd_trans ⟨(q : Int) ^ K, by rw [Int.pow_succ, Int.mul_comm]⟩ hc
    obtain ⟨g, hg⟩ := hdvd
    have e0 : (2 - (q : Int)) * (c : Int) - 1 = 2 * (c : Int) - 1 - (q : Int) * (c : Int) := by int_ring
    rw [e0] at hg
    have h1 : (((2 * c : Nat)) : Int) = 1 + (q : Int) * ((c : Int) + g) := by
      simp only [Int.natCast_mul]
      show (2 : Int) * (c : Int) = _
      rw [Int.mul_add]; omega
    have h2 := Int.natCast_emod (2 * c) q
    have h3 : (((2 * c : Nat)) : Int) % (q : Int) = 1 := by
      rw [h1, Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt (by omega) (by omega)
    omega
  have hcpow : c % q = 2 ^ (d - 1) % q := by
    have e2 : 2 ^ d % q = 1 := by
      rw [hd, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)
    have e3 : c * 2 ^ d = (2 * c) * 2 ^ (d - 1) := by
      rw [show d = (d - 1) + 1 by omega, Nat.pow_succ]
      simp only [Nat.add_sub_cancel]; nat_ring
    have := congrArg (· % q) e3
    rw [Nat.mul_mod, e2, Nat.mul_one, Nat.mod_mod, Nat.mul_mod (2 * c), hcq, Nat.one_mul,
      Nat.mod_mod] at this
    exact this
  have hMt := target_inPowTwo q hi K
  have hMc := target_inPowTwo q hcpow K
  obtain ⟨j, hj⟩ := inPowTwo_ratio q hMt hMc
  have hT : 2 ^ (d * q ^ K) % q ^ (K + 1) = 1 % q ^ (K + 1) := by
    rw [Nat.pow_mul, hd, hP1]
    simpa [Nat.pow_one, Nat.add_comm] using (order_iff hodd hq3 (Nat.le_refl 1) hu K (q ^ K)).2 (Nat.dvd_refl _)
  have hTpos : 0 < d * q ^ K := Nat.mul_pos hd0 (powp_pos q K)
  refine ⟨j % (d * q ^ K), Nat.mod_lt _ hTpos, ?_⟩
  have hν : 2 ^ (j % (d * q ^ K)) % q ^ (K + 1) = 2 ^ j % q ^ (K + 1) :=
    pow_two_mod_period (q ^ (K + 1)) (d * q ^ K) hT _ _ (by rw [Nat.mod_mod])
  have hfin : (2 ^ (j % (d * q ^ K)) * t) % q ^ (K + 1) = c % q ^ (K + 1) := by
    rw [mul_mod_cong _ _ _ _ hν]; exact hj
  have h := nat_mod_to_int_dvd _ _ _ hfin
  simp only [Int.natCast_pow, Int.natCast_mul] at h
  exact h

theorem P_struct (q : Nat) [NonWieferich q] (K d u e eQ e' : Nat) (hd : 2 ^ d = 1 + q * u)
    (hu : Nat.Coprime q u) (he0 : 0 < e) (hee : e = eQ * e') (hKe : eQ ∣ q ^ K)
    (he'q : Nat.Coprime e' q) :
    ∃ uP : Nat, 2 ^ (Nat.lcm (d * q ^ K) e) = 1 + q ^ (K + 1) * uP ∧ Nat.Coprime q uP := by
  have hodd := NonWieferich.odd (q := q)
  obtain ⟨uK, huK, hexp⟩ := lift_exponent hodd (Nat.le_refl 1) hu K
  have h2a : 2 ^ (d * q ^ K) = 1 + q ^ (K + 1) * uK := by
    rw [Nat.pow_mul, hd]; simpa [Nat.pow_one, Nat.add_comm] using hexp
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd (d * q ^ K) e := ⟨_, rfl⟩
  have hge : g ∣ e := by rw [hg]; exact Nat.gcd_dvd_right _ _
  obtain ⟨f, hf⟩ : ∃ f, f = e / g := ⟨_, rfl⟩
  have hlcm : Nat.lcm (d * q ^ K) e = d * q ^ K * f := by
    show d * q ^ K * e / Nat.gcd (d * q ^ K) e = _
    rw [← hg, hf]; exact Nat.mul_div_assoc _ hge
  have hegf : e = g * f := by rw [hf]; exact (Nat.mul_div_cancel' hge).symm
  have heQa : eQ ∣ d * q ^ K := Nat.dvd_trans hKe (Nat.dvd_mul_left _ _)
  have heQe : eQ ∣ e := ⟨e', hee⟩
  have heQg : eQ ∣ g := by rw [hg]; exact Nat.dvd_gcd heQa heQe
  obtain ⟨g', hg'⟩ := heQg
  have heQ0 : 0 < eQ := by
    rcases Nat.eq_zero_or_pos eQ with h | h
    · rw [h, Nat.zero_mul] at hee; omega
    · exact h
  have he' : e' = f * g' := by
    have h1 : eQ * e' = eQ * (g' * f) := by
      rw [← hee, hegf, hg']; (first | nat_ring | int_ring)
    rw [Nat.eq_of_mul_eq_mul_left heQ0 h1, Nat.mul_comm]
  have hfq : Nat.Coprime f q := Nat.Coprime.coprime_dvd_left ⟨g', he'⟩ he'q
  obtain ⟨z, hz⟩ := binom_quadratic (q ^ (K + 1) * uK) f
  refine ⟨f * uK + q * (q ^ K * (uK ^ 2 * z)), ?_, ?_⟩
  · rw [hlcm, Nat.pow_mul, h2a, hz]
    have e1 : q ^ (K + 1) = q * q ^ K := by rw [Nat.pow_succ, Nat.mul_comm]
    simp only [Nat.pow_two]
    generalize q ^ K = A at e1 ⊢
    rw [e1]; (first | nat_ring | int_ring)
  · rw [Nat.Coprime, Nat.gcd_add_mul_left_right]
    exact Nat.Coprime.mul_right hfq.symm huK

theorem ipow2_ge_one (k : Nat) : (1 : Int) ≤ (2 : Int) ^ k := by
  induction k with
  | zero => rw [Int.pow_zero]; exact Int.le_refl _
  | succ k ih => rw [Int.pow_succ]; omega

theorem chain_pos (q : Nat) (hq : 1 ≤ q) (P : Nat) (y0 : Int) (b J : Nat → Nat) (n : Nat)
    (hI : Integral (q : Int) P y0 b J n) (hy0 : 1 ≤ y0) (hb : ∀ l, 1 ≤ l → l ≤ n → 1 ≤ b l) :
    ∀ i, i ≤ n → 1 ≤ chain (q : Int) P y0 b J i := by
  intro i
  induction i with
  | zero => intro _; exact hy0
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    have rel := chain_rel hI i (by omega)
    have hb1 := hb (i + 1) (by omega) hi
    obtain ⟨b', hb'⟩ : ∃ b', b (i + 1) = b' + 1 := ⟨b (i + 1) - 1, by omega⟩
    have h2b : (2 : Int) ≤ (2 : Int) ^ (b (i + 1)) := by
      rw [hb', Int.pow_succ]; have := ipow2_ge_one b'; omega
    have hJP := ipow2_ge_one (J (i + 1) * P)
    generalize (2 : Int) ^ (b (i + 1)) = A at *
    generalize (2 : Int) ^ (J (i + 1) * P) = B at *
    generalize chain (q : Int) P y0 b J i = y at *
    generalize chain (q : Int) P y0 b J (i + 1) = c1 at *
    have hAB : A ≤ A * B := by
      have := Int.mul_le_mul_of_nonneg_left hJP (show 0 ≤ A by omega)
      rw [Int.mul_one] at this; exact this
    have hABy : A * B ≤ A * B * y := by
      have := Int.mul_le_mul_of_nonneg_left ih' (show 0 ≤ A * B by omega)
      rw [Int.mul_one] at this; exact this
    have hq' : (0 : Int) ≤ (q : Int) := by omega
    match Int.lt_or_le c1 1 with
    | Or.inr hle => exact (by omega : 1 ≤ c1)
    | Or.inl hc =>
    have hc' : c1 ≤ 0 := by omega
    have := Int.mul_le_mul_of_nonneg_left hc' hq'
    rw [Int.mul_zero] at this
    omega

theorem chain_size (q : Nat) (hq : 1 ≤ q) (P : Nat) (y0 : Int) (b J : Nat → Nat) (n : Nat)
    (hI : Integral (q : Int) P y0 b J n) (hy0 : 1 ≤ y0) (hb : ∀ l, 1 ≤ l → l ≤ n → 1 ≤ b l) :
    ∀ i, i ≤ n → chain (q : Int) P y0 b J i ≤ (2 : Int) ^ (asum (fun l => b l + J l * P) i) * y0 := by
  intro i
  induction i with
  | zero => intro _; show y0 ≤ (2 : Int) ^ 0 * y0; rw [Int.pow_zero, Int.one_mul]; exact Int.le_refl _
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    have rel := chain_rel hI i (by omega)
    have hAs : (2 : Int) ^ (asum (fun l => b l + J l * P) (i + 1))
        = (2 : Int) ^ (asum (fun l => b l + J l * P) i) * ((2 : Int) ^ (b (i + 1)) * (2 : Int) ^ (J (i + 1) * P)) := by
      show (2 : Int) ^ (asum (fun l => b l + J l * P) i + (b (i + 1) + J (i + 1) * P)) = _
      rw [Int.pow_add, Int.pow_add]
    rw [hAs]
    have hA1 := ipow2_ge_one (b (i + 1))
    have hB1 := ipow2_ge_one (J (i + 1) * P)
    have hC1 := ipow2_ge_one (asum (fun l => b l + J l * P) i)
    have hc1pos := chain_pos q hq P y0 b J n hI hy0 hb (i + 1) hi
    generalize (2 : Int) ^ (b (i + 1)) = A at *
    generalize (2 : Int) ^ (J (i + 1) * P) = B at *
    generalize (2 : Int) ^ (asum (fun l => b l + J l * P) i) = C at *
    generalize chain (q : Int) P y0 b J i = y at *
    generalize chain (q : Int) P y0 b J (i + 1) = c1 at *
    have hq' : (0 : Int) ≤ (q : Int) := by omega
    have h1 : c1 ≤ (q : Int) * c1 := by
      have := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ (q : Int) by omega)
        (show 0 ≤ c1 by omega)
      rw [Int.one_mul] at this; exact this
    have hAB : 0 ≤ A * B := Int.mul_nonneg (by omega) (by omega)
    have h2 : A * B * y ≤ A * B * (C * y0) := Int.mul_le_mul_of_nonneg_left ih' hAB
    have e : A * B * (C * y0) = C * (A * B) * y0 := by int_ring
    rw [← e]
    omega

theorem chain_reaches (q : Nat) [NonWieferich q] (P : Nat) (y0 : Int) (b J : Nat → Nat) (n : Nat)
    (hI : Integral (q : Int) P y0 b J n) (hy0 : 1 ≤ y0) (hb : ∀ l, 1 ≤ l → l ≤ n → 1 ≤ b l)
    (Y0 : Nat) (hY0 : (Y0 : Int) = y0) :
    ∀ i, i ≤ n → ∃ yi : Nat, (yi : Int) = chain (q : Int) P y0 b J i ∧ Reaches q yi Y0 := by
  have hq1 : 1 ≤ q := by have := NonWieferich.three_le (q := q); omega
  intro i
  induction i with
  | zero => intro _; exact ⟨Y0, hY0, ⟨0, rfl⟩⟩
  | succ i ih =>
    intro hi
    obtain ⟨yi, hyi, hr⟩ := ih (by omega)
    have rel := chain_rel hI i (by omega)
    have hpos := chain_pos q hq1 P y0 b J n hI hy0 hb (i + 1) hi
    obtain ⟨yN, hyN⟩ : ∃ y : Nat, (y : Int) = chain (q : Int) P y0 b J (i + 1) :=
      ⟨(chain (q : Int) P y0 b J (i + 1)).toNat, Int.toNat_of_nonneg (by omega)⟩
    refine ⟨yN, hyN, ?_⟩
    have hb1 := hb (i + 1) (by omega) hi
    have hnat : q * yN + 1 = 2 ^ (b (i + 1) + J (i + 1) * P) * yi := by
      apply Int.ofNat_inj.1
      simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow, Int.natCast_one]
      rw [hyN, hyi, Int.pow_add]
      show (q : Int) * chain (q : Int) P y0 b J (i + 1) + 1 = _
      exact rel
    exact reaches_trans q (backstep_reaches (q := q) yN yi _ (by omega) hnat) hr

theorem asum_bound (f : Nat → Nat) (X : Nat) :
    ∀ n, (∀ l, 1 ≤ l → l ≤ n → f l ≤ X) → asum f (n + 1) ≤ n * X + f (n + 1)
  | 0, _ => by show asum f 0 + f (0 + 1) ≤ 0 * X + f (0 + 1); simp [asum]
  | n + 1, H => by
    have ih := asum_bound f X n (fun l h1 h2 => H l h1 (by omega))
    have hn := H (n + 1) (by omega) (Nat.le_refl _)
    show asum f (n + 1) + f (n + 1 + 1) ≤ (n + 1) * X + f (n + 1 + 1)
    rw [Nat.succ_mul]; omega

theorem setup_of (q K P uPn : Nat) [NonWieferich q] (c y0 : Int) (b : Nat → Nat)
    (hP : (2 : Int) ^ P = 1 + (q : Int) ^ (K + 1) * (uPn : Int))
    (huP : Nat.Coprime q uPn)
    (hc : (q : Int) ^ (K + 1) ∣ (2 - (q : Int)) * c - 1)
    (hy0 : (q : Int) ^ (K + 1) ∣ y0 - c)
    (hb1 : ∀ i, 1 ≤ i → i ≤ K + 1 → b i = 1) :
    Setup (q : Int) K P (uPn : Int) b y0 c := by
  have hq3 := NonWieferich.three_le (q := q)
  have hodd := NonWieferich.odd (q := q)
  have hp0 : (q : Int) ≠ 0 := by omega
  refine ⟨hp0, hP, ?_, ?_, hc, hy0, hb1⟩
  · refine ⟨((q + 1) / 2 : Nat), ⟨1, ?_⟩⟩
    have h2 : 2 * ((q + 1) / 2) = q + 1 := by omega
    have h3 : (2 : Int) * (((q + 1) / 2 : Nat) : Int) = (q : Int) + 1 := by
      have := congrArg (fun n : Nat => (n : Int)) h2
      simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one] at this
      exact this
    omega
  · obtain ⟨k, w, hkw⟩ := nat_bez uPn q (by omega) (Nat.Coprime.symm huP)
    refine ⟨(k : Int), ⟨(w : Int), ?_⟩⟩
    have h4 : (uPn : Int) * (k : Int) = (q : Int) * (w : Int) + 1 := by
      have := congrArg (fun n : Nat => (n : Int)) hkw
      simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one] at this
      exact this
    omega

theorem step_lower (q : Nat) [NonWieferich q] (P : Nat) (y0 : Int) (b J : Nat → Nat) (n : Nat)
    (hI : Integral (q : Int) P y0 b J n) (hy0 : 1 ≤ y0) (hb : ∀ l, 1 ≤ l → l ≤ n → 1 ≤ b l)
    (i : Nat) (hi : i < n) :
    (2 : Int) ^ (b (i + 1) + J (i + 1) * P) ≤ (q : Int) * chain (q : Int) P y0 b J (i + 1) + 1 := by
  have rel := chain_rel hI i hi
  have hprev := chain_pos q (by have := NonWieferich.three_le (q := q); omega) P y0 b J n hI hy0 hb i (by omega)
  have e : (2 : Int) ^ (b (i + 1) + J (i + 1) * P)
      = (2 : Int) ^ (b (i + 1)) * (2 : Int) ^ (J (i + 1) * P) := Int.pow_add _ _ _
  rw [e]
  have hA : (0 : Int) ≤ (2 : Int) ^ (b (i + 1)) * (2 : Int) ^ (J (i + 1) * P) := by
    have := ipow2_ge_one (b (i + 1)); have := ipow2_ge_one (J (i + 1) * P)
    exact Int.mul_nonneg (by omega) (by omega)
  have hmul : (2 : Int) ^ (b (i + 1)) * (2 : Int) ^ (J (i + 1) * P) ≤
      (2 : Int) ^ (b (i + 1)) * (2 : Int) ^ (J (i + 1) * P) * chain (q : Int) P y0 b J i := by
    have := Int.mul_le_mul_of_nonneg_left hprev hA
    rw [Int.mul_one] at this; exact this
  have hq : (0 : Int) ≤ (q : Int) := by omega
  omega

theorem ipow2_mono (a c : Nat) (h : a ≤ c) : (2 : Int) ^ a ≤ (2 : Int) ^ c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Int.pow_add]
  have h1 := ipow2_ge_one d
  have hA : (0 : Int) ≤ (2 : Int) ^ a := by have := ipow2_ge_one a; omega
  have := Int.mul_le_mul_of_nonneg_left h1 hA
  rw [Int.mul_one] at this
  exact this

theorem amin_exists (X : Nat) (hX : 1 ≤ X) : ∃ a : Nat, X < 2 ^ a ∧ 2 ^ a ≤ 2 * X := by
  refine ⟨Nat.log2 X + 1, Nat.lt_log2_self, ?_⟩
  have hX0 : X ≠ 0 := by omega
  have hlt : ¬ (X < 2 ^ Nat.log2 X) := by
    intro h
    have := (Nat.log2_lt hX0).2 h
    omega
  have hle : 2 ^ Nat.log2 X ≤ X := Nat.le_of_not_lt hlt
  rw [Nat.pow_succ]
  omega

theorem size_bound (q : Nat) [NonWieferich q] (P ν t s qP M D : Nat) (b J : Nat → Nat)
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hν : ν ≤ D)
    (hI : Integral (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J s)
    (hb : ∀ l, 1 ≤ l → l ≤ s → 1 ≤ b l)
    (hsmall : ∀ l, 1 ≤ l → l + 1 ≤ s → b l + J l * P ≤ qP)
    (hlast : b s + J s * P ≤ M) :
    chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J s
      ≤ (2 : Int) ^ (D + (s - 1) * qP + M) * (t : Int) := by
  have hq1 : 1 ≤ q := by have := NonWieferich.three_le (q := q); omega
  have hy0 : 1 ≤ (2 : Int) ^ ν * (t : Int) := by
    have h1 := ipow2_ge_one ν
    have := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ (t : Int) by omega)
      (show (0 : Int) ≤ (2 : Int) ^ ν by omega)
    rw [Int.mul_one] at this; omega
  have hc := chain_size q hq1 P ((2 : Int) ^ ν * (t : Int)) b J s hI hy0 hb s (Nat.le_refl s)
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hab := asum_bound (fun l => b l + J l * P) qP s' (fun l h1 h2 => hsmall l h1 (by omega))
  have hs' : s' + 1 - 1 = s' := by omega
  have hA : (2 : Int) ^ (asum (fun l => b l + J l * P) (s' + 1))
      ≤ (2 : Int) ^ (s' * qP + M) := ipow2_mono _ _ (by omega)
  have hB : (2 : Int) ^ ν ≤ (2 : Int) ^ D := ipow2_mono _ _ hν
  have hfin : chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J (s' + 1)
      ≤ (2 : Int) ^ (s' * qP + M) * ((2 : Int) ^ ν * (t : Int)) := by
    have hnn : (0 : Int) ≤ (2 : Int) ^ ν * (t : Int) :=
      Int.mul_nonneg (by have := ipow2_ge_one ν; omega) (by omega)
    have h := Int.mul_le_mul_of_nonneg_right hA hnn
    exact Int.le_trans hc h
  have hfin2 : (2 : Int) ^ (s' * qP + M) * ((2 : Int) ^ ν * (t : Int))
      ≤ (2 : Int) ^ (D + (s' + 1 - 1) * qP + M) * (t : Int) := by
    rw [hs']
    have eD : (2 : Int) ^ (D + s' * qP + M) = (2 : Int) ^ (s' * qP + M) * (2 : Int) ^ D := by
      rw [show D + s' * qP + M = (s' * qP + M) + D by omega, Int.pow_add]
    rw [eD]
    have e1 : (2 : Int) ^ (s' * qP + M) * (2 : Int) ^ ν * (t : Int)
        ≤ (2 : Int) ^ (s' * qP + M) * (2 : Int) ^ D * (t : Int) := by
      have hpos : (0 : Int) ≤ (2 : Int) ^ (s' * qP + M) := by
        have := ipow2_ge_one (s' * qP + M); omega
      have := Int.mul_le_mul_of_nonneg_left hB hpos
      have htn : (0 : Int) ≤ (t : Int) := by omega
      have h3 := Int.mul_le_mul_of_nonneg_right this htn
      exact h3
    have e2 : (2 : Int) ^ (s' * qP + M) * ((2 : Int) ^ ν * (t : Int))
        = (2 : Int) ^ (s' * qP + M) * (2 : Int) ^ ν * (t : Int) := by int_ring
    rw [e2]; exact e1
  exact Int.le_trans hfin hfin2

theorem chain_rel_mod (m : Int) (q : Nat) (P : Nat) (y0 : Int) (b J : Nat → Nat) (n : Nat)
    (hI : Integral (q : Int) P y0 b J n) (hP : m ∣ (2 : Int) ^ P - 1) :
    ∀ i, i < n → m ∣ (q : Int) * chain (q : Int) P y0 b J (i + 1) + 1
      - (2 : Int) ^ (b (i + 1)) * chain (q : Int) P y0 b J i := by
  intro i hi
  have rel := chain_rel hI i hi
  have hJ := pow_mod_one_int m P (J (i + 1)) hP
  obtain ⟨g, hg⟩ := hJ
  refine ⟨(2 : Int) ^ (b (i + 1)) * chain (q : Int) P y0 b J i * g, ?_⟩
  have hJ' : (2 : Int) ^ (J (i + 1) * P) = 1 + m * g := by omega
  have key : (q : Int) * chain (q : Int) P y0 b J (i + 1) + 1
      - (2 : Int) ^ (b (i + 1)) * chain (q : Int) P y0 b J i
      = (2 : Int) ^ (b (i + 1)) * chain (q : Int) P y0 b J i * (2 ^ (J (i + 1) * P) - 1) := by
    rw [rel]; int_ring
  rw [key, hJ']
  int_ring

theorem two_mul_succ_mul (a b : Nat) : 2 * (a + 1) * b = 2 * (a * b) + 2 * b := by
  rw [Nat.mul_assoc, Nat.add_mul, Nat.one_mul, Nat.mul_add]

theorem kappa_le (q : Nat) (hq : 3 ≤ q) : ∀ u : List Nat, (∀ e ∈ u, e ≤ 1) →
    kappa q u + q ^ ones u ≤ 2 ^ u.length * q ^ ones u
  | [], _ => by simp [kappa, ones]
  | e :: u, hu => by
    have ih := kappa_le q hq u (fun d hd => hu d (by simp [hd]))
    have he : e = 0 ∨ e = 1 := by
      have := hu e (by simp); omega
    simp only [kappa, ones, List.length_cons]
    have hT : 1 ≤ 2 ^ u.length := Nat.one_le_two_pow
    rcases he with rfl | rfl
    · rw [show (2 : Nat) ^ (u.length + 1) = 2 * 2 ^ u.length from Nat.pow_succ']
      obtain ⟨t1, ht1⟩ : ∃ t1, 2 ^ u.length = t1 + 1 := ⟨2 ^ u.length - 1, by omega⟩
      rw [ht1] at ih ⊢
      try simp only [Nat.add_zero]
      rw [two_mul_succ_mul, Nat.mul_zero, Nat.zero_add]
      have e2 : (t1 + 1) * q ^ ones u = t1 * q ^ ones u + q ^ ones u := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [e2] at ih
      omega
    · rw [show q ^ (ones u + 1) = q * q ^ ones u from Nat.pow_succ',
        show (2 : Nat) ^ (u.length + 1) = 2 * 2 ^ u.length from Nat.pow_succ']
      obtain ⟨t1, ht1⟩ : ∃ t1, 2 ^ u.length = t1 + 1 := ⟨2 ^ u.length - 1, by omega⟩
      rw [ht1] at ih ⊢
      have hY : q ^ ones u ≤ q * q ^ ones u := Nat.le_mul_of_pos_left _ (by omega)
      have hty : t1 * q ^ ones u ≤ t1 * (q * q ^ ones u) := Nat.mul_le_mul_left t1 hY
      have e2 : (t1 + 1) * q ^ ones u = t1 * q ^ ones u + q ^ ones u := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [e2] at ih
      rw [two_mul_succ_mul, Nat.mul_one]
      omega

theorem ones_le_length : ∀ u : List Nat, (∀ e ∈ u, e ≤ 1) → ones u ≤ u.length
  | [], _ => by simp [ones]
  | e :: u, hu => by
    have ih := ones_le_length u (fun d hd => hu d (by simp [hd]))
    have he : e ≤ 1 := hu e (by simp)
    simp only [ones, List.length_cons]
    omega

theorem theta_bound (q : Nat) (hq : 3 ≤ q) (m rb B ρ : Nat) (u : List Nat) (hu : ∀ e ∈ u, e ≤ 1)
    (hrb : rb < m)
    (hρ : 2 ^ u.length * ρ = q ^ ones u * rb + kappa q u) :
    ρ + q ^ ones u * (B + 1) ≤ q ^ u.length * ((m + 1) * (B + 1)) := by
  have hO := kappa_le q hq u hu
  have hA : 1 ≤ 2 ^ u.length := Nat.one_le_two_pow
  have hX : 1 ≤ q ^ ones u := Nat.one_le_pow _ _ (by omega)

  have hstep1 : 2 ^ u.length * ρ ≤ 2 ^ u.length * (q ^ ones u * (rb + 1)) := by
    have e1 : 2 ^ u.length * (q ^ ones u * (rb + 1))
        = 2 ^ u.length * (q ^ ones u * rb) + 2 ^ u.length * q ^ ones u := by
      simp only [Nat.mul_add, Nat.mul_one]
    have hXr : q ^ ones u * rb ≤ 2 ^ u.length * (q ^ ones u * rb) :=
      Nat.le_mul_of_pos_left _ (by omega)
    rw [e1]
    rw [hρ]
    omega
  have hrho : ρ ≤ q ^ ones u * (rb + 1) := Nat.le_of_mul_le_mul_left hstep1 (by omega)

  have hmB : rb + 1 ≤ m := hrb
  have hK : (rb + 1 + B + 1) ≤ (m + 1) * (B + 1) := by
    have e3 : (m + 1) * (B + 1) = m * B + m + B + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    rw [e3]; omega

  have hsum : ρ + q ^ ones u * (B + 1) ≤ q ^ ones u * ((m + 1) * (B + 1)) := by
    have e4 : q ^ ones u * ((m + 1) * (B + 1))
        = q ^ ones u * (rb + 1 + B + 1) + q ^ ones u * ((m + 1) * (B + 1) - (rb + 1 + B + 1)) := by
      rw [← Nat.mul_add]; congr 1; omega
    have hm1 : q ^ ones u * (rb + 1) + q ^ ones u * (B + 1)
        = q ^ ones u * (rb + 1 + B + 1) := by
      rw [← Nat.mul_add]; congr 1
    have := Nat.add_le_add hrho (Nat.le_refl (q ^ ones u * (B + 1)))
    rw [hm1] at this
    rw [e4]; omega
  have hpow : q ^ ones u ≤ q ^ u.length := Nat.pow_le_pow_right (by omega) (ones_le_length u hu)
  have hfin : q ^ ones u * ((m + 1) * (B + 1)) ≤ q ^ u.length * ((m + 1) * (B + 1)) :=
    Nat.mul_le_mul_right _ hpow
  omega

theorem class_indep_of_shifts (m q P : Nat) (hm0 : 0 < m) (hcop : Nat.Coprime m q)
    (hP : (m : Int) ∣ (2 : Int) ^ P - 1) (y0 y0' : Int) (b b' J J' : Nat → Nat) (n : Nat)
    (hI : Integral (q : Int) P y0 b J n) (hI' : Integral (q : Int) P y0' b' J' n)
    (hbb : ∀ i, 1 ≤ i → i ≤ n → b i = b' i)
    (h0 : (m : Int) ∣ y0 - y0') :
    ∀ i, i ≤ n → (m : Int) ∣ chain (q : Int) P y0 b J i - chain (q : Int) P y0' b' J' i := by
  intro i
  induction i with
  | zero => intro _; exact h0
  | succ i ih =>
    intro hi
    obtain ⟨k, hk⟩ := ih (by omega)
    obtain ⟨g1, hg1⟩ := chain_rel_mod (m : Int) q P y0 b J n hI hP i (by omega)
    obtain ⟨g2, hg2⟩ := chain_rel_mod (m : Int) q P y0' b' J' n hI' hP i (by omega)
    have hbe : b (i + 1) = b' (i + 1) := hbb (i + 1) (by omega) hi
    rw [hbe] at hg1
    have hid : (q : Int) * (chain (q : Int) P y0 b J (i + 1) - chain (q : Int) P y0' b' J' (i + 1))
        = ((q : Int) * chain (q : Int) P y0 b J (i + 1) + 1 - (2 : Int) ^ (b' (i + 1)) * chain (q : Int) P y0 b J i)
          - ((q : Int) * chain (q : Int) P y0' b' J' (i + 1) + 1 - (2 : Int) ^ (b' (i + 1)) * chain (q : Int) P y0' b' J' i)
          + (2 : Int) ^ (b' (i + 1)) * (chain (q : Int) P y0 b J i - chain (q : Int) P y0' b' J' i) := by
      int_ring
    rw [hg1, hg2, hk] at hid
    have hq : (m : Int) ∣ (q : Int) * (chain (q : Int) P y0 b J (i + 1) - chain (q : Int) P y0' b' J' (i + 1)) := by
      refine ⟨g1 - g2 + (2 : Int) ^ (b' (i + 1)) * k, ?_⟩
      rw [hid]; int_ring
    exact int_cancel m q hm0 hcop _ hq

theorem least_in_class (P Lam b j0 amin : Nat) (hP : 0 < P) (hL : 0 < Lam) (hbP : b ≤ P)
    (ha : 1 ≤ amin) :
    ∃ j : Nat, j % Lam = j0 % Lam ∧ amin ≤ b + j * P ∧ b + j * P < amin + P * Lam := by
  obtain ⟨E, hE1, hE2, hE3⟩ := exists_in_class (b + j0 * P) amin (P * Lam) (Nat.mul_pos hP hL)
  have hbE : b ≤ E := by
    rcases Nat.lt_or_ge E b with hlt | hge
    · exfalso
      have h1 : E % P = (b + j0 * P) % P := by
        have h2 : E % P = (E % (P * Lam)) % P := (Nat.mod_mod_of_dvd E (Nat.dvd_mul_right P Lam)).symm
        rw [h2, hE3, Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right P Lam)]
      have hb' : (b + j0 * P) % P = b % P := by
        rw [Nat.add_mod, Nat.mul_mod_left, Nat.add_zero, Nat.mod_mod]
      rw [hb'] at h1
      have hEP : E % P = E := Nat.mod_eq_of_lt (by omega)
      rw [hEP] at h1
      rcases Nat.lt_or_ge b P with hbl | hbe
      · rw [Nat.mod_eq_of_lt hbl] at h1; omega
      · have hbPe : b = P := by omega
        rw [hbPe, Nat.mod_self] at h1; omega
    · exact hge
  have hdvd : P ∣ E - b := by
    have e1 : E % P = (b + j0 * P) % P := by
      have h2 : E % P = (E % (P * Lam)) % P := (Nat.mod_mod_of_dvd E (Nat.dvd_mul_right P Lam)).symm
      rw [h2, hE3, Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right P Lam)]
    have hb' : (b + j0 * P) % P = b % P := by
      rw [Nat.add_mod, Nat.mul_mod_left, Nat.add_zero, Nat.mod_mod]
    have hsub := Nat.sub_mod_eq_zero_of_mod_eq (e1.trans hb')
    exact Nat.dvd_of_mod_eq_zero hsub
  obtain ⟨j, hj⟩ := hdvd
  have hj' : E - b = j * P := by rw [hj, Nat.mul_comm]
  have hEj : E = b + j * P := by omega
  refine ⟨j, ?_, ?_, ?_⟩
  · have hI := nat_mod_to_int_dvd E (b + j0 * P) (P * Lam) hE3
    have hPi : (P : Int) ≠ 0 := by omega
    have e2 : (E : Int) - ((b + j0 * P : Nat) : Int) = (P : Int) * ((j : Int) - (j0 : Int)) := by
      rw [hEj]; simp only [Int.natCast_add, Int.natCast_mul]; int_ring
    rw [e2, Int.natCast_mul] at hI
    obtain ⟨k, hk⟩ := hI
    have hk2 : (j : Int) - (j0 : Int) = (Lam : Int) * k := by
      apply Int.eq_of_mul_eq_mul_left hPi
      rw [hk]; int_ring
    have hmod : (j : Int) % (Lam : Int) = (j0 : Int) % (Lam : Int) := by
      apply Int.emod_eq_emod_iff_emod_sub_eq_zero.2
      rw [hk2]; exact Int.mul_emod_right _ _
    have hjn : ((j % Lam : Nat) : Int) = ((j0 % Lam : Nat) : Int) := by
      rw [Int.natCast_emod, Int.natCast_emod]; exact hmod
    exact Int.natCast_inj.1 hjn
  · omega
  · omega


end Collatz
