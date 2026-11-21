import Collatz.WideStep

namespace Collatz

theorem steer (q m' e γ : Nat) (hm0 : 0 < m') (he0 : 0 < e) (he : 2 ^ e % m' = 1 % m')
    (hcov : Covers q m' γ) (hqm : Nat.Coprime m' q) (z0 ρb : Int) :
    ∃ β : Nat → Nat, (∀ l, 1 ≤ l → l ≤ γ + 1 → 1 ≤ β l ∧ β l ≤ e) ∧
      ∀ x : Nat → Int, (m' : Int) ∣ x 0 - z0 →
        (∀ l, 1 ≤ l → l ≤ γ + 1 → (m' : Int) ∣ (q : Int) * x l + 1 - 2 ^ (β l) * x (l - 1)) →
        (m' : Int) ∣ x (γ + 1) - ρb := by
  have hmI : (0 : Int) < (m' : Int) := by omega

  obtain ⟨T, hT⟩ : ∃ T : Int, T = z0 - (q : Int) ^ γ - (q : Int) ^ (γ + 1) * ρb := ⟨_, rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T' : Nat, (T' : Int) = T % (m' : Int) :=
    ⟨(T % (m' : Int)).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))⟩
  have hT'lt : T' < m' := Int.ofNat_lt.1 (by rw [hT']; exact Int.emod_lt_of_pos _ hmI)
  obtain ⟨is, hl, hlt, hws⟩ := (covers_iff_bounded q m' e he0 he γ).1 hcov T' hT'lt
  have hwT : (m' : Int) ∣ (wsum q is : Int) - T := by
    have h1 := nat_mod_to_int_dvd _ _ _ hws
    have h2 : (m' : Int) ∣ (T' : Int) - T := by
      rw [hT', Int.emod_def]; exact ⟨-(T / (m' : Int)), by int_ring⟩
    have e3 : (wsum q is : Int) - T = ((wsum q is : Int) - (T' : Int)) + ((T' : Int) - T) := by int_ring
    rw [e3]; exact Int.dvd_add h1 h2

  obtain ⟨c0, hmem0, hW0⟩ := cover_c q is
  obtain ⟨c, hc⟩ : ∃ c : Nat → Nat, c = fun k => if k = 0 then 0 else if k ≤ γ then c0 k else 0 := ⟨_, rfl⟩
  have hc0 : c 0 = 0 := by rw [hc]; simp
  have hcg : c (γ + 1) = 0 := by
    have hn : ¬ (γ + 1 ≤ γ) := by omega
    rw [hc]; simp [hn]
  have hcmid : ∀ k, 1 ≤ k → k ≤ γ → c k = c0 k := by
    intro k h1 h2; rw [hc]; simp [show k ≠ 0 by omega, h2]
  have hclt : ∀ k, k ≤ γ + 1 → c k < e := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, hc0]; exact he0
    · rcases Nat.lt_or_ge γ k with h2 | h2
      · have : k = γ + 1 := by omega
        rw [this, hcg]; exact he0
      · rw [hcmid k h h2]
        have := hmem0 k h (by rw [hl]; exact h2)
        exact hlt _ this
  have hcW : wsumFun q c γ = wsum q is := by
    rw [← hW0, hl] at *
    exact wsumFun_congr q c c0 γ (fun k h1 h2 => hcmid k h1 h2)
  obtain ⟨β, hβ⟩ : ∃ β : Nat → Nat, β = fun l => (c (l - 1) + e - c l - 1) % e + 1 := ⟨_, rfl⟩
  have hβb : ∀ l, 1 ≤ l → l ≤ γ + 1 → 1 ≤ β l ∧ β l ≤ e := by
    intro l h1 h2
    have hbl : β l = (c (l - 1) + e - c l - 1) % e + 1 := by rw [hβ]
    have := Nat.mod_lt (c (l - 1) + e - c l - 1) he0
    rw [hbl]
    exact ⟨by omega, by omega⟩
  have hβc : ∀ l, 1 ≤ l → l ≤ γ + 1 → (c l + β l) % e = c (l - 1) % e := by
    intro l h1 h2
    have hcl := hclt l h2
    have hdm := Nat.div_add_mod (c (l - 1) + e - c l - 1) e
    have hbl : β l = (c (l - 1) + e - c l - 1) % e + 1 := by rw [hβ]
    have hs : c l + β l + e * ((c (l - 1) + e - c l - 1) / e) = c (l - 1) + e := by omega
    have := Nat.add_mul_mod_self_left (c l + β l) e ((c (l - 1) + e - c l - 1) / e)
    rw [hs, Nat.add_mod_right] at this
    exact this.symm

  have claim1 : ∀ n, n ≤ γ + 1 → (2 ^ (c n) * fwdSum q β n) % m' = wsumFun q c n % m' := by
    intro n
    induction n with
    | zero => intro _; simp [fwdSum, wsumFun, hc0]
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      have hU : 2 ^ (c (n + 1) + β (n + 1)) % m' = 2 ^ (c n) % m' := by
        apply pow_two_mod_period m' e he
        have := hβc (n + 1) (by omega) hn
        simpa using this
      have e1 : 2 ^ (c (n + 1)) * fwdSum q β (n + 1)
          = 2 ^ (c (n + 1) + β (n + 1)) * fwdSum q β n + q ^ n * 2 ^ (c (n + 1)) := by
        show 2 ^ (c (n + 1)) * (2 ^ (β (n + 1)) * fwdSum q β n + q ^ n) = _
        rw [Nat.pow_add]; (first | nat_ring | int_ring)
      rw [e1]
      show _ = (wsumFun q c n + q ^ n * 2 ^ (c (n + 1))) % m'
      rw [add_mod_cong _ (2 ^ (c n) * fwdSum q β n) _ _ (mul_mod_cong _ _ _ _ hU)]
      exact add_mod_cong _ _ _ _ ih'

  have claim2 : ∀ n, n ≤ γ + 1 → (asum β n + c n) % e = 0 := by
    intro n
    induction n with
    | zero => intro _; simp [asum, hc0]
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      have h1 := hβc (n + 1) (by omega) hn
      simp only [Nat.add_sub_cancel] at h1
      have e1 : asum β (n + 1) + c (n + 1) = asum β n + (c (n + 1) + β (n + 1)) := by
        show asum β n + β (n + 1) + c (n + 1) = _; omega
      rw [e1, Nat.add_mod, h1, ← Nat.add_mod]
      exact ih'
  have hB : 2 ^ (asum β (γ + 1)) % m' = 1 % m' := by
    have h := claim2 (γ + 1) (Nat.le_refl _)
    rw [hcg, Nat.add_zero] at h
    have := pow_two_mod_period m' e he (asum β (γ + 1)) 0 (by rw [h]; simp)
    simpa using this
  refine ⟨β, hβb, fun x hx0 hrel => ?_⟩

  have unroll : ∀ n, n ≤ γ + 1 → (m' : Int) ∣
      (2 : Int) ^ (asum β n) * x 0 - (q : Int) ^ n * x n - (fwdSum q β n : Int) := by
    intro n
    induction n with
    | zero => intro _; simp [asum, fwdSum]
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 := hrel (n + 1) (by omega) hn
      simp only [Nat.add_sub_cancel] at h2
      obtain ⟨g1, hg1⟩ := h1
      obtain ⟨g2, hg2⟩ := h2
      have hF : ((fwdSum q β (n + 1) : Nat) : Int) = (2 : Int) ^ (β (n + 1)) * (fwdSum q β n : Int) + (q : Int) ^ n := by
        show (((2 ^ (β (n + 1)) * fwdSum q β n + q ^ n : Nat)) : Int) = _
        simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow]
        rfl
      have hBs : (2 : Int) ^ (asum β (n + 1)) = (2 : Int) ^ (asum β n) * (2 : Int) ^ (β (n + 1)) := by
        show (2 : Int) ^ (asum β n + β (n + 1)) = _
        rw [Int.pow_add]
      have hq1 : (q : Int) ^ (n + 1) = (q : Int) ^ n * (q : Int) := Int.pow_succ _ _
      rw [hF, hBs, hq1]
      have e : (2 : Int) ^ (asum β n) * (2 : Int) ^ (β (n + 1)) * x 0
          - (q : Int) ^ n * (q : Int) * x (n + 1)
          - ((2 : Int) ^ (β (n + 1)) * (fwdSum q β n : Int) + (q : Int) ^ n)
          = (2 : Int) ^ (β (n + 1)) * ((2 : Int) ^ (asum β n) * x 0 - (q : Int) ^ n * x n - (fwdSum q β n : Int))
            - (q : Int) ^ n * ((q : Int) * x (n + 1) + 1 - (2 : Int) ^ (β (n + 1)) * x n) := by int_ring
      rw [e, hg1, hg2]
      exact ⟨(2 : Int) ^ (β (n + 1)) * g1 - (q : Int) ^ n * g2, by int_ring⟩
  have hU := unroll (γ + 1) (Nat.le_refl _)

  have hB' : (m' : Int) ∣ (2 : Int) ^ (asum β (γ + 1)) - 1 := by
    have := nat_mod_to_int_dvd _ _ _ hB
    simpa using this
  have hF1 : (m' : Int) ∣ (fwdSum q β (γ + 1) : Int) - ((wsum q is : Int) + (q : Int) ^ γ) := by
    have h := claim1 (γ + 1) (Nat.le_refl _)
    have hWs : wsumFun q c (γ + 1) = wsum q is + q ^ γ * 2 ^ (c (γ + 1)) := by
      show wsumFun q c γ + q ^ γ * 2 ^ (c (γ + 1)) = _
      rw [hcW]
    rw [hcg, Nat.pow_zero, Nat.one_mul, hWs, hcg, Nat.pow_zero, Nat.mul_one] at h
    have := nat_mod_to_int_dvd _ _ _ h
    simpa [Int.natCast_add, Int.natCast_pow] using this
  have hE : (m' : Int) ∣ (q : Int) ^ (γ + 1) * (ρb - x (γ + 1)) := by
    have e : (q : Int) ^ (γ + 1) * (ρb - x (γ + 1))
        = ((2 : Int) ^ (asum β (γ + 1)) * x 0 - (q : Int) ^ (γ + 1) * x (γ + 1) - (fwdSum q β (γ + 1) : Int))
          - ((2 : Int) ^ (asum β (γ + 1)) - 1) * x 0 - (x 0 - z0)
          + ((fwdSum q β (γ + 1) : Int) - ((wsum q is : Int) + (q : Int) ^ γ))
          + ((wsum q is : Int) - T) := by
      rw [hT]; int_ring
    rw [e]
    refine Int.dvd_add (Int.dvd_add (Int.dvd_sub (Int.dvd_sub hU ?_) hx0) hF1) hwT
    exact Int.dvd_mul_of_dvd_left hB'
  have hcoprime : Nat.Coprime m' (q ^ (γ + 1)) := Nat.Coprime.pow_right (γ + 1) hqm
  have hE' : (m' : Int) ∣ ((q ^ (γ + 1) : Nat) : Int) * (ρb - x (γ + 1)) := by
    rw [Int.natCast_pow]; exact hE
  obtain ⟨g, hg⟩ := int_cancel m' (q ^ (γ + 1)) hm0 hcoprime _ hE'
  exact ⟨-g, by rw [Int.mul_neg]; omega⟩


end Collatz
