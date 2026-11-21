import Collatz.ProofSteps

namespace Collatz

theorem delay_line_witness (q K P uPn τ ν t N B amin : Nat) [NonWieferich q] (ρ c : Int)
    (hP : (2 : Int) ^ P = 1 + (q : Int) ^ (K + 1) * (uPn : Int))
    (huP : Nat.Coprime q uPn)
    (hc : (q : Int) ^ (K + 1) ∣ (2 - (q : Int)) * c - 1)
    (hνc : (q : Int) ^ (K + 1) ∣ (2 : Int) ^ ν * (t : Int) - c)
    (ht1 : 1 ≤ t) (hN : K ≤ N)
    (b : Nat → Nat) (hb1 : ∀ i, 1 ≤ i → i ≤ K + 1 → b i = 1)
    (hbpos : ∀ i, 1 ≤ i → i ≤ K + 1 + τ → 1 ≤ b i)
    (E0 : Nat) (hbE : ∀ i, 1 ≤ i → i ≤ K + 1 + τ → b i ≤ E0) (hE0P : E0 ≤ P)
    (hPpos : 0 < P) (hB : q * (B + 1) + 1 ≤ 2 ^ amin) :
    ∃ J : Nat → Nat, Integral (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J (K + 1 + τ) ∧
      ∃ y : Nat, Reaches q y t ∧ B < y ∧
      (q : Int) ^ N ∣ chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J (K + 1 + τ) - ρ ∧
      (y : Int) = chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J (K + 1 + τ) ∧
      chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J (K + 1 + τ)
        ≤ (2 : Int) ^ (ν + (K + τ) * ((q - 1) * P + E0) + (amin + P * q ^ (N - K))) * (t : Int) := by
  have hodd := NonWieferich.odd (q := q)
  have hq3 := NonWieferich.three_le (q := q)
  have hq0 : 0 < q := by omega
  have hcop : Nat.Coprime q uPn := huP
  have S := setup_of q K P uPn c ((2 : Int) ^ ν * (t : Int)) b hP huP hc hνc hb1
  obtain ⟨f, hfb, hf⟩ := choose_shifts (p := (q : Int)) q hq0 rfl S τ ρ
  obtain ⟨j0, hj0, hw⟩ := wide_step q hq3 hodd hcop rfl S τ ρ N hN f hf
  have hΛ : 0 < q ^ (N - K) := Nat.pow_pos (by omega)
  have ha1 : 1 ≤ amin := by
    rcases Nat.eq_zero_or_pos amin with h | h
    · subst h
      have : 0 < q * (B + 1) := Nat.mul_pos hq0 (Nat.succ_pos B)
      simp at hB; omega
    · exact h
  obtain ⟨j, hjmod, hjlo, hjhi⟩ := least_in_class P (q ^ (N - K)) (b (K + 1 + τ)) j0 amin hPpos hΛ
    (Nat.le_trans (hbE (K + 1 + τ) (by omega) (Nat.le_refl _)) hE0P) ha1
  have hJmod : j % q ^ (N - K) = j0 := by rw [hjmod]; exact Nat.mod_eq_of_lt hj0
  obtain ⟨J0, hJ0⟩ : ∃ J0 : Nat → Nat, J0 = fun l => if l ≤ K + τ then f l else if l = K + 1 + τ then j else 0 :=
    ⟨_, rfl⟩
  have hJa : ∀ l, 1 ≤ l → l ≤ K + τ → J0 l = f l := by
    intro l h1 h2; rw [hJ0]; simp [h2]
  have hJs : J0 (K + 1 + τ) = j := by
    have hn : ¬ (K + 1 + τ ≤ K + τ) := by omega
    rw [hJ0]; simp [hn]
  refine ⟨J0, ?_⟩
  obtain ⟨hI, _⟩ := hf J0 hJa
  have hdiv := hw J0 hJa (by rw [hJs]; exact hJmod)
  have hy0 : 1 ≤ (2 : Int) ^ ν * (t : Int) := by
    have h1 := ipow2_ge_one ν
    have := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ (t : Int) by omega)
      (show (0 : Int) ≤ (2 : Int) ^ ν by omega)
    rw [Int.mul_one] at this; omega
  have hY0 : ((2 ^ ν * t : Nat) : Int) = (2 : Int) ^ ν * (t : Int) := by
    simp only [Int.natCast_mul, Int.natCast_pow]; norm_cast
  obtain ⟨yi, hyi, hr⟩ := chain_reaches q P ((2 : Int) ^ ν * (t : Int)) b J0 (K + 1 + τ) hI hy0
    (fun l h1 h2 => hbpos l h1 h2) (2 ^ ν * t) hY0 (K + 1 + τ) (Nat.le_refl _)
  have hreach : Reaches q yi t := reaches_trans q hr (reaches_pow2 q t ν)

  have hstep := step_lower q P ((2 : Int) ^ ν * (t : Int)) b J0 (K + 1 + τ) hI hy0
    (fun l h1 h2 => hbpos l h1 h2) (K + τ) (by omega)
  have e1 : K + τ + 1 = K + 1 + τ := by omega
  rw [e1, hJs] at hstep
  have hpow : (2 : Int) ^ amin ≤ (2 : Int) ^ (b (K + 1 + τ) + j * P) :=
    ipow2_mono _ _ hjlo
  have hBi : (q : Int) * ((B : Int) + 1) + 1 ≤ (2 : Int) ^ amin := by
    have := hB; exact_mod_cast this
  have hyB : (B : Int) + 1 ≤ chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J0 (K + 1 + τ) := by
    have hq' : (0 : Int) < (q : Int) := by omega
    have h1 : (q : Int) * ((B : Int) + 1) ≤ (q : Int) * chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J0 (K + 1 + τ) := by
      have := Int.le_trans hBi (Int.le_trans hpow hstep); omega
    exact Int.le_of_mul_le_mul_left h1 hq'
  have hBy : B < yi := by
    have : (yi : Int) = chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J0 (K + 1 + τ) := hyi
    omega
  refine ⟨hI, yi, hreach, hBy, hdiv, hyi, ?_⟩

  have hsmall : ∀ l, 1 ≤ l → l + 1 ≤ K + 1 + τ → b l + J0 l * P ≤ (q - 1) * P + E0 := by
    intro l h1 h2
    have hJl : J0 l = f l := hJa l h1 (by omega)
    have hfl : f l < q := hfb l h1 (by omega)
    have hbl := hbE l h1 (by omega)
    have hmul : J0 l * P ≤ (q - 1) * P := by
      apply Nat.mul_le_mul_right; rw [hJl]; omega
    omega
  have hlast : b (K + 1 + τ) + J0 (K + 1 + τ) * P ≤ amin + P * q ^ (N - K) := by
    rw [hJs]; have := hjhi; rw [Nat.mul_comm j P] at *; omega
  have hsz := size_bound q P ν t (K + 1 + τ) ((q - 1) * P + E0) (amin + P * q ^ (N - K)) ν b J0
    (by omega) ht1 (Nat.le_refl ν) hI (fun l h1 h2 => hbpos l h1 (by omega)) hsmall hlast
  have e2 : K + 1 + τ - 1 = K + τ := by omega
  rw [e2] at hsz
  exact hsz

def steps (K γ m' : Nat) : Nat := if m' = 1 then 1 else K + γ + 2

theorem chain_witness (q K P uPn e γ ν t N B amin m' : Nat) [NonWieferich q] (ρ c : Int)
    (hP : (2 : Int) ^ P = 1 + (q : Int) ^ (K + 1) * (uPn : Int))
    (huP : Nat.Coprime q uPn)
    (hc : (q : Int) ^ (K + 1) ∣ (2 - (q : Int)) * c - 1)
    (hνc : (q : Int) ^ (K + 1) ∣ (2 : Int) ^ ν * (t : Int) - c)
    (ht1 : 1 ≤ t) (hN : K ≤ N)
    (hPpos : 0 < P) (heP : e ∣ P) (he0 : 0 < e) (he : 2 ^ e % m' = 1 % m')
    (hcov : Covers q m' γ) (hqm : Nat.Coprime m' q) (hm0 : 0 < m') (hK1 : m' = 1 → K = 0)
    (hB : q * (B + 1) + 1 ≤ 2 ^ amin) :
    ∃ y : Nat, Reaches q y t ∧ B < y ∧ (q : Int) ^ N * (m' : Int) ∣ (y : Int) - ρ ∧
      (y : Int) ≤ (2 : Int) ^ (ν + (steps K γ m' - 1) * ((q - 1) * P + e) + (amin + P * q ^ (N - K)))
        * (t : Int) := by
  by_cases h1 : m' = 1
  · have hK := hK1 h1
    subst h1; subst hK
    obtain ⟨J, _, y, hr, hBy, hdiv, hyi, hsz⟩ := delay_line_witness q 0 P uPn 0 ν t N B amin ρ c hP huP hc hνc
      ht1 hN (fun _ => 1) (fun _ _ _ => rfl) (fun _ _ _ => Nat.le_refl 1)
      e (fun _ _ _ => he0) (Nat.le_of_dvd hPpos heP) hPpos hB
    refine ⟨y, hr, hBy, ?_, ?_⟩
    · rw [hyi]; simpa using hdiv
    · have hs : steps 0 γ 1 - 1 = 0 := by simp [steps]
      rw [hs, hyi]; simpa using hsz
  · have hs : steps K γ m' - 1 = K + (γ + 1) := by simp [steps, h1]; omega
    rw [hs]
    have hq0 : 0 < q := by have := NonWieferich.three_le (q := q); omega
    have hodd := NonWieferich.odd (q := q)
    have hqcop : Nat.Coprime m' q := hqm

    have hm2P : (m' : Int) ∣ (2 : Int) ^ P - 1 := by
      have h1 : 2 ^ P % m' = 1 % m' := by
        have := pow_two_mod_period m' e he P 0 (by rw [Nat.zero_mod]; exact Nat.mod_eq_zero_of_dvd heP)
        rw [Nat.pow_zero] at this; exact this
      have h2 := nat_mod_to_int_dvd (2 ^ P) 1 m' h1
      simp only [Int.natCast_pow, Int.natCast_one] at h2
      exact h2

    have S0 := setup_of q K P uPn c ((2 : Int) ^ ν * (t : Int)) (fun _ => 1) hP huP hc hνc (fun i _ _ => rfl)
    have hI0 : Integral (q : Int) P ((2 : Int) ^ ν * (t : Int)) (fun _ => 1) (fun _ => 0) (K + 1) := (primer_chain S0 (fun _ => 0)).2

    obtain ⟨β, hβb, hβs⟩ := steer q m' e γ hm0 he0 he hcov hqcop
      (chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) (fun _ => 1) (fun _ => 0) (K + 1)) ρ
    obtain ⟨b', hb'⟩ : ∃ b' : Nat → Nat, b' = fun i => if i ≤ K + 1 then 1 else β (i - (K + 1)) := ⟨_, rfl⟩
    have hb1 : ∀ i, 1 ≤ i → i ≤ K + 1 → b' i = 1 := by
      intro i h1 h2; rw [hb']; simp [h2]
    have hβle : ∀ l, 1 ≤ l → l ≤ γ + 1 → 1 ≤ β l ∧ β l ≤ e := hβb
    have hbpos : ∀ i, 1 ≤ i → i ≤ K + 1 + (γ + 1) → 1 ≤ b' i := by
      intro i h1 h2
      by_cases hi : i ≤ K + 1
      · rw [hb1 i h1 hi]; exact Nat.le_refl 1
      · rw [hb']; simp only [hi, ite_false]
        exact (hβle (i - (K + 1)) (by omega) (by omega)).1
    have hePle : e ≤ P := Nat.le_of_dvd hPpos heP
    have hbE : ∀ i, 1 ≤ i → i ≤ K + 1 + (γ + 1) → b' i ≤ e := by
      intro i h1 h2
      by_cases hi : i ≤ K + 1
      · rw [hb1 i h1 hi]; omega
      · rw [hb']; simp only [hi, ite_false]
        exact (hβle (i - (K + 1)) (by omega) (by omega)).2
    obtain ⟨J, hI, y, hreach, hBy, hdiv, hyi, hszb⟩ :=
      delay_line_witness q K P uPn (γ + 1) ν t N B amin ρ c hP huP hc hνc ht1 hN b' hb1 hbpos e hbE hePle hPpos hB
    refine ⟨y, hreach, hBy, ?_, ?_⟩

    have hIb' : Integral (q : Int) P ((2 : Int) ^ ν * (t : Int)) b' J (K + 1) :=
      (primer_chain (setup_of q K P uPn c ((2 : Int) ^ ν * (t : Int)) b' hP huP hc hνc hb1) J).2
    have hx0 : (m' : Int) ∣ chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b' J (K + 1)
        - chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) (fun _ => 1) (fun _ => 0) (K + 1) := by
      refine class_indep_of_shifts m' q P hm0 hqcop hm2P ((2 : Int) ^ ν * (t : Int)) ((2 : Int) ^ ν * (t : Int)) b' (fun _ => 1) J (fun _ => 0) (K + 1)
        hIb' hI0 ?_ (by simp) (K + 1) (Nat.le_refl _)
      intro i h1 h2; rw [hb1 i h1 h2]
    have hrel : ∀ l, 1 ≤ l → l ≤ γ + 1 →
        (m' : Int) ∣ (q : Int) * chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b' J (K + 1 + l) + 1
          - (2 : Int) ^ (β l) * chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b' J (K + 1 + (l - 1)) := by
      intro l h1 h2
      have hc' := chain_rel_mod (m' : Int) q P ((2 : Int) ^ ν * (t : Int)) b' J (K + 1 + (γ + 1)) hI hm2P
        (K + l) (by omega)
      have e1 : K + l + 1 = K + 1 + l := by omega
      have e2 : K + 1 + (l - 1) = K + l := by omega
      have eb : b' (K + 1 + l) = β l := by
        rw [hb']; simp only [show ¬ (K + 1 + l ≤ K + 1) by omega, ite_false]
        congr 1; omega
      rw [e2, ← eb]
      rw [e1] at hc'
      exact hc'
    have hfin := hβs (fun l => chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b' J (K + 1 + l)) hx0 hrel
    obtain ⟨g, hg⟩ := hdiv
    have hcopN : Nat.Coprime m' (q ^ N) := Nat.Coprime.pow_right N hqm
    have hm'g : (m' : Int) ∣ ((q ^ N : Nat) : Int) * g := by
      rw [Int.natCast_pow, ← hg]; exact hfin
    obtain ⟨k, hk⟩ := int_cancel m' (q ^ N) hm0 hcopN g hm'g
    · refine ⟨k, ?_⟩
      rw [hyi, hg, hk]
      int_ring
    · rw [hyi]; exact hszb

def ceilLog2 (n : Nat) : Nat := Nat.log2 (n - 1) + 1

theorem ceilLog2_spec (n : Nat) : n ≤ 2 ^ ceilLog2 n := by
  unfold ceilLog2
  have := @Nat.lt_log2_self (n - 1)
  omega

theorem final_budget (α ν S Q amin dK q m B t Θ y w : Nat)
    (hw : w ≤ 2 ^ α * y) (hy : y ≤ 2 ^ (ν + S + (amin + Q)) * t) (hν : ν + 1 ≤ dK)
    (ham : 2 ^ amin ≤ 2 * (q * Θ)) (hΘ : Θ ≤ q ^ α * ((m + 1) * (B + 1))) :
    w ≤ (B + 1) * t * 2 ^ (dK + S + Q + (α + 1) + ceilLog2 (q ^ (α + 1)) + (ceilLog2 (m + 1))) := by
  have hm1 : m + 1 ≤ 2 ^ (ceilLog2 (m + 1)) := ceilLog2_spec (m + 1)
  have hqa : q ^ (α + 1) ≤ 2 ^ (ceilLog2 (q ^ (α + 1))) := ceilLog2_spec _

  have h2a : 2 ^ amin ≤ 2 ^ (1 + ceilLog2 (q ^ (α + 1)) + (ceilLog2 (m + 1))) * (B + 1) := by
    have e1 : q * Θ ≤ q ^ (α + 1) * (m + 1) * (B + 1) := by
      have := Nat.mul_le_mul_left q hΘ
      calc q * Θ ≤ q * (q ^ α * ((m + 1) * (B + 1))) := this
        _ = q ^ (α + 1) * (m + 1) * (B + 1) := by rw [Nat.pow_succ]; ac_rfl
    have e2 : q ^ (α + 1) * (m + 1) * (B + 1) ≤ 2 ^ (ceilLog2 (q ^ (α + 1))) * 2 ^ (ceilLog2 (m + 1)) * (B + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hqa hm1)
    have e3 : 2 ^ (1 + ceilLog2 (q ^ (α + 1)) + (ceilLog2 (m + 1))) * (B + 1)
        = 2 * (2 ^ (ceilLog2 (q ^ (α + 1))) * 2 ^ (ceilLog2 (m + 1)) * (B + 1)) := by
      rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]; ac_rfl
    rw [e3]; omega
  have hexp : α + (ν + S + Q) + (1 + ceilLog2 (q ^ (α + 1)) + (ceilLog2 (m + 1)))
      ≤ dK + S + Q + (α + 1) + ceilLog2 (q ^ (α + 1)) + (ceilLog2 (m + 1)) := by
    omega
  calc w ≤ 2 ^ α * y := hw
    _ ≤ 2 ^ α * (2 ^ (ν + S + (amin + Q)) * t) := Nat.mul_le_mul_left _ hy
    _ = 2 ^ (α + (ν + S + Q)) * 2 ^ amin * t := by
        rw [show ν + S + (amin + Q) = (ν + S + Q) + amin by omega,
          show α + (ν + S + Q) = α + (ν + S + Q) from rfl, Nat.pow_add 2 (ν + S + Q) amin,
          Nat.pow_add 2 α (ν + S + Q)]; ac_rfl
    _ ≤ 2 ^ (α + (ν + S + Q)) * (2 ^ (1 + ceilLog2 (q ^ (α + 1)) + (ceilLog2 (m + 1))) * (B + 1)) * t :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2a)
    _ = (B + 1) * t * 2 ^ (α + (ν + S + Q) + (1 + ceilLog2 (q ^ (α + 1)) + (ceilLog2 (m + 1)))) := by
        rw [Nat.pow_add 2 (α + (ν + S + Q))]; ac_rfl
    _ ≤ (B + 1) * t * 2 ^ (dK + S + Q + (α + 1) + ceilLog2 (q ^ (α + 1)) + (ceilLog2 (m + 1))) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hexp)


end Collatz
