import Collatz.GeneralAWide
import Collatz.GeneralASelect

/-! Theorem A, Step 3 (steering modulo m', Lemma 9) packaged for the assembly, and the core
    statement of Section 4 (generalAB.md). Choice-free (relative to `shift_select`). -/

namespace Collatz

theorem asum_le_mul (f : Nat → Nat) (X : Nat) :
    ∀ n, (∀ l, 1 ≤ l → l ≤ n → f l ≤ X) → asum f n ≤ n * X
  | 0, _ => by simp [asum]
  | n + 1, H => by
    have ih := asum_le_mul f X n (fun l h1 h2 => H l h1 (by omega))
    have hn := H (n + 1) (by omega) (Nat.le_refl _)
    show asum f n + f (n + 1) ≤ (n + 1) * X
    rw [Nat.succ_mul]; omega

theorem asum_add (f g : Nat → Nat) :
    ∀ n, asum (fun l => f l + g l) n = asum f n + asum g n
  | 0 => rfl
  | n + 1 => by
    show asum (fun l => f l + g l) n + (f (n + 1) + g (n + 1)) = asum f n + f (n + 1) + (asum g n + g (n + 1))
    rw [asum_add f g n]; omega

theorem asum_congr (f g : Nat → Nat) :
    ∀ n, (∀ l, 1 ≤ l → l ≤ n → f l = g l) → asum f n = asum g n
  | 0, _ => rfl
  | n + 1, H => by
    show asum f n + f (n + 1) = asum g n + g (n + 1)
    rw [asum_congr f g n (fun l h1 h2 => H l h1 (by omega)), H (n + 1) (by omega) (Nat.le_refl _)]

theorem asum_split (f : Nat → Nat) (n : Nat) :
    ∀ k, asum f (n + k) = asum f n + asum (fun l => f (n + l)) k
  | 0 => rfl
  | k + 1 => by
    show asum f (n + k) + f (n + k + 1) = asum f n + (asum (fun l => f (n + l)) k + f (n + (k + 1)))
    rw [asum_split f n k, show n + k + 1 = n + (k + 1) by omega]; omega

theorem integral_mono {p : Int} {P : Nat} {y0 : Int} {b J : Nat → Nat} {n n' : Nat}
    (h : Integral p P y0 b J n) (hn : n' ≤ n) : Integral p P y0 b J n' :=
  fun i hi => h i (by omega)

theorem PM_ge_d {q m : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) : dq q ≤ PM q m := by
  have h1 : dq q ≤ dq q * q ^ KM q m := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
  exact Nat.le_trans h1 (Nat.le_of_dvd (PM_pos hq hodd hm) (dK_dvd_PM q m))

theorem mp_dvd_pow2P {q m : Nat} (hq : 1 < q) (hm : 1 ≤ m) :
    (mpM q m : Int) ∣ (2 : Int) ^ PM q m - 1 := by
  have he := eM_isOrder2 (q := q) hq hm
  obtain ⟨t, ht⟩ := e_dvd_PM q m
  have h1 : 2 ^ PM q m % mpM q m = 1 % mpM q m := by
    rw [ht, Nat.pow_mul]; exact pow_mod_one _ _ _ he.2.1
  have h2 := nat_mod_to_int_dvd _ _ _ h1
  push_cast at h2; exact h2

/-- Steering (Lemma 9) packaged: exponents b with b = a up to K + κ + 1, all ≥ 1, b_s ≤ P,
    Σ_{l<s} b_l ≤ B₀(a), and every integral path ending at step s satisfies y_s ≡ ρ (mod m'). -/
theorem steer_b {q m a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) (ha1 : 1 ≤ a)
    (haD : a ≤ dq q) (hκa : κq q = 0 → a = 1) {c y0 : Int}
    (hc : (LamA q m : Int) ∣ ((2 : Int) ^ a - q) * c - 1) (hy0 : (LamA q m : Int) ∣ y0 - c)
    (ρ : Int) :
    ∃ b : Nat → Nat, (∀ l, 1 ≤ l → l ≤ KM q m + κq q + 1 → b l = a) ∧ (∀ l, 1 ≤ b l) ∧
      b (sM q m) ≤ PM q m ∧ asum b (sM q m - 1) ≤ B0 q m a ∧ KM q m + κq q + 1 ≤ sM q m ∧
      ∀ J : Nat → Nat, Integral (q : Int) (PM q m) y0 b J (sM q m) →
        (mpM q m : Int) ∣ chain (q : Int) (PM q m) y0 b J (sM q m) - ρ := by
  have hdP := PM_ge_d hq hodd hm
  by_cases hmp : mpM q m = 1
  · obtain ⟨_, hK⟩ := mp_one_params hmp
    have hs : sM q m = KM q m + κq q + 1 := by unfold sM; simp only [hmp, ↓reduceIte]
    refine ⟨fun _ => a, fun _ _ _ => rfl, fun _ => ha1, by show a ≤ PM q m; omega, ?_, by omega, fun J _ => by
      rw [hmp]; exact Int.one_dvd _⟩
    rw [hs, hK, Nat.zero_add, Nat.add_sub_cancel]
    have := asum_le_mul (fun _ => a) a (κq q) (fun _ _ _ => Nat.le_refl _)
    unfold B0; simp only [hmp, ↓reduceIte]
    exact this
  · -- m' > 1: reference path up to K0, then steer
    have he := eM_isOrder2 (q := q) hq hm
    have hmp0 : 0 < mpM q m := mp_pos hm
    have hcov := (leastCover_spec q (mpM q m) (eM q m) (mp_coprime_2q hq hm) he).1
    have hs : sM q m = (KM q m + κq q + 1) + (gammaM q m + 1) := by
      unfold sM; simp only [hmp, ↓reduceIte]; omega
    obtain ⟨Jr, _, _, hIr, _⟩ := shift_select hq hodd hm hκa hc hy0
      (b := fun _ => a) (fun _ _ _ => rfl) (Nat.le_refl (KM q m + κq q + 1)) 0
    obtain ⟨β, hβ, hβsteer⟩ := steer q (mpM q m) (eM q m) (gammaM q m) hmp0 he.1 he.2.1 hcov
      (mp_coprime_q hq hm)
      (chain (q : Int) (PM q m) y0 (fun _ => a) Jr (KM q m + κq q + 1)) ρ
    have heP : eM q m ≤ PM q m := Nat.le_of_dvd (PM_pos hq hodd hm) (e_dvd_PM q m)
    have hbeq : ∀ l, 1 ≤ l → l ≤ gammaM q m + 1 →
        max 1 (β l) = β l := fun l h1 h2 => Nat.max_eq_right (hβ l h1 h2).1
    refine ⟨fun l => if l ≤ KM q m + κq q + 1 then a else max 1 (β (l - (KM q m + κq q + 1))),
      fun l _ hl => by simp only [hl, ↓reduceIte], fun l => ?_, ?_, ?_, by omega, ?_⟩
    · by_cases hl : l ≤ KM q m + κq q + 1
      · simp only [hl, ↓reduceIte]; exact ha1
      · simp only [hl, ↓reduceIte]; exact Nat.le_max_left _ _
    · have hl : ¬ sM q m ≤ KM q m + κq q + 1 := by omega
      simp only [hl, ↓reduceIte]
      have e1 : sM q m - (KM q m + κq q + 1) = gammaM q m + 1 := by omega
      rw [e1, hbeq _ (by omega) (Nat.le_refl _)]
      exact Nat.le_trans (hβ _ (by omega) (Nat.le_refl _)).2 heP
    · have e1 : sM q m - 1 = (KM q m + κq q + 1) + gammaM q m := by omega
      rw [e1, asum_split]
      have h1 : asum (fun l => if l ≤ KM q m + κq q + 1 then a else
          max 1 (β (l - (KM q m + κq q + 1)))) (KM q m + κq q + 1) ≤ (KM q m + κq q + 1) * a :=
        asum_le_mul _ a _ (fun l _ hl => by simp only [hl, ↓reduceIte]; exact Nat.le_refl _)
      have h2 : asum (fun l => (fun l => if l ≤ KM q m + κq q + 1 then a else
          max 1 (β (l - (KM q m + κq q + 1)))) (KM q m + κq q + 1 + l)) (gammaM q m)
            ≤ gammaM q m * eM q m := by
        apply asum_le_mul
        intro l hl1 hl2
        have hl : ¬ KM q m + κq q + 1 + l ≤ KM q m + κq q + 1 := by omega
        simp only [hl, ↓reduceIte]
        have e2 : KM q m + κq q + 1 + l - (KM q m + κq q + 1) = l := by omega
        rw [e2, hbeq l hl1 (by omega)]
        exact (hβ l hl1 (by omega)).2
      refine Nat.le_trans (Nat.add_le_add h1 h2) ?_
      unfold B0; simp only [hmp, ↓reduceIte]; exact Nat.le_refl _
    · intro J hI
      have hP' := mp_dvd_pow2P hq hm
      have hK0 := class_indep_of_shifts (mpM q m) q (PM q m) hmp0 (mp_coprime_q hq hm) hP' y0 y0
        _ (fun _ => a) J Jr (KM q m + κq q + 1) (integral_mono hI (by omega)) hIr
        (fun i _ hi => by simp only [hi, ↓reduceIte]) (by rw [Int.sub_self]; exact Int.dvd_zero _)
        (KM q m + κq q + 1) (Nat.le_refl _)
      have key := hβsteer (fun l => chain (q : Int) (PM q m) y0
          (fun l => if l ≤ KM q m + κq q + 1 then a else max 1 (β (l - (KM q m + κq q + 1))))
          J (KM q m + κq q + 1 + l)) hK0 (fun l hl1 hl2 => by
        have h := chain_rel_mod (mpM q m : Int) q (PM q m) y0 _ J (sM q m) hI hP'
          (KM q m + κq q + 1 + l - 1) (by omega)
        have e1 : KM q m + κq q + 1 + l - 1 + 1 = KM q m + κq q + 1 + l := by omega
        have e2 : KM q m + κq q + 1 + (l - 1) = KM q m + κq q + 1 + l - 1 := by omega
        rw [e1] at h
        have hl : ¬ KM q m + κq q + 1 + l ≤ KM q m + κq q + 1 := by omega
        have e3 : KM q m + κq q + 1 + l - (KM q m + κq q + 1) = l := by omega
        simp only [hl, ↓reduceIte, e3, hbeq l hl1 hl2] at h
        show (mpM q m : Int) ∣ (q : Int) * chain (q : Int) (PM q m) y0 _ J (KM q m + κq q + 1 + l) + 1
          - 2 ^ β l * chain (q : Int) (PM q m) y0 _ J (KM q m + κq q + 1 + (l - 1))
        rw [e2]; exact h)
      have e4 : KM q m + κq q + 1 + (gammaM q m + 1) = sM q m := by omega
      simp only [e4] at key
      exact key

theorem lt_of_mul_lt_mul_left' {a b c : Nat} (h : a * b < a * c) : b < c := by
  match Nat.lt_or_ge b c with
  | Or.inl hl => exact hl
  | Or.inr hge =>
    exfalso
    have := Nat.mul_le_mul_left a hge
    omega

/-- n(r): the number of odd letters in the tail word of r mod 2^α. -/
def nfA (q m r : Nat) : Nat := ones (tailw q (alphaM m) (r % 2 ^ alphaM m))

/-- The core of Section 4: for x satisfying (H) with exponent a, every residue class r mod m
    contains some w → x beyond B, with the bound of Theorem A in terms of x. -/
theorem core_A {q m a x : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) (hx1 : 1 ≤ x)
    (ha1 : 1 ≤ a) (haD : a ≤ dq q) (hκa : κq q = 0 → a = 1) (hHa : HypHa q a x) (r B : Nat) :
    ∃ w, Reaches q w x ∧ w % m = r % m ∧ B < w ∧
      (w < 2 ^ (alphaM m + Qt q m (nfA q m r)) * (B + MM q m + 1) ∨
        w * q ^ (nfA q m r + sM q m) <
          2 ^ (alphaM m + Qt q m (nfA q m r) + dq q * q ^ KM q m - 1
            + (sM q m - 1) * J0star q * PM q m + B0 q m a) * x) := by
  have hq3 : 3 ≤ q := by omega
  have hm2 : m = 2 ^ alphaM m * MM q m := m_decomp hm
  have h2m : 2 ^ alphaM m ∣ m := ⟨MM q m, hm2⟩
  have hrb : r % m < m := Nat.mod_lt _ (by omega)
  have hrb2 : (r % m) % 2 ^ alphaM m = (r % 2 ^ alphaM m) % 2 ^ alphaM m := by
    rw [Nat.mod_mod_of_dvd r h2m, Nat.mod_mod]
  have hword : tailw q (alphaM m) (r % m) = tailw q (alphaM m) (r % 2 ^ alphaM m) :=
    tailw_mod hodd _ _ _ hrb2
  have hn : ones (tailw q (alphaM m) (r % m)) = nfA q m r := by unfold nfA; rw [hword]
  have hρM : tailv q (alphaM m) (r % m) + 1 ≤ q ^ nfA q m r * MM q m := by
    have h := tail_bound hq3 hodd (alphaM m) (r % m) (MM q m) (by rw [← hm2]; omega)
    rwa [hn] at h
  generalize hρd : tailv q (alphaM m) (r % m) = ρ at hρM
  generalize hnd : nfA q m r = n at hn hρM ⊢
  have hqn : 0 < q ^ n := Nat.pow_pos (by omega)
  -- Step 1: start
  obtain ⟨i0, hi0, hH'⟩ := hypha_nat hq hodd hx1 hHa
  obtain ⟨c, hc⟩ := cstar_exists (m := m) hq hodd a
  obtain ⟨lam0, hlam, hy0n⟩ := start_point (m := m) hq hodd hx1 hH' hi0 hc
  have hqL := q_le_LamA (m := m) hq hodd
  have hcI : (LamA q m : Int) ∣ ((2 : Int) ^ a - q) * c - 1 := by
    have h := nat_mod_to_int_dvd _ _ _ hc
    have h2a : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    have e : (((2 ^ a + LamA q m - q) * c : Nat) : Int) - ((1 : Nat) : Int)
        = (((2 : Int) ^ a - q) * c - 1) + (LamA q m : Int) * c := by
      rw [Int.natCast_mul, Int.ofNat_sub (by omega)]; push_cast; int_ring
    rw [e] at h
    exact (Int.dvd_add_left (Int.dvd_mul_right _ _)).mp h
  have hy0I : (LamA q m : Int) ∣ ((2 ^ lam0 * x : Nat) : Int) - c := nat_mod_to_int_dvd _ _ _ hy0n
  have hy0p : (1 : Int) ≤ ((2 ^ lam0 * x : Nat) : Int) := by
    have : 1 ≤ 2 ^ lam0 * x := Nat.mul_pos Nat.one_le_two_pow hx1
    exact_mod_cast this
  -- Steps 3–4: exponents and shifts
  obtain ⟨b, hbK, hb1, hbs, hbsum, hsK, hmod⟩ := steer_b hq hodd hm ha1 haD hκa hcI hy0I (ρ : Int)
  obtain ⟨J, hJle, hJs, hI, hρq⟩ :=
    shift_select hq hodd hm hκa hcI hy0I hbK hsK (ρ : Int)
  -- Step 5: wide step
  have hs1 : 1 ≤ sM q m := by omega
  obtain ⟨j, Y, Ys, hY, hYs, hI', hrel, hΘYs, hres, hcase⟩ := gwide_step (n := n) hq hodd hm hs1 hI
    hJs hy0p (fun l _ _ => hb1 l) hbs ρ (ρ + q ^ n * (B + 1)) hρq
  -- y_s ≡ ρ (mod q^n m_q m')
  have hmodm' : Ys % mpM q m = ρ % mpM q m := by
    have h := hmod _ hI'
    rw [← hYs] at h
    exact nat_mod_of_int_dvd h
  have hqmq : q ^ n * mqM q m ∣ q ^ KM q m * uqq q * Wt q m n := by
    rw [Wt_mul]; exact Nat.dvd_lcm_left _ _
  have hmodq : Ys % (q ^ n * mqM q m) = ρ % (q ^ n * mqM q m) := by
    rw [← Nat.mod_mod_of_dvd Ys hqmq, hres, Nat.mod_mod_of_dvd ρ hqmq]
  have hcop : Nat.Coprime (q ^ n * mqM q m) (mpM q m) := by
    apply coprime_of_no_prime
    intro p hp h1 h2
    have hpq : p ∣ q := by
      rcases isPrime_dvd_mul hp h1 with h3 | h3
      · exact isPrime_dvd_pow hp n h3
      · exact isPrime_dvd_pow hp _ (Nat.dvd_trans h3 (mq_dvd_pow q m))
    have := Nat.dvd_gcd h2 hpq
    rw [mp_coprime_q hq hm] at this
    have := Nat.le_of_dvd Nat.one_pos this; have := hp.1; omega
  have hdiv : q ^ n * MM q m ∣ Ys - ρ := by
    have e : q ^ n * MM q m = (q ^ n * mqM q m) * mpM q m := by
      show q ^ n * (mqM q m * mpM q m) = _; rw [Nat.mul_assoc]
    rw [e]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop
      (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmodq))
      (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmodm'))
  -- tail
  obtain ⟨w, hBw, hwm, hRw, hwle⟩ := tail_match hq3 hodd hm2 (rb := r % m) (B := B) (y := Ys)
    (by rw [hn, hρd]; exact hΘYs) (by rw [hn, hρd]; exact hdiv)
  rw [hn] at hwle
  -- reachability
  have hYsodd : Ys % 2 = 1 := by
    have hev : 2 ^ (b (sM q m) + j * PM q m) * Y % 2 = 0 := by
      have e : b (sM q m) + j * PM q m = (b (sM q m) + j * PM q m - 1) + 1 := by
        have := hb1 (sM q m); omega
      rw [e, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
      exact Nat.mul_mod_right _ _
    have hm' := Nat.mul_mod q Ys 2
    rw [hodd] at hm'
    rcases Nat.mod_two_eq_zero_or_one Ys with h | h
    · rw [h] at hm'; omega
    · exact h
  have hcs1 : chain (q : Int) (PM q m) ((2 ^ lam0 * x : Nat) : Int) b
      (fun l => if l = sM q m then j else J l) (sM q m - 1)
      = chain (q : Int) (PM q m) ((2 ^ lam0 * x : Nat) : Int) b J (sM q m - 1) :=
    (chain_congr (q : Int) (PM q m) _ b J _ (sM q m - 1) (fun l h1 h2 => by
      have : ¬ l = sM q m := by omega
      simp only [this, ↓reduceIte])).symm
  obtain ⟨yi, hyi, hRyi⟩ := chain_reach hq hodd (PM q m) _ b _ (sM q m) hI' hy0p
    (fun l _ _ => hb1 l) (2 ^ lam0 * x) rfl (sM q m - 1) (by omega)
  have hyiY : yi = Y := by
    apply Int.ofNat_inj.1; rw [hyi, hcs1, ← hY]
  rw [hyiY] at hRyi
  have hR : Reaches q w x :=
    reaches_trans q hRw (reaches_trans q (reaches_of_step hYsodd hrel)
      (reaches_trans q hRyi ⟨lam0, iter_pow2 q lam0 x⟩))
  refine ⟨w, hR, by rw [hwm, Nat.mod_mod], hBw, ?_⟩
  -- size of y_{s-1}
  have hsz0 := chain_qsize hq (PM q m) _ b _ (sM q m) hI' hy0p (fun l _ _ => hb1 l) (sM q m - 1) (by omega)
  rw [hcs1, ← hY] at hsz0
  generalize hAd : asum (fun l => b l + (fun l => if l = sM q m then j else J l) l * PM q m) (sM q m - 1)
    = A at hsz0
  have hsz : q ^ (sM q m - 1) * Y ≤ 2 ^ A * (2 ^ lam0 * x) := by exact_mod_cast hsz0
  have hA : A ≤ B0 q m a + (sM q m - 1) * (J0star q * PM q m) := by
    rw [← hAd, asum_add]
    have h2 : asum (fun l => (fun l => if l = sM q m then j else J l) l * PM q m) (sM q m - 1)
        ≤ (sM q m - 1) * (J0star q * PM q m) := by
      apply asum_le_mul
      intro l hl1 hl2
      have hne : ¬ l = sM q m := by omega
      simp only [hne, ↓reduceIte]
      exact Nat.mul_le_mul_right _ (hJle l hl1 hl2)
    have := Nat.add_le_add hbsum h2
    exact this
  have hE : 2 ^ A * 2 ^ lam0 ≤ 2 ^ (dq q * q ^ KM q m - 1 + (sM q m - 1) * J0star q * PM q m + B0 q m a) := by
    rw [← Nat.pow_add]
    apply Nat.pow_le_pow_right (by omega)
    rw [Nat.mul_assoc]; omega
  have hQt : Qt q m n = Wt q m n * PM q m := rfl
  rcases hcase with hle | hle
  · -- k₀ = 0: right disjunct
    right
    have hs' : n + sM q m = n + (sM q m - 1) + 1 := by omega
    have hpos : 0 < 2 ^ alphaM m * q ^ (sM q m - 1) := Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
    calc w * q ^ (n + sM q m)
        = q ^ (sM q m - 1) * (q * (q ^ n * w)) := by
          rw [hs', Nat.pow_succ, Nat.pow_add]; simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ ≤ q ^ (sM q m - 1) * (q * (2 ^ alphaM m * Ys)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hwle)
      _ = (2 ^ alphaM m * q ^ (sM q m - 1)) * (q * Ys) := by
          simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ < (2 ^ alphaM m * q ^ (sM q m - 1)) * (q * Ys + 1) := Nat.mul_lt_mul_of_pos_left (by omega) hpos
      _ = 2 ^ alphaM m * 2 ^ (b (sM q m) + j * PM q m) * (q ^ (sM q m - 1) * Y) := by
          rw [hrel]; simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ ≤ 2 ^ alphaM m * 2 ^ (Qt q m n) * (2 ^ A * (2 ^ lam0 * x)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by rw [hQt]; exact hle))) hsz
      _ = 2 ^ alphaM m * 2 ^ (Qt q m n) * (2 ^ A * 2 ^ lam0) * x := by
          simp only [Nat.mul_assoc]
      _ ≤ 2 ^ alphaM m * 2 ^ (Qt q m n) *
            2 ^ (dq q * q ^ KM q m - 1 + (sM q m - 1) * J0star q * PM q m + B0 q m a) * x :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hE)
      _ = 2 ^ (alphaM m + Qt q m n + dq q * q ^ KM q m - 1
            + (sM q m - 1) * J0star q * PM q m + B0 q m a) * x := by
          have hdK : 1 ≤ dq q * q ^ KM q m := by omega
          have e : alphaM m + Qt q m n + dq q * q ^ KM q m - 1 + (sM q m - 1) * J0star q * PM q m
              + B0 q m a = alphaM m + (Qt q m n + (dq q * q ^ KM q m - 1
                + (sM q m - 1) * J0star q * PM q m + B0 q m a)) := by omega
          rw [e, Nat.pow_add 2 (alphaM m), Nat.pow_add 2 (Qt q m n), Nat.mul_assoc (2 ^ alphaM m)]
  · -- k₀ ≥ 1: left disjunct
    left
    rw [← hQt] at hle
    have h1 : q * Ys < q * (2 ^ Qt q m n * (ρ + q ^ n * (B + 1))) := by
      have : q * Ys + 1 ≤ 2 ^ Qt q m n * (q * (ρ + q ^ n * (B + 1))) := by rw [hrel]; exact hle
      rw [Nat.mul_left_comm] at this; omega
    have h2 := lt_of_mul_lt_mul_left' h1
    have hΘ : ρ + q ^ n * (B + 1) ≤ q ^ n * (B + MM q m + 1) := by
      have e : q ^ n * (B + MM q m + 1) = q ^ n * MM q m + q ^ n * (B + 1) := by
        simp only [Nat.mul_add, Nat.mul_one]; omega
      omega
    have h3 : q ^ n * w < q ^ n * (2 ^ (alphaM m + Qt q m n) * (B + MM q m + 1)) := by
      calc q ^ n * w ≤ 2 ^ alphaM m * Ys := hwle
        _ < 2 ^ alphaM m * (2 ^ Qt q m n * (ρ + q ^ n * (B + 1))) :=
            Nat.mul_lt_mul_of_pos_left h2 (Nat.pow_pos (by omega))
        _ ≤ 2 ^ alphaM m * (2 ^ Qt q m n * (q ^ n * (B + MM q m + 1))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hΘ)
        _ = q ^ n * (2 ^ (alphaM m + Qt q m n) * (B + MM q m + 1)) := by
            rw [Nat.pow_add]; simp only [Nat.mul_comm, Nat.mul_assoc]
    exact lt_of_mul_lt_mul_left' h3

end Collatz
