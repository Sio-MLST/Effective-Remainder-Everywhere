import Collatz.GeneralAStart

/-! Theorem A, Lemma 10 (perturbation) of generalAB.md, in the exact form
    q^{i+1} (y'_{k+i} − y_{k+i}) = 2^{a_k} 2^{S_i} y_{k−1} (2^{DP} − 1)
    for two shift sequences differing only at k by D > 0, plus integrality propagation and
    the per-prime divisibility of the differences. Choice-free. -/

namespace Collatz

/-- Exact perturbation identity (both paths integral). -/
theorem perturb_identity {q : Nat} (P : Nat) (y0 : Int) (b J J' : Nat → Nat) (k D T : Nat)
    (hk : 1 ≤ k) (hJ' : ∀ l, l ≠ k → J' l = J l) (hJk : J' k = J k + D)
    (hI : Integral (q : Int) P y0 b J T) (hI' : Integral (q : Int) P y0 b J' T) :
    ∀ i, k + i ≤ T →
      (q : Int) ^ (i + 1) * (chain (q : Int) P y0 b J' (k + i) - chain (q : Int) P y0 b J (k + i))
        = (2 : Int) ^ (b k + J k * P) * (2 : Int) ^ (asum (fun l => b (k + l) + J (k + l) * P) i)
          * chain (q : Int) P y0 b J (k - 1) * ((2 : Int) ^ (D * P) - 1)
  | 0, h => by
    have hk1 : k - 1 + 1 = k := by omega
    have r := chain_rel hI (k - 1) (by omega)
    have r' := chain_rel hI' (k - 1) (by omega)
    rw [hk1] at r r'
    have hc : chain (q : Int) P y0 b J' (k - 1) = chain (q : Int) P y0 b J (k - 1) :=
      (chain_congr (q : Int) P y0 b J J' (k - 1) (fun l _ h2 => (hJ' l (by omega)).symm)).symm
    rw [hc, hJk] at r'
    have e1 : (2 : Int) ^ ((J k + D) * P) = (2 : Int) ^ (J k * P) * (2 : Int) ^ (D * P) := by
      rw [Nat.add_mul, Int.pow_add]
    rw [e1] at r'
    have e2 : asum (fun l => b (k + l) + J (k + l) * P) 0 = 0 := rfl
    have this : (q : Int) * (chain (q : Int) P y0 b J' k - chain (q : Int) P y0 b J k)
        = ((q : Int) * chain (q : Int) P y0 b J' k + 1) - ((q : Int) * chain (q : Int) P y0 b J k + 1) := by
      int_ring
    have gf : (q : Int) * (chain (q : Int) P y0 b J' k - chain (q : Int) P y0 b J k)
        = (2 : Int) ^ (b k + J k * P) * (2 : Int) ^ 0 * chain (q : Int) P y0 b J (k - 1)
          * ((2 : Int) ^ (D * P) - 1) := by
      rw [this, r, r', Int.pow_zero, Int.pow_add]; int_ring
    rw [e2, ← gf, show k + 0 = k from rfl, Int.pow_one]
  | i + 1, h => by
    have ih := perturb_identity P y0 b J J' k D T hk hJ' hJk hI hI' i (by omega)
    have r := chain_rel hI (k + i) (by omega)
    have r' := chain_rel hI' (k + i) (by omega)
    have hne : k + i + 1 ≠ k := by omega
    rw [hJ' (k + i + 1) hne] at r'
    have e0 : k + (i + 1) = k + i + 1 := by omega
    rw [e0]
    have hS : asum (fun l => b (k + l) + J (k + l) * P) (i + 1)
        = asum (fun l => b (k + l) + J (k + l) * P) i + (b (k + i + 1) + J (k + i + 1) * P) := by
      show asum (fun l => b (k + l) + J (k + l) * P) i + (b (k + (i + 1)) + J (k + (i + 1)) * P) = _
      rw [e0]
    have key : (q : Int) * (chain (q : Int) P y0 b J' (k + i + 1) - chain (q : Int) P y0 b J (k + i + 1))
        = (2 : Int) ^ b (k + i + 1) * (2 : Int) ^ (J (k + i + 1) * P)
          * (chain (q : Int) P y0 b J' (k + i) - chain (q : Int) P y0 b J (k + i)) := by
      have : (q : Int) * (chain (q : Int) P y0 b J' (k + i + 1) - chain (q : Int) P y0 b J (k + i + 1))
          = ((q : Int) * chain (q : Int) P y0 b J' (k + i + 1) + 1)
            - ((q : Int) * chain (q : Int) P y0 b J (k + i + 1) + 1) := by int_ring
      rw [this, r, r']; int_ring
    calc (q : Int) ^ (i + 1 + 1) * (chain (q : Int) P y0 b J' (k + i + 1) - chain (q : Int) P y0 b J (k + i + 1))
        = (q : Int) ^ (i + 1) * ((q : Int) * (chain (q : Int) P y0 b J' (k + i + 1)
            - chain (q : Int) P y0 b J (k + i + 1))) := by rw [Int.pow_succ]; int_ring
      _ = (2 : Int) ^ b (k + i + 1) * (2 : Int) ^ (J (k + i + 1) * P) * ((q : Int) ^ (i + 1)
            * (chain (q : Int) P y0 b J' (k + i) - chain (q : Int) P y0 b J (k + i))) := by
          rw [key]; int_ring
      _ = _ := by rw [ih, hS, Int.pow_add (2 : Int) (asum _ i), Int.pow_add (2 : Int) (b (k + i + 1))]; int_ring

/-- Cancel a factor p^n: (p^n · p^E) ∣ p^n · X gives p^E ∣ X (Int). -/
theorem int_dvd_cancel_pow {p n E : Nat} (hp : 0 < p) {X : Int}
    (h : (((p ^ n * p ^ E : Nat)) : Int) ∣ ((p ^ n : Nat) : Int) * X) : ((p ^ E : Nat) : Int) ∣ X := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have hne : ((p ^ n : Nat) : Int) ≠ 0 := by
    have : 0 < p ^ n := Nat.pow_pos hp; omega
  apply Int.eq_of_mul_eq_mul_left hne
  rw [hc]; push_cast; int_ring

/-- From p^E ∣ q^{i+1} Z (Int) with v_p(q) = α and (i+1)α ≤ E, get p^{E − (i+1)α} ∣ Z. -/
theorem dvd_of_dvd_qpow {q p i E : Nat} (hq : 1 < q) (hp : IsPrime p) (hpq : p ∣ q)
    (hE : (i + 1) * vp p q ≤ E) {Z : Int}
    (h : ((p ^ E : Nat) : Int) ∣ (q : Int) ^ (i + 1) * Z) :
    ((p ^ (E - (i + 1) * vp p q) : Nat) : Int) ∣ Z := by
  have hv := val_pow hp (val_q hq hp hpq).1 (i + 1)
  obtain ⟨w, hw⟩ := hv.1
  have hpw : ¬ p ∣ w := fun hd => hv.2 (by
    obtain ⟨c, hc⟩ := hd; exact ⟨c, by rw [hw, hc, Nat.pow_succ, Nat.mul_assoc]⟩)
  have hcop : Nat.Coprime (p ^ (E - (i + 1) * vp p q)) w :=
    Nat.Coprime.pow_left _ (isPrime_coprime hp hpw)
  have hqI : (q : Int) ^ (i + 1) = ((p ^ ((i + 1) * vp p q) : Nat) : Int) * (w : Int) := by
    have : q ^ (i + 1) = p ^ ((i + 1) * vp p q) * w := hw
    exact_mod_cast this
  rw [hqI, Int.mul_assoc] at h
  have e : p ^ E = p ^ ((i + 1) * vp p q) * p ^ (E - (i + 1) * vp p q) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [e] at h
  have h2 := int_dvd_cancel_pow (show 0 < p by have := hp.1; omega) h
  exact int_cancel _ w (Nat.pow_pos (by have := hp.1; omega)) hcop Z h2

theorem vp_ge_of_dvd {p e D : Nat} (hp : 1 < p) (hD : 0 < D) (h : p ^ e ∣ D) : e ≤ vp p D := by
  have hv := val_vp hp hD
  match Nat.lt_or_ge (vp p D) e with
  | Or.inr hge => exact hge
  | Or.inl hlt => exact absurd (Nat.dvd_trans (Nat.pow_dvd_pow p hlt) h) hv.2

/-- Integrality at step k does not depend on the k-th shift. -/
theorem integral_prefix {q : Nat} {P : Nat} {y0 : Int} {b J J' : Nat → Nat} {k : Nat}
    (hP : (q : Int) ∣ (2 : Int) ^ P - 1) (hJ' : ∀ l, l ≠ k → J' l = J l)
    (hI : Integral (q : Int) P y0 b J k) : Integral (q : Int) P y0 b J' k := by
  intro i hi
  have hc : chain (q : Int) P y0 b J' i = chain (q : Int) P y0 b J i :=
    (chain_congr (q : Int) P y0 b J J' i (fun l _ h2 => (hJ' l (by omega)).symm)).symm
  rw [hc]
  have hG : ∀ j : Nat, (q : Int) ∣ (2 : Int) ^ (j * P) - 1 := fun j => pow_mod_one_int _ P j hP
  rw [step_int_iff _ _ _ _ _ (hG (J' (i + 1)))]
  exact (step_int_iff _ _ _ _ _ (hG (J (i + 1)))).mp (hI i hi)

theorem integral_le {p : Int} {P : Nat} {y0 : Int} {b J : Nat → Nat} {n n' : Nat}
    (h : Integral p P y0 b J n) (hn : n' ≤ n) : Integral p P y0 b J n' :=
  fun i hi => h i (by omega)

theorem q_dvd_LamA (q m : Nat) : q ∣ LamA q m :=
  Nat.dvd_trans (Nqq_dvd q) (by rw [LamA_eq]; exact Nat.dvd_mul_right _ _)

theorem q_dvd_pow2P {q m : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) :
    (q : Int) ∣ (2 : Int) ^ PM q m - 1 := by
  have h := Lam_dvd (m := m) hq hodd hm 1
  rw [Nat.one_mul] at h
  have e : ((2 ^ PM q m - 1 : Nat) : Int) = (2 : Int) ^ PM q m - 1 := by
    rw [Int.ofNat_sub Nat.one_le_two_pow]; push_cast; rfl
  rw [← e]; exact Int.ofNat_dvd.mpr (Nat.dvd_trans (q_dvd_LamA q m) h)

/-- q ∣ Z from p^{α_p} ∣ Z for all primes p ∣ q (Int). -/
theorem q_dvd_of_primes {q : Nat} (hq : 1 < q) {Z : Int}
    (h : ∀ p, IsPrime p → p ∣ q → ((p ^ vp p q : Nat) : Int) ∣ Z) : (q : Int) ∣ Z := by
  have hn : q ∣ Z.natAbs := dvd_of_val_le hq (by omega) (fun r _ hr => hr)
    (fun p hp hpq => Int.natAbs_dvd_natAbs.mpr (h p hp hpq))
  exact Int.natAbs_dvd_natAbs.mp (by rwa [Int.natAbs_natCast])

theorem int_step_transfer {q : Int} {A y y' : Int} (h : q ∣ y' - y) :
    q ∣ A * y - 1 → q ∣ A * y' - 1 := by
  intro h1
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, hd⟩ := h1
  exact ⟨d + A * c, by rw [Int.mul_add, ← hd, ← Int.mul_assoc, Int.mul_comm q A, Int.mul_assoc, ← hc]; int_ring⟩

/-- Lemma 10 (perturbation): integrality transfers and the differences have the predicted
    p-adic divisibility, for every prime p ∣ q. -/
theorem perturb {q m : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) {y0 : Int}
    {b J J' : Nat → Nat} {k D T : Nat} (hk : 1 ≤ k) (hkT : k ≤ T)
    (hJ' : ∀ l, l ≠ k → J' l = J l) (hJk : J' k = J k + D) (hD : 0 < D) (ef : Nat → Nat)
    (hef : ∀ p, IsPrime p → p ∣ q → p ^ ef p ∣ D)
    (hlev : ∀ p, IsPrime p → p ∣ q →
      (T - k + 1) * vp p q ≤ (KM q m + 1) * vp p q + vp p (uu q) + ef p)
    (hI : Integral (q : Int) (PM q m) y0 b J T ∨ Integral (q : Int) (PM q m) y0 b J' T) :
    Integral (q : Int) (PM q m) y0 b J T ∧ Integral (q : Int) (PM q m) y0 b J' T ∧
      ∀ i, k + i ≤ T → ∀ p, IsPrime p → p ∣ q →
        ((p ^ ((KM q m + 1) * vp p q + vp p (uu q) + ef p - (i + 1) * vp p q) : Nat) : Int) ∣
          chain (q : Int) (PM q m) y0 b J' (k + i) - chain (q : Int) (PM q m) y0 b J (k + i) := by
  have hP := q_dvd_pow2P hq hodd hm
  have hJsym : ∀ l, l ≠ k → J l = J' l := fun l h => (hJ' l h).symm
  -- divisibility from the identity, given both integral up to k + i
  have hdivR : ∀ i, k + i ≤ T → Integral (q : Int) (PM q m) y0 b J (k + i) →
      Integral (q : Int) (PM q m) y0 b J' (k + i) → ∀ p, IsPrime p → p ∣ q →
        ((p ^ ((KM q m + 1) * vp p q + vp p (uu q) + ef p - (i + 1) * vp p q) : Nat) : Int) ∣
          chain (q : Int) (PM q m) y0 b J' (k + i) - chain (q : Int) (PM q m) y0 b J (k + i) := by
    intro i hi hIi hI'i p hp hpq
    have hid := perturb_identity (PM q m) y0 b J J' k D (k + i) hk hJ' hJk hIi hI'i i (Nat.le_refl _)
    have hv := val_2PN (m := m) (N := D) hq hodd hm hp hpq hD
    have hge := vp_ge_of_dvd hp.1 hD (hef p hp hpq)
    have h1 : p ^ ((KM q m + 1) * vp p q + vp p (uu q) + ef p) ∣ 2 ^ (D * PM q m) - 1 :=
      Nat.dvd_trans (Nat.pow_dvd_pow p (by omega)) hv.1
    have h1I : ((p ^ ((KM q m + 1) * vp p q + vp p (uu q) + ef p) : Nat) : Int) ∣ (2 : Int) ^ (D * PM q m) - 1 := by
      have e : ((2 ^ (D * PM q m) - 1 : Nat) : Int) = (2 : Int) ^ (D * PM q m) - 1 := by
        rw [Int.ofNat_sub Nat.one_le_two_pow]; push_cast; rfl
      rw [← e]; exact Int.ofNat_dvd.mpr h1
    have h2 : ((p ^ ((KM q m + 1) * vp p q + vp p (uu q) + ef p) : Nat) : Int) ∣
        (q : Int) ^ (i + 1) * (chain (q : Int) (PM q m) y0 b J' (k + i) - chain (q : Int) (PM q m) y0 b J (k + i)) := by
      rw [hid]; exact Int.dvd_trans h1I (Int.dvd_mul_left _ _)
    have hl1 := hlev p hp hpq
    have hl2 : (i + 1) * vp p q ≤ (T - k + 1) * vp p q := Nat.mul_le_mul_right _ (by omega)
    exact dvd_of_dvd_qpow hq hp hpq (by omega) h2
  -- induction on the delay
  have main : ∀ i, k + i ≤ T → Integral (q : Int) (PM q m) y0 b J (k + i) ∧
      Integral (q : Int) (PM q m) y0 b J' (k + i) := by
    intro i
    induction i with
    | zero =>
      intro h
      rcases hI with hI | hI
      · exact ⟨integral_le hI h, integral_prefix hP hJ' (integral_le hI h)⟩
      · exact ⟨integral_prefix hP hJsym (integral_le hI h), integral_le hI h⟩
    | succ i ih =>
      intro h
      obtain ⟨hIi, hI'i⟩ := ih (by omega)
      have hd := hdivR i (by omega) hIi hI'i
      have hqd : (q : Int) ∣ chain (q : Int) (PM q m) y0 b J' (k + i) - chain (q : Int) (PM q m) y0 b J (k + i) :=
        q_dvd_of_primes hq (fun p hp hpq => by
          have h' := hd p hp hpq
          have hlv := hlev p hp hpq
          have hle : vp p q ≤ (KM q m + 1) * vp p q + vp p (uu q) + ef p - (i + 1) * vp p q := by
            have h1 : (i + 2) * vp p q ≤ (T - k + 1) * vp p q := Nat.mul_le_mul_right _ (by omega)
            have h2 : (i + 2) * vp p q = (i + 1) * vp p q + vp p q := Nat.succ_mul _ _
            omega
          exact Int.dvd_trans (Int.ofNat_dvd.mpr (Nat.pow_dvd_pow p hle)) h')
      have hne : k + i + 1 ≠ k := by omega
      have e : k + (i + 1) = k + i + 1 := by omega
      rw [e]
      rcases hI with hI | hI
      · refine ⟨integral_le hI (by omega), fun j hj => ?_⟩
        rcases Nat.lt_or_ge j (k + i) with hj1 | hj1
        · exact hI'i j hj1
        · have hj2 : j = k + i := by omega
          subst hj2
          rw [hJ' (k + i + 1) hne]
          exact int_step_transfer hqd (hI (k + i) (by omega))
      · refine ⟨fun j hj => ?_, integral_le hI (by omega)⟩
        rcases Nat.lt_or_ge j (k + i) with hj1 | hj1
        · exact hIi j hj1
        · have hj2 : j = k + i := by omega
          subst hj2
          have h3 := hI (k + i) (by omega)
          rw [hJ' (k + i + 1) hne] at h3
          have hqd' : (q : Int) ∣ chain (q : Int) (PM q m) y0 b J (k + i) - chain (q : Int) (PM q m) y0 b J' (k + i) := by
            obtain ⟨c, hc⟩ := hqd; exact ⟨-c, by rw [Int.mul_neg, ← hc]; int_ring⟩
          exact int_step_transfer hqd' h3
  have hT := main (T - k) (by omega)
  rw [show k + (T - k) = T by omega] at hT
  exact ⟨hT.1, hT.2, fun i hi => hdivR i hi (integral_le hT.1 hi) (integral_le hT.2 hi)⟩

/-- Exactness at one prime p₀ (with v_{p₀}(D) = e exactly). -/
theorem perturb_exact {q m : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) {y0 : Int}
    {b J J' : Nat → Nat} {k D T : Nat} (hk : 1 ≤ k) (hkT : k ≤ T)
    (hJ' : ∀ l, l ≠ k → J' l = J l) (hJk : J' k = J k + D) (hD : 0 < D)
    (hI : Integral (q : Int) (PM q m) y0 b J T) (hI' : Integral (q : Int) (PM q m) y0 b J' T)
    {p e i : Nat} (hp : IsPrime p) (hpq : p ∣ q) (hpe : p ^ e ∣ D) (hpe1 : ¬ p ^ (e + 1) ∣ D)
    (hi : k + i ≤ T) (hiE : (i + 1) * vp p q ≤ (KM q m + 1) * vp p q + vp p (uu q) + e) :
    ¬ ((p ^ ((KM q m + 1) * vp p q + vp p (uu q) + e - (i + 1) * vp p q + 1) : Nat) : Int) ∣
      chain (q : Int) (PM q m) y0 b J' (k + i) - chain (q : Int) (PM q m) y0 b J (k + i) := by
  intro hdiv
  have hid := perturb_identity (PM q m) y0 b J J' k D T hk hJ' hJk hI hI' i hi
  have hve : vp p D = e := val_unique (val_vp hp.1 hD) ⟨hpe, hpe1⟩
  have hv := val_2PN (m := m) (N := D) hq hodd hm hp hpq hD
  rw [hve] at hv
  generalize hE : (KM q m + 1) * vp p q + vp p (uu q) + e = E at hv hdiv hiE
  -- p^{E+1} ∣ q^{i+1} Δ
  have hvq := val_pow hp (val_q hq hp hpq).1 (i + 1)
  have hqI : ((p ^ ((i + 1) * vp p q) : Nat) : Int) ∣ (q : Int) ^ (i + 1) := by
    have h := Int.ofNat_dvd.mpr hvq.1; push_cast at h ⊢; exact h
  have h1 : ((p ^ (E + 1) : Nat) : Int) ∣ (q : Int) ^ (i + 1) *
      (chain (q : Int) (PM q m) y0 b J' (k + i) - chain (q : Int) (PM q m) y0 b J (k + i)) := by
    have e1 : p ^ (E + 1) = p ^ ((i + 1) * vp p q) * p ^ (E - (i + 1) * vp p q + 1) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [e1]; push_cast
    exact Int.mul_dvd_mul (by push_cast at hqI; exact hqI) (by push_cast at hdiv; exact hdiv)
  rw [hid] at h1
  -- the unit factor
  have hk1 := hI (k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at hk1
  generalize hY : chain (q : Int) (PM q m) y0 b J (k - 1) = Y at hk1 h1
  have hpY : ¬ p ∣ Y.natAbs := by
    intro h
    have h2 : (p : Int) ∣ (2 : Int) ^ b k * 2 ^ (J k * PM q m) * Y :=
      Int.dvd_trans (Int.natAbs_dvd_natAbs.mp (by rwa [Int.natAbs_natCast])) (Int.dvd_mul_left _ _)
    have h3 : (p : Int) ∣ (2 : Int) ^ b k * 2 ^ (J k * PM q m) * Y - 1 :=
      Int.dvd_trans (Int.ofNat_dvd.mpr hpq) hk1
    have h4 : (p : Int) ∣ 1 := by
      have := Int.dvd_sub h2 h3
      rwa [show (2 : Int) ^ b k * 2 ^ (J k * PM q m) * Y - ((2 : Int) ^ b k * 2 ^ (J k * PM q m) * Y - 1) = 1
        by omega] at this
    have := Int.eq_one_of_dvd_one (by omega) h4
    have := hp.1; omega
  have hp2 : ¬ p ∣ 2 := fun h => by
    have := Nat.le_of_dvd (by omega) h
    have := hp.1
    have hp2 : p = 2 := by omega
    rw [hp2] at hpq; obtain ⟨c, hc⟩ := hpq; omega
  have hU : ¬ p ∣ (2 ^ (b k + J k * PM q m) * 2 ^ (asum (fun l => b (k + l) + J (k + l) * PM q m) i)
      * Y.natAbs) := by
    intro h
    rcases isPrime_dvd_mul hp h with h | h
    · rcases isPrime_dvd_mul hp h with h | h
      · exact hp2 (isPrime_dvd_pow hp _ h)
      · exact hp2 (isPrime_dvd_pow hp _ h)
    · exact hpY h
  have hN : p ^ (E + 1) ∣ (2 ^ (b k + J k * PM q m) * 2 ^ (asum (fun l => b (k + l) + J (k + l) * PM q m) i)
      * Y.natAbs) * (2 ^ (D * PM q m) - 1) := by
    have h2 := Int.natAbs_dvd_natAbs.mpr h1
    rw [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow,
      Int.natAbs_pow] at h2
    have e3 : ((2 : Int) ^ (D * PM q m) - 1).natAbs = 2 ^ (D * PM q m) - 1 := by
      have : ((2 : Int) ^ (D * PM q m) - 1) = ((2 ^ (D * PM q m) - 1 : Nat) : Int) := by
        rw [Int.ofNat_sub Nat.one_le_two_pow]; push_cast; rfl
      rw [this, Int.natAbs_natCast]
    rw [e3] at h2
    exact h2
  have hcop : Nat.Coprime (p ^ (E + 1)) (2 ^ (b k + J k * PM q m) *
      2 ^ (asum (fun l => b (k + l) + J (k + l) * PM q m) i) * Y.natAbs) :=
    Nat.Coprime.pow_left _ (isPrime_coprime hp hU)
  exact hv.2 (hcop.dvd_of_dvd_mul_left hN)

end Collatz
