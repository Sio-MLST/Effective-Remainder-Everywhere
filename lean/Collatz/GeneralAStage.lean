import Collatz.GeneralAOp

/-! Theorem A, Lemma 12 for κ ≥ 1: per-prime primer, digit controllers, the intermediate
    stages T = K+1, …, s−1, the final stage T = s, and the assembly. Choice-free. -/

namespace Collatz

/-- ν_p ≤ κ α_p. -/
theorem nu_le_kappa {q p : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hp : IsPrime p) (hpq : p ∣ q) :
    vp p (uu q) ≤ κq q * vp p q := by
  have hU := val_uq hq hodd hp hpq
  have h1 : p ^ vp p (uu q) ∣ q ^ κq q := Nat.dvd_trans hU.1 (kappaQ_spec q (uu q)).1
  have hv := val_pow hp (val_q hq hp hpq).1 (κq q)
  have h2 := vp_ge_of_dvd hp.1 (Nat.pow_pos (by omega)) h1
  rw [val_unique (val_vp hp.1 (Nat.pow_pos (by omega))) hv] at h2
  exact h2

/-- κ-minimality: if ν_p ≤ k·α_p for every prime p ∣ q, then κ ≤ k. Together with
    `nu_le_kappa` this gives κ = max_{p ∣ q} ⌈ν_p / α_p⌉ (generalAB.md, Section 1). -/
theorem kappa_le_of_nu_le {q k : Nat} (hq : 1 < q) (hodd : q % 2 = 1)
    (h : ∀ p, IsPrime p → p ∣ q → vp p (uu q) ≤ k * vp p q) : κq q ≤ k := by
  have hdvd : uqq q ∣ q ^ k := by
    refine dvd_of_val_le hq (uqq_pos hq hodd)
      (fun r hr hrU => isPrime_dvd_pow hr _ (Nat.dvd_trans hrU (uq_dvd_pow q (uu q)))) ?_
    intro p hp hpq
    rw [val_unique (val_vp hp.1 (uqq_pos hq hodd)) (val_uq hq hodd hp hpq)]
    exact Nat.dvd_trans (Nat.pow_dvd_pow p (h p hp hpq)) (val_pow hp (val_q hq hp hpq).1 k).1
  match Nat.lt_or_ge k (κq q) with
  | Or.inl hlt => exact absurd hdvd ((kappaQ_spec q (uu q)).2 k hlt)
  | Or.inr hge => exact hge

/-- The controller of a digit h < α: δ and v with v < α, h + δα = ν + v, δ ≤ κ. -/
theorem controller {α ν κ h : Nat} (hα : 1 ≤ α) (hh : h < α) (hν : ν ≤ κ * α) :
    ∃ δ v, v < α ∧ h + δ * α = ν + v ∧ δ ≤ κ := by
  have hd := Nat.div_add_mod (ν + α - 1 - h) α
  have hm := Nat.mod_lt (ν + α - 1 - h) (show 0 < α by omega)
  generalize (ν + α - 1 - h) / α = δ at hd
  generalize (ν + α - 1 - h) % α = r at hd hm
  have e : α * δ = δ * α := Nat.mul_comm _ _
  refine ⟨δ, h + δ * α - ν, by omega, by omega, ?_⟩
  match Nat.lt_or_ge κ δ with
  | Or.inr h' => exact h'
  | Or.inl h' =>
    exfalso
    have : (κ + 1) * α ≤ δ * α := Nat.mul_le_mul_right _ h'
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

/-- Per-prime primer: with b_l = a for l ≤ K+κ+1, y_l ≡ c_* (mod p^{(K+1)α+ν−lα}). -/
theorem primer_p {q m a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) {c y0 : Int}
    (hc : (LamA q m : Int) ∣ ((2 : Int) ^ a - q) * c - 1) (hy0 : (LamA q m : Int) ∣ y0 - c)
    {b J : Nat → Nat} (hbK : ∀ l, 1 ≤ l → l ≤ KM q m + κq q + 1 → b l = a)
    {p : Nat} (hp : IsPrime p) (hpq : p ∣ q) :
    ∀ l, l ≤ KM q m + κq q + 1 → Integral (q : Int) (PM q m) y0 b J l →
      ((p ^ ((KM q m + 1) * vp p q + vp p (uu q) - l * vp p q) : Nat) : Int) ∣
        chain (q : Int) (PM q m) y0 b J l - c
  | 0, _, _ => by
    have hv := val_qkU (k := KM q m + 1) hq hodd hp hpq
    rw [Nat.zero_mul, Nat.sub_zero]
    exact Int.dvd_trans (Int.ofNat_dvd.mpr hv.1) hy0
  | l + 1, hl, hI => by
    have ih := primer_p hq hodd hm hc hy0 hbK hp hpq l (by omega) (integral_le hI (by omega))
    obtain ⟨E, hE⟩ : ∃ E, E = (KM q m + 1) * vp p q + vp p (uu q) - l * vp p q := ⟨_, rfl⟩
    rw [← hE] at ih
    have hE1 : (KM q m + 1) * vp p q + vp p (uu q) - (l + 1) * vp p q = E - vp p q := by
      have h3 : (l + 1) * vp p q = l * vp p q + vp p q := by rw [Nat.add_mul, Nat.one_mul]
      rw [h3, hE]; omega
    rw [hE1]
    match Nat.lt_or_ge E (vp p q) with
    | Or.inl hlt =>
      rw [show E - vp p q = 0 by omega, Nat.pow_zero]; exact Int.one_dvd _
    | Or.inr hge =>
      have hEL : p ^ E ∣ LamA q m := by
        have hv := val_qkU (k := KM q m + 1) hq hodd hp hpq
        exact Nat.dvd_trans (Nat.pow_dvd_pow p (by omega)) hv.1
      have hELI : ((p ^ E : Nat) : Int) ∣ (LamA q m : Int) := Int.ofNat_dvd.mpr hEL
      have r := chain_rel hI l (by omega)
      rw [hbK (l + 1) (by omega) hl] at r
      have hG : (LamA q m : Int) ∣ (2 : Int) ^ (J (l + 1) * PM q m) - 1 := by
        have := Lam_dvd (m := m) hq hodd hm (J (l + 1))
        have e : ((2 ^ (J (l + 1) * PM q m) - 1 : Nat) : Int) = (2 : Int) ^ (J (l + 1) * PM q m) - 1 := by
          rw [Int.ofNat_sub Nat.one_le_two_pow]; push_cast; rfl
        rw [← e]; exact Int.ofNat_dvd.mpr this
      generalize chain (q : Int) (PM q m) y0 b J l = y at ih r
      generalize (2 : Int) ^ (J (l + 1) * PM q m) = G at hG r
      have hX : ((p ^ E : Nat) : Int) ∣ (q : Int) ^ (0 + 1) * (chain (q : Int) (PM q m) y0 b J (l + 1) - c) := by
        have e : (q : Int) ^ (0 + 1) * (chain (q : Int) (PM q m) y0 b J (l + 1) - c)
            = (2 : Int) ^ a * y * (G - 1) + (2 : Int) ^ a * (y - c) + (((2 : Int) ^ a - q) * c - 1) := by
          have hY : (q : Int) * chain (q : Int) (PM q m) y0 b J (l + 1) = (2 : Int) ^ a * G * y - 1 := by
            omega
          rw [Nat.zero_add, Int.pow_one, Int.mul_sub, hY]; int_ring
        rw [e]
        exact Int.dvd_add (Int.dvd_add (Int.dvd_trans (Int.dvd_trans hELI hG) (Int.dvd_mul_left _ _))
          (Int.dvd_trans ih (Int.dvd_mul_left _ _))) (Int.dvd_trans hELI hc)
      have := dvd_of_dvd_qpow hq hp hpq (i := 0) (by omega) hX
      rwa [Nat.zero_add, Nat.one_mul] at this

theorem two_pow_not_dvd {p : Nat} (hp : IsPrime p) (hpo : p % 2 = 1) (e : Nat) :
    ¬ (p : Int) ∣ (2 : Int) ^ e := by
  intro h
  have h1 : p ∣ 2 ^ e := by
    have := Int.natAbs_dvd_natAbs.mpr h
    rwa [Int.natAbs_natCast, Int.natAbs_pow] at this
  have h2 := isPrime_dvd_pow hp e h1
  have := Nat.le_of_dvd (by omega) h2
  have := hp.1
  omega

theorem prime_odd_of_q {q p : Nat} (hodd : q % 2 = 1) (hpq : p ∣ q) : p % 2 = 1 :=
  odd_of_dvd_odd hpq hodd

/-- One prime of an intermediate stage T: fix all α_p digits of 2^{b_{T+1}} y_T − 1 at p. -/
theorem stage_prime {q m a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) {c y0 : Int}
    (hc : (LamA q m : Int) ∣ ((2 : Int) ^ a - q) * c - 1) (hy0 : (LamA q m : Int) ∣ y0 - c)
    {b : Nat → Nat} (hbK : ∀ l, 1 ≤ l → l ≤ KM q m + κq q + 1 → b l = a)
    {T : Nat} (hT1 : KM q m + 1 ≤ T) (L : List Nat) (hLsub : ∀ r ∈ L, r ∈ qprimes q)
    {p : Nat} (hpL : p ∈ qprimes q) (hpnot : p ∉ L) :
    ∀ h, h ≤ αp q p → ∀ β : Nat → Nat → Nat, (∀ l, ∀ r ∈ qprimes q, β l r < r ^ αp q r) →
      Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β l)) T →
      (∀ r ∈ L, ((r ^ αp q r : Nat) : Int) ∣ (2 : Int) ^ b (T + 1) *
        chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β l)) T - 1) →
      ∃ β' : Nat → Nat → Nat, (∀ l, ∀ r ∈ qprimes q, β' l r < r ^ αp q r) ∧
        (∀ l, T - KM q m < l → β' l = β l) ∧
        Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β' l)) T ∧
        (∀ r ∈ L, ((r ^ αp q r : Nat) : Int) ∣ (2 : Int) ^ b (T + 1) *
          chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β' l)) T - 1) ∧
        ((p ^ h : Nat) : Int) ∣ (2 : Int) ^ b (T + 1) *
          chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β' l)) T - 1
  | 0, _, β, hβ, hI, hL => ⟨β, hβ, fun _ _ => rfl, hI, hL, by rw [Nat.pow_zero]; exact Int.one_dvd _⟩
  | h + 1, hh, β, hβ, hI, hL => by
    obtain ⟨β1, hβ1, hun1, hI1, hL1, hp1⟩ :=
      stage_prime hq hodd hm hc hy0 hbK hT1 L hLsub hpL hpnot h (by omega) β hβ hI hL
    have hpp := (mem_qprimes (show 1 ≤ q by omega)).mp hpL
    have hα1 : 1 ≤ αp q p := one_le_vp hpp.1.1 (by omega) hpp.2
    have hν := nu_le_kappa hq hodd hpp.1 hpp.2
    obtain ⟨δ, v, hv, hδv, hδκ⟩ := controller (h := h) hα1 (by omega) hν
    have hαe : αp q p = vp p q := rfl
    have hνe : νp q p = vp p (uu q) := rfl
    have hδe : δ * αp q p = δ * vp p q := by rw [hαe]
    match Nat.lt_or_ge (KM q m + δ) T with
    | Or.inr hle =>
      -- automatic digit (primer)
      refine ⟨β1, hβ1, hun1, hI1, hL1, ?_⟩
      have hbT : b (T + 1) = a := hbK (T + 1) (by omega) (by omega)
      rw [hbT]
      have hpr := primer_p hq hodd hm hc hy0 hbK hpp.1 hpp.2 T (by omega) hI1
      have hlev : h + 1 ≤ (KM q m + 1) * vp p q + vp p (uu q) - T * vp p q := by
        have h1 : T * vp p q ≤ (KM q m + δ) * vp p q := Nat.mul_le_mul_right _ hle
        have h2 : (KM q m + δ) * vp p q = KM q m * vp p q + δ * vp p q := Nat.add_mul _ _ _
        have h3 : (KM q m + 1) * vp p q = KM q m * vp p q + vp p q := by rw [Nat.add_mul, Nat.one_mul]
        omega
      have hpr' := Int.dvd_trans (Int.ofNat_dvd.mpr (Nat.pow_dvd_pow p hlev)) hpr
      have hac : ((p ^ (h + 1) : Nat) : Int) ∣ (2 : Int) ^ a * c - 1 := by
        have h1 : ((p ^ (h + 1) : Nat) : Int) ∣ (q : Int) := by
          apply Int.ofNat_dvd.mpr
          exact Nat.dvd_trans (Nat.pow_dvd_pow p (by unfold αp at hh; omega)) (val_q hq hpp.1 hpp.2).1.1
        have h2 : ((p ^ (h + 1) : Nat) : Int) ∣ (LamA q m : Int) := Int.dvd_trans h1 (Int.ofNat_dvd.mpr (q_dvd_LamA q m))
        have e : (2 : Int) ^ a * c - 1 = (((2 : Int) ^ a - q) * c - 1) + (q : Int) * c := by int_ring
        rw [e]; exact Int.dvd_add (Int.dvd_trans h2 hc) (Int.dvd_trans h1 (Int.dvd_mul_right _ _))
      have e : (2 : Int) ^ a * chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β1 l)) T - 1
          = (2 : Int) ^ a * (chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β1 l)) T - c)
            + ((2 : Int) ^ a * c - 1) := by int_ring
      rw [e]
      exact Int.dvd_add (Int.dvd_trans hpr' (Int.dvd_mul_left _ _)) hac
    | Or.inl hlt =>
      -- steered digit via the controller (k, v), k = T − K − δ
      have hk : 1 ≤ T - (KM q m + δ) := by omega
      have hTk : T - (T - (KM q m + δ)) = KM q m + δ := by omega
      have hlv : (T - (T - (KM q m + δ)) + 1) * αp q p ≤ (KM q m + 1) * αp q p + νp q p + v := by
        rw [hTk, show KM q m + δ + 1 = (KM q m + 1) + δ by omega, Nat.add_mul (KM q m + 1) δ]
        try simp only [αp, νp] at hδv hv ⊢
        omega
      have hexp : (KM q m + 1) * αp q p + νp q p + v - (T - (T - (KM q m + δ)) + 1) * αp q p = h := by
        rw [hTk, show KM q m + δ + 1 = (KM q m + 1) + δ by omega, Nat.add_mul (KM q m + 1) δ]
        try simp only [αp, νp] at hδv hv ⊢
        omega
      have hcur : ((p ^ ((KM q m + 1) * αp q p + νp q p + v - (T - (T - (KM q m + δ)) + 1) * αp q p) : Nat) : Int) ∣
          (2 : Int) ^ b (T + 1) * chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β1 l)) T - 1 := by
        rw [hexp]; exact hp1
      obtain ⟨D, _, hbD, hID, hnew, hpres⟩ := op_digit hq hodd hm β1 hβ1 hk (by omega) (by omega)
        hI1 hpL hv hlv (two_pow_not_dvd hpp.1 (prime_odd_of_q hodd hpp.2) _) hcur
      rw [hexp] at hnew
      refine ⟨setD β1 (T - (KM q m + δ)) p v D, hbD, fun l hl => ?_, hID, fun r hr => ?_, hnew⟩
      · rw [setD_ne β1 (by omega)]; exact hun1 l hl
      · -- preservation at the other primes of L
        have hrp : r ≠ p := fun e => hpnot (e ▸ hr)
        have hrr := (mem_qprimes (show 1 ≤ q by omega)).mp (hLsub r hr)
        have hpr := hpres (T - (T - (KM q m + δ))) (by omega) r hrr.1 hrr.2
        simp only [hrp, ↓reduceIte] at hpr
        rw [show T - (KM q m + δ) + (T - (T - (KM q m + δ))) = T by omega, hTk] at hpr
        have hlvr : vp r q ≤ (KM q m + 1) * vp r q + vp r (uu q) + Xp q r - (KM q m + δ + 1) * vp r q := by
          have h1 := Xp_ge q r
          unfold αp νp at h1
          have h2 : (δ + 1) * vp r q ≤ (κq q + 1) * vp r q := Nat.mul_le_mul_right _ (by omega)
          have h3 : (KM q m + δ + 1) * vp r q = KM q m * vp r q + (δ + 1) * vp r q := by
            rw [show KM q m + δ + 1 = KM q m + (δ + 1) by omega, Nat.add_mul]
          have h4 : (KM q m + 1) * vp r q = KM q m * vp r q + vp r q := by rw [Nat.add_mul, Nat.one_mul]
          omega
        have hpr' := Int.dvd_trans (Int.ofNat_dvd.mpr (Nat.pow_dvd_pow r hlvr)) hpr
        have hold := hL1 r hr
        have e : (2 : Int) ^ b (T + 1) * chain (q : Int) (PM q m) y0 b
              (fun l => jsumL q (qprimes q) (setD β1 (T - (KM q m + δ)) p v D l)) T - 1
            = (2 : Int) ^ b (T + 1) * (chain (q : Int) (PM q m) y0 b
              (fun l => jsumL q (qprimes q) (setD β1 (T - (KM q m + δ)) p v D l)) T
              - chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β1 l)) T)
              + ((2 : Int) ^ b (T + 1) * chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β1 l)) T - 1) := by
          int_ring
        rw [e]
        exact Int.dvd_add (Int.dvd_trans hpr' (Int.dvd_mul_left _ _)) hold

/-- An intermediate stage T: make step T + 1 integral. -/
theorem stage_mid {q m a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) {c y0 : Int}
    (hc : (LamA q m : Int) ∣ ((2 : Int) ^ a - q) * c - 1) (hy0 : (LamA q m : Int) ∣ y0 - c)
    {b : Nat → Nat} (hbK : ∀ l, 1 ≤ l → l ≤ KM q m + κq q + 1 → b l = a)
    {T : Nat} (hT1 : KM q m + 1 ≤ T) (β : Nat → Nat → Nat)
    (hβ : ∀ l, ∀ r ∈ qprimes q, β l r < r ^ αp q r)
    (hI : Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β l)) T) :
    ∃ β' : Nat → Nat → Nat, (∀ l, ∀ r ∈ qprimes q, β' l r < r ^ αp q r) ∧
      (∀ l, T - KM q m < l → β' l = β l) ∧
      Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β' l)) (T + 1) := by
  have key : ∀ L : List Nat, L.Nodup → (∀ r ∈ L, r ∈ qprimes q) →
      ∃ β' : Nat → Nat → Nat, (∀ l, ∀ r ∈ qprimes q, β' l r < r ^ αp q r) ∧
        (∀ l, T - KM q m < l → β' l = β l) ∧
        Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β' l)) T ∧
        (∀ r ∈ L, ((r ^ αp q r : Nat) : Int) ∣ (2 : Int) ^ b (T + 1) *
          chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β' l)) T - 1) := by
    intro L
    induction L with
    | nil => intro _ _; exact ⟨β, hβ, fun _ _ => rfl, hI, fun r hr => absurd hr List.not_mem_nil⟩
    | cons p L ih =>
      intro hnd hsub
      have hnd' := List.nodup_cons.mp hnd
      obtain ⟨β1, hβ1, hun1, hI1, hL1⟩ := ih hnd'.2 (fun r hr => hsub r (List.mem_cons_of_mem _ hr))
      obtain ⟨β2, hβ2, hun2, hI2, hL2, hp2⟩ := stage_prime hq hodd hm hc hy0 hbK hT1 L
        (fun r hr => hsub r (List.mem_cons_of_mem _ hr)) (hsub p (List.mem_cons_self ..)) hnd'.1
        (αp q p) (Nat.le_refl _) β1 hβ1 hI1 hL1
      refine ⟨β2, hβ2, fun l hl => (hun2 l hl).trans (hun1 l hl), hI2, fun r hr => ?_⟩
      rcases List.mem_cons.mp hr with h | h
      · subst h; exact hp2
      · exact hL2 r h
  obtain ⟨β', hβ', hun, hI', hall⟩ := key (qprimes q) (qprimes_nodup q) (fun r hr => hr)
  refine ⟨β', hβ', hun, fun i hi => ?_⟩
  rcases Nat.lt_or_ge i T with h | h
  · exact hI' i h
  · have : i = T := by omega
    subst this
    have hq' : (q : Int) ∣ (2 : Int) ^ b (i + 1) *
        chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β' l)) i - 1 :=
      q_dvd_of_primes hq (fun p hp hpq => hall p ((mem_qprimes (show 1 ≤ q by omega)).mpr ⟨hp, hpq⟩))
    have hG : ∀ j : Nat, (q : Int) ∣ (2 : Int) ^ (j * PM q m) - 1 :=
      fun j => pow_mod_one_int _ _ j (q_dvd_pow2P hq hodd hm)
    exact (step_int_iff _ _ _ _ _ (hG _)).mpr hq'

/-- Final stage, one prime p at step k: raise the p-level of y_s − ρ from F_p(k) to F_p(k+1),
    keeping the levels of the other primes (bounded by F_r(k+1)). -/
theorem final_prime {q m : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) {y0 ρ : Int}
    {b : Nat → Nat} {s k : Nat} (hk1 : 1 ≤ k) (hks : k + 1 ≤ s) {p : Nat} (hpL : p ∈ qprimes q)
    (H : Nat → Nat) (hH : ∀ r, H r ≤ (KM q m + 1) * αp q r + νp q r - (s - k) * αp q r) :
    ∀ v, v ≤ αp q p → ∀ β : Nat → Nat → Nat, (∀ l, ∀ r ∈ qprimes q, β l r < r ^ αp q r) →
      Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β l)) s →
      (∀ r ∈ qprimes q, r ≠ p → ((r ^ H r : Nat) : Int) ∣
        chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β l)) s - ρ) →
      ((p ^ ((KM q m + 1) * αp q p + νp q p - (s - k + 1) * αp q p) : Nat) : Int) ∣
        chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β l)) s - ρ →
      ∃ β' : Nat → Nat → Nat, (∀ l, ∀ r ∈ qprimes q, β' l r < r ^ αp q r) ∧
        (∀ l, l ≠ k → β' l = β l) ∧
        Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β' l)) s ∧
        (∀ r ∈ qprimes q, r ≠ p → ((r ^ H r : Nat) : Int) ∣
          chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β' l)) s - ρ) ∧
        ((p ^ ((KM q m + 1) * αp q p + νp q p + v - (s - k + 1) * αp q p) : Nat) : Int) ∣
          chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β' l)) s - ρ
  | 0, _, β, hβ, hI, hO, hP => ⟨β, hβ, fun _ _ => rfl, hI, hO, by rw [Nat.add_zero]; exact hP⟩
  | v + 1, hv, β, hβ, hI, hO, hP => by
    obtain ⟨β1, hβ1, hun1, hI1, hO1, hP1⟩ :=
      final_prime hq hodd hm hk1 hks hpL H hH v (by omega) β hβ hI hO hP
    have hpp := (mem_qprimes (show 1 ≤ q by omega)).mp hpL
    have hαe : αp q p = vp p q := rfl
    have hνe : νp q p = vp p (uu q) := rfl
    match Nat.lt_or_ge ((KM q m + 1) * αp q p + νp q p + v) ((s - k + 1) * αp q p) with
    | Or.inl hlt =>
      refine ⟨β1, hβ1, hun1, hI1, hO1, ?_⟩
      rw [show (KM q m + 1) * αp q p + νp q p + (v + 1) - (s - k + 1) * αp q p = 0 by omega,
        Nat.pow_zero]
      exact Int.one_dvd _
    | Or.inr hge =>
      -- s − k ≤ K + κ follows from the level inequality
      have hν := nu_le_kappa hq hodd hpp.1 hpp.2
      have hTk : s - k ≤ KM q m + κq q := by
        match Nat.lt_or_ge (KM q m + κq q) (s - k) with
        | Or.inr h => exact h
        | Or.inl h =>
          exfalso
          have h1 : (KM q m + κq q + 2) * αp q p ≤ (s - k + 1) * αp q p := Nat.mul_le_mul_right _ (by omega)
          have h2 : (KM q m + κq q + 2) * αp q p = (KM q m + 1) * αp q p + κq q * αp q p + αp q p := by
            rw [show KM q m + κq q + 2 = (KM q m + 1) + κq q + 1 by omega, Nat.add_mul, Nat.add_mul,
              Nat.one_mul]
          rw [← hαe, ← hνe] at hν
          omega
      have hcur : ((p ^ ((KM q m + 1) * αp q p + νp q p + v - (s - (s - (s - k)) + 1) * αp q p) : Nat) : Int) ∣
          1 * chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β1 l)) s - ρ := by
        rw [show s - (s - (s - k)) = s - k by omega, Int.one_mul]; exact hP1
      have hk' : s - (s - k) = k := by omega
      obtain ⟨D, _, hbD, hID, hnew, hpres⟩ := op_digit (A := 1) (B0 := ρ) hq hodd hm β1 hβ1
        (k := s - (s - k)) (by omega) (by omega) (by omega) hI1 hpL (by omega)
        (by rw [show s - (s - (s - k)) = s - k by omega]; exact hge)
        (fun h => by have := Int.eq_one_of_dvd_one (by omega) h; have := hpp.1.1; omega) hcur
      rw [hk'] at hbD hID hnew hpres
      rw [Int.one_mul] at hnew
      refine ⟨setD β1 k p v D, hbD, fun l hl => by rw [setD_ne β1 hl]; exact hun1 l hl, hID,
        fun r hr hrp => ?_, ?_⟩
      · have hrr := (mem_qprimes (show 1 ≤ q by omega)).mp hr
        have hpr := hpres (s - k) (by omega) r hrr.1 hrr.2
        simp only [hrp, ↓reduceIte] at hpr
        rw [show k + (s - k) = s by omega] at hpr
        have hlvr : H r ≤ (KM q m + 1) * vp r q + vp r (uu q) + Xp q r - (s - k + 1) * vp r q := by
          have h1 := hH r
          have h2 := Xp_ge_alpha q r
          have h3 : (s - k + 1) * vp r q = (s - k) * vp r q + vp r q := Nat.succ_mul _ _
          unfold αp νp at h1
          unfold αp at h2
          omega
        have hpr' := Int.dvd_trans (Int.ofNat_dvd.mpr (Nat.pow_dvd_pow r hlvr)) hpr
        have hold := hO1 r hr hrp
        have e : chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β1 k p v D l)) s - ρ
            = (chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β1 k p v D l)) s
              - chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β1 l)) s)
              + (chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β1 l)) s - ρ) := by int_ring
        rw [e]; exact Int.dvd_add hpr' hold
      · rw [show (KM q m + 1) * αp q p + νp q p + (v + 1) - (s - k + 1) * αp q p
          = (KM q m + 1) * αp q p + νp q p + v - (s - k + 1) * αp q p + 1 by omega]
        exact hnew

/-- Final stage, one step k, all primes. -/
theorem final_k {q m : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) {y0 ρ : Int}
    {b : Nat → Nat} {s k : Nat} (hk1 : 1 ≤ k) (hks : k + 1 ≤ s) :
    ∀ L : List Nat, L.Nodup → (∀ r ∈ L, r ∈ qprimes q) →
    ∀ β : Nat → Nat → Nat, (∀ l, ∀ r ∈ qprimes q, β l r < r ^ αp q r) →
      Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β l)) s →
      (∀ r ∈ qprimes q, ((r ^ ((KM q m + 1) * αp q r + νp q r - (s - k + 1) * αp q r) : Nat) : Int) ∣
        chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β l)) s - ρ) →
      ∃ β' : Nat → Nat → Nat, (∀ l, ∀ r ∈ qprimes q, β' l r < r ^ αp q r) ∧
        (∀ l, l ≠ k → β' l = β l) ∧
        Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β' l)) s ∧
        (∀ r ∈ qprimes q, ((r ^ (if r ∈ L then (KM q m + 1) * αp q r + νp q r - (s - k) * αp q r
            else (KM q m + 1) * αp q r + νp q r - (s - k + 1) * αp q r) : Nat) : Int) ∣
          chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β' l)) s - ρ)
  | [], _, _, β, hβ, hI, h0 => ⟨β, hβ, fun _ _ => rfl, hI, fun r hr => by
      simp only [List.not_mem_nil, ↓reduceIte]; exact h0 r hr⟩
  | p :: L, hnd, hsub, β, hβ, hI, h0 => by
    have hnd' := List.nodup_cons.mp hnd
    obtain ⟨β1, hβ1, hun1, hI1, h1⟩ :=
      final_k hq hodd hm hk1 hks L hnd'.2 (fun r hr => hsub r (List.mem_cons_of_mem _ hr)) β hβ hI h0
    have hpL := hsub p (List.mem_cons_self ..)
    have hH : ∀ r, (if r ∈ L then (KM q m + 1) * αp q r + νp q r - (s - k) * αp q r
        else (KM q m + 1) * αp q r + νp q r - (s - k + 1) * αp q r)
          ≤ (KM q m + 1) * αp q r + νp q r - (s - k) * αp q r := by
      intro r
      split
      · exact Nat.le_refl _
      · have : (s - k) * αp q r ≤ (s - k + 1) * αp q r := Nat.mul_le_mul_right _ (by omega)
        omega
    have hPp := h1 p hpL
    simp only [hnd'.1, ↓reduceIte] at hPp
    obtain ⟨β2, hβ2, hun2, hI2, hO2, hP2⟩ := final_prime hq hodd hm hk1 hks hpL _ hH (αp q p)
      (Nat.le_refl _) β1 hβ1 hI1 (fun r hr _ => h1 r hr) hPp
    refine ⟨β2, hβ2, fun l hl => (hun2 l hl).trans (hun1 l hl), hI2, fun r hr => ?_⟩
    by_cases hrp : r = p
    · subst hrp
      simp only [List.mem_cons_self, ↓reduceIte]
      have e : (KM q m + 1) * αp q r + νp q r + αp q r - (s - k + 1) * αp q r
          = (KM q m + 1) * αp q r + νp q r - (s - k) * αp q r := by
        have h5 : (s - k + 1) * αp q r = (s - k) * αp q r + αp q r := by rw [Nat.add_mul, Nat.one_mul]
        omega
      rw [← e]; exact hP2
    · have h2 := hO2 r hr hrp
      by_cases hrL : r ∈ L
      · have hmem : r ∈ p :: L := List.mem_cons_of_mem _ hrL
        simp only [hmem, hrL, ↓reduceIte] at h2 ⊢; exact h2
      · have hmem : r ∉ p :: L := fun h => by
          rcases List.mem_cons.mp h with h | h
          · exact hrp h
          · exact hrL h
        simp only [hmem, hrL, ↓reduceIte] at h2 ⊢; exact h2

/-- Final stage: all steps k = 1, …, s − 1. -/
theorem final_all {q m : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) {y0 ρ : Int}
    {b : Nat → Nat} {s : Nat} (hs : KM q m + κq q + 1 ≤ s) (β : Nat → Nat → Nat)
    (hβ : ∀ l, ∀ r ∈ qprimes q, β l r < r ^ αp q r)
    (hI : Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β l)) s) :
    ∀ k, 1 ≤ k → k ≤ s → ∃ β' : Nat → Nat → Nat, (∀ l, ∀ r ∈ qprimes q, β' l r < r ^ αp q r) ∧
      (∀ l, s ≤ l → β' l = β l) ∧
      Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β' l)) s ∧
      (∀ r ∈ qprimes q, ((r ^ ((KM q m + 1) * αp q r + νp q r - (s - k + 1) * αp q r) : Nat) : Int) ∣
        chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β' l)) s - ρ)
  | 0, h, _ => absurd h (by omega)
  | 1, _, _ => by
    refine ⟨β, hβ, fun _ _ => rfl, hI, fun r hr => ?_⟩
    have hrr := (mem_qprimes (show 1 ≤ q by omega)).mp hr
    have hν := nu_le_kappa hq hodd hrr.1 hrr.2
    have h1 : (KM q m + κq q + 1) * αp q r ≤ (s - 1 + 1) * αp q r := Nat.mul_le_mul_right _ (by omega)
    have h2 : (KM q m + κq q + 1) * αp q r = (KM q m + 1) * αp q r + κq q * αp q r := by
      rw [show KM q m + κq q + 1 = KM q m + 1 + κq q by omega, Nat.add_mul]
    have h3 : (KM q m + 1) * αp q r + νp q r - (s - 1 + 1) * αp q r = 0 := by
      unfold αp at h1 h2; unfold αp νp; omega
    rw [h3, Nat.pow_zero]; exact Int.one_dvd _
  | k + 2, _, hk => by
    obtain ⟨β1, hβ1, hun1, hI1, h1⟩ := final_all hq hodd hm hs β hβ hI (k + 1) (by omega) (by omega)
    obtain ⟨β2, hβ2, hun2, hI2, h2⟩ := final_k (ρ := ρ) hq hodd hm (k := k + 1) (by omega) (by omega)
      (qprimes q) (qprimes_nodup q) (fun r hr => hr) β1 hβ1 hI1 h1
    refine ⟨β2, hβ2, fun l hl => (hun2 l (by omega)).trans (hun1 l hl), hI2, fun r hr => ?_⟩
    have h := h2 r hr
    simp only [hr, ↓reduceIte] at h
    rw [show s - (k + 2) + 1 = s - (k + 1) by omega]; exact h

end Collatz
