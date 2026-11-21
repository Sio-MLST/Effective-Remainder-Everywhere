import Collatz.GeneralAStage
import Collatz.GeneralAWide

/-! Theorem A, Step 4, Lemma 12 (shift selection), full statement for all κ ≥ 0.
    κ = 0 is `shift_select_k0` (below). For κ ≥ 1 we start from the zero digit
    function, extend the path one stage at a time up to length s with `stage_mid`
    (digit index s is never touched, so j_s = 0 is kept), and finish with `final_all`
    at k = s. Choice-free. -/

namespace Collatz

/-- The zero digit function β_l(r) = 0. -/
def zeroD (_ : Nat) : Nat → Nat := fun _ => 0

theorem jsumL_zero (q : Nat) : ∀ L : List Nat, jsumL q L (fun _ => 0) = 0
  | [] => rfl
  | p :: L => by simp only [jsumL_cons, jsumL_zero q L, Nat.mul_zero, Nat.add_zero]

/-- A nat divisibility criterion for integers from prime-power divisibility. -/
theorem nat_dvd_int_of_primes {q X : Nat} {Z : Int} (hq : 1 < q) (hX : 1 ≤ X)
    (hXq : ∀ r, IsPrime r → r ∣ X → r ∣ q)
    (h : ∀ p, IsPrime p → p ∣ q → ((p ^ vp p X : Nat) : Int) ∣ Z) : (X : Int) ∣ Z := by
  have hn : X ∣ Z.natAbs := dvd_of_val_le hq hX hXq
    (fun p hp hpq => Int.natAbs_dvd_natAbs.mpr (h p hp hpq))
  exact Int.natAbs_dvd_natAbs.mp (by rwa [Int.natAbs_natCast])

/-- κ = 0: Lemma 12 is the κ = 0 shift selection `choose_shifts` (with a = 1, u_q = 1). -/
theorem shift_select_k0 {q m a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m)
    (hκ0 : κq q = 0) (ha : a = 1) {c y0 : Int}
    (hc : (LamA q m : Int) ∣ ((2 : Int) ^ a - q) * c - 1) (hy0 : (LamA q m : Int) ∣ y0 - c)
    {b : Nat → Nat} (hbK : ∀ l, 1 ≤ l → l ≤ KM q m + κq q + 1 → b l = a)
    {s : Nat} (hs : KM q m + κq q + 1 ≤ s) (ρ : Int) :
    ∃ J : Nat → Nat, (∀ l, 1 ≤ l → l ≤ s - 1 → J l ≤ J0star q) ∧ J s = 0 ∧
      Integral (q : Int) (PM q m) y0 b J s ∧
      ((q ^ KM q m * uqq q : Nat) : Int) ∣ chain (q : Int) (PM q m) y0 b J s - ρ := by
  subst ha
  have hU : uqq q = 1 := (kappaQ_zero_iff q (uu q)).mp hκ0
  have hL : LamA q m = q ^ (KM q m + 1) := by unfold LamA; rw [hU, Nat.mul_one]
  have hqK : 0 < q ^ (KM q m + 1) := Nat.pow_pos (by omega)
  -- u_P with 2^P = 1 + q^{K+1} u_P, a unit mod q
  have hdvd := Lam_dvd (m := m) hq hodd hm 1
  rw [Nat.one_mul, hL] at hdvd
  obtain ⟨uP, huP⟩ := hdvd
  have h2P : (2 : Int) ^ PM q m = 1 + ((q : Nat) : Int) ^ (KM q m + 1) * (uP : Int) := by
    have h1 : 1 ≤ 2 ^ PM q m := Nat.one_le_two_pow
    have : 2 ^ PM q m = 1 + q ^ (KM q m + 1) * uP := by omega
    exact_mod_cast this
  have hcop : Nat.gcd uP q = 1 := by
    apply coprime_of_no_prime
    intro p hp hpu hpq
    have hv := val_2PN (m := m) (N := 1) hq hodd hm hp hpq Nat.one_pos
    have hν : vp p (uu q) = 0 := by
      have h1 := val_uq hq hodd hp hpq
      rw [hU] at h1
      exact val_unique h1 (val_zero_of_not_dvd (fun h => by
        have := Nat.le_of_dvd Nat.one_pos h; have := hp.1; omega))
    rw [Nat.one_mul, hν, Nat.add_zero, show vp p 1 = 0 by
      exact val_unique (val_vp hp.1 Nat.one_pos) (val_zero_of_not_dvd (fun h => by
        have := Nat.le_of_dvd Nat.one_pos h; have := hp.1; omega)), Nat.add_zero] at hv
    apply hv.2
    rw [huP, Nat.pow_succ]
    have hqp := (val_pow hp (val_q hq hp hpq).1 (KM q m + 1)).1
    exact Nat.mul_dvd_mul hqp hpu
  obtain ⟨kk, ww, hkw⟩ := nat_bez uP q hq hcop
  have S : Setup (q : Int) (KM q m) (PM q m) (uP : Int) b y0 c := {
    hp := by omega
    h2P := h2P
    inv2 := ⟨((q + 1) / 2 : Nat), ⟨1, by
      have : q + 1 = 2 * ((q + 1) / 2) := by omega
      have h : ((q + 1 : Nat) : Int) = 2 * (((q + 1) / 2 : Nat) : Int) := by exact_mod_cast this
      push_cast at h; omega⟩⟩
    invu := ⟨(kk : Int), ⟨(ww : Int), by
      have : ((uP * kk : Nat) : Int) = ((q * ww + 1 : Nat) : Int) := by rw [hkw]
      push_cast at this; omega⟩⟩
    hc := by rw [hL] at hc; push_cast at hc; simpa [Int.pow_one] using hc
    hy0 := by rw [hL] at hy0; push_cast at hy0; exact hy0
    hb1 := fun i h1 h2 => hbK i h1 (by omega) }
  obtain ⟨f, hf, hJ⟩ := choose_shifts q (by omega) rfl S (s - (KM q m + 1)) ρ
  have hsK : KM q m + 1 + (s - (KM q m + 1)) = s := by omega
  refine ⟨fun l => if l ≤ KM q m + (s - (KM q m + 1)) then f l else 0, fun l h1 h2 => ?_, ?_, ?_⟩
  · have hl : l ≤ KM q m + (s - (KM q m + 1)) := by omega
    simp only [hl, ↓reduceIte]
    unfold J0star; rw [hκ0]; simp only [↓reduceIte]
    have := hf l h1 hl; omega
  · have : ¬ s ≤ KM q m + (s - (KM q m + 1)) := by omega
    simp only [this, ↓reduceIte]
  · have h := hJ (fun l => if l ≤ KM q m + (s - (KM q m + 1)) then f l else 0)
      (fun l _ hl => by simp only [hl, ↓reduceIte])
    rw [hsK] at h
    refine ⟨h.1, ?_⟩
    rw [hU, Nat.mul_one]; push_cast; exact h.2

/-- κ ≥ 1 branch of Lemma 12. -/
theorem shift_select_k1 {q m a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m)
    (hκ1 : 0 < κq q) {c y0 : Int}
    (hc : (LamA q m : Int) ∣ ((2 : Int) ^ a - q) * c - 1) (hy0 : (LamA q m : Int) ∣ y0 - c)
    {b : Nat → Nat} (hbK : ∀ l, 1 ≤ l → l ≤ KM q m + κq q + 1 → b l = a)
    {s : Nat} (hs : KM q m + κq q + 1 ≤ s) (ρ : Int) :
    ∃ J : Nat → Nat, (∀ l, 1 ≤ l → l ≤ s - 1 → J l ≤ J0star q) ∧ J s = 0 ∧
      Integral (q : Int) (PM q m) y0 b J s ∧
      ((q ^ KM q m * uqq q : Nat) : Int) ∣ chain (q : Int) (PM q m) y0 b J s - ρ := by
  -- Start: zero digits. Integral up to K+1 holds for any digit function (primer).
  have hβ0 : ∀ l, ∀ r ∈ qprimes q, zeroD l r < r ^ αp q r := by
    intro l r hr
    have hr' := (mem_qprimes (show 1 ≤ q by omega)).mp hr
    have h2 := hr'.1.1
    show 0 < r ^ αp q r
    exact Nat.pow_pos (by omega)
  have hI0 : Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (zeroD l)) (KM q m + 1) :=
    (primer hq hodd hm hc hy0 (b := b) (J := fun l => jsumL q (qprimes q) (zeroD l))
      (fun l h1 h2 => hbK l h1 (by omega)) (KM q m + 1) (Nat.le_refl _)).1
  -- Extend one stage at a time; digit index s is preserved throughout.
  have hstage : ∀ n, KM q m + 1 + n ≤ s → ∃ β : Nat → Nat → Nat,
      (∀ l, ∀ r ∈ qprimes q, β l r < r ^ αp q r) ∧ (∀ r, β s r = 0) ∧
      Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β l)) (KM q m + 1 + n) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨zeroD, hβ0, fun _ => rfl, hI0⟩
    | succ n ih =>
      intro hn
      obtain ⟨β, hβ, hβs, hI⟩ := ih (by omega)
      obtain ⟨β', hβ', hsame, hI'⟩ := stage_mid hq hodd hm hc hy0 hbK
        (T := KM q m + 1 + n) (by omega) β hβ hI
      refine ⟨β', hβ', fun r => ?_, ?_⟩
      · have h := congrFun (hsame s (by omega)) r
        rw [h]; exact hβs r
      · rw [show KM q m + 1 + (n + 1) = KM q m + 1 + n + 1 by omega]; exact hI'
  obtain ⟨β, hβ, hβs, hI⟩ := hstage (s - (KM q m + 1)) (by omega)
  rw [show KM q m + 1 + (s - (KM q m + 1)) = s by omega] at hI
  obtain ⟨β', hβ', hsame', hI', hdiv⟩ :=
    final_all (ρ := ρ) hq hodd hm hs β hβ hI s (by omega) (Nat.le_refl s)
  have hzs : β' s = fun _ => 0 := funext fun r => by
    rw [congrFun (hsame' s (Nat.le_refl s)) r]; exact hβs r
  refine ⟨fun l => jsumL q (qprimes q) (β' l), fun l _ _ => ?_, ?_, hI', ?_⟩
  · show jsumL q (qprimes q) (β' l) ≤ J0star q
    rw [J0star_eq (by omega)]
    exact jsumL_le q (β' l) (qprimes q) (fun p hp => hβ' l p hp)
  · show jsumL q (qprimes q) (β' s) = 0
    rw [hzs]; exact jsumL_zero q _
  · have hXpos : 0 < q ^ KM q m * uqq q := qKU_pos (m := m) hq hodd
    refine nat_dvd_int_of_primes hq (by omega) (fun r hr hrX => prime_dvd_q_of_dvd_qU hr hrX) ?_
    intro p hp hpq
    have hpL : p ∈ qprimes q := (mem_qprimes (show 1 ≤ q by omega)).mpr ⟨hp, hpq⟩
    have hv : vp p (q ^ KM q m * uqq q) = KM q m * αp q p + νp q p := by
      unfold αp νp
      exact val_unique (val_vp hp.1 hXpos) (val_qkU hq hodd hp hpq)
    have he : (KM q m + 1) * αp q p + νp q p - (s - s + 1) * αp q p
        = KM q m * αp q p + νp q p := by
      rw [show s - s + 1 = 1 by omega, Nat.one_mul, Nat.add_mul, Nat.one_mul]
      omega
    have hd := hdiv p hpL
    rw [he] at hd
    rw [hv]
    exact hd

/-- Lemma 12 (shift selection): with b_l = a for l ≤ K + κ + 1 and y₀ ≡ c_* (mod Λ),
    there are shifts j_l ≤ J₀^* (1 ≤ l < s), j_s = 0, making the path integral up to s with
    y_s ≡ ρ (mod q^K u_q). -/
theorem shift_select {q m a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m)
    (hκa : κq q = 0 → a = 1) {c y0 : Int}
    (hc : (LamA q m : Int) ∣ ((2 : Int) ^ a - q) * c - 1) (hy0 : (LamA q m : Int) ∣ y0 - c)
    {b : Nat → Nat} (hbK : ∀ l, 1 ≤ l → l ≤ KM q m + κq q + 1 → b l = a)
    {s : Nat} (hs : KM q m + κq q + 1 ≤ s) (ρ : Int) :
    ∃ J : Nat → Nat, (∀ l, 1 ≤ l → l ≤ s - 1 → J l ≤ J0star q) ∧ J s = 0 ∧
      Integral (q : Int) (PM q m) y0 b J s ∧
      ((q ^ KM q m * uqq q : Nat) : Int) ∣ chain (q : Int) (PM q m) y0 b J s - ρ := by
  match Nat.eq_zero_or_pos (κq q) with
  | Or.inl hκ0 => exact shift_select_k0 hq hodd hm hκ0 (hκa hκ0) hc hy0 hbK hs ρ
  | Or.inr hκ1 => exact shift_select_k1 hq hodd hm hκ1 hc hy0 hbK hs ρ

end Collatz
