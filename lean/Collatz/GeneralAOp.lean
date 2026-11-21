import Collatz.GeneralAPerturb

/-! Theorem A, Lemma 12 infrastructure for κ ≥ 1: the weights E_p^*, shifts
    j = Σ_p E_p^* β_p with β_p < p^{α_p} (so j ≤ J₀^*), and base-p digit replacement.
    Choice-free. -/

namespace Collatz

/-- X_{p'} = max(α_{p'}, (κ+1)α_{p'} − ν_{p'}). -/
def Xp (q p : Nat) : Nat := max (αp q p) ((κq q + 1) * αp q p - νp q p)

theorem Epstar_eq (q p : Nat) :
    Epstar q p = pprod (Xp q) ((qprimes q).filter (fun p' => p' != p)) := rfl

theorem filter_primes {q : Nat} (hq : 1 ≤ q) (p : Nat) :
    ∀ r ∈ (qprimes q).filter (fun p' => p' != p), IsPrime r :=
  fun r hr => qprimes_prime hq r (List.mem_filter.mp hr).1


theorem E_not_dvd {q p : Nat} (hq : 1 < q) (hp : IsPrime p) : ¬ p ∣ Epstar q p := by
  rw [Epstar_eq]
  have hc := coprime_pow_pprod (f := Xp q) hp 1 _ (filter_primes (q := q) (by omega) p) (fun h => by
    have := (List.mem_filter.mp h).2
    simp at this)
  rw [Nat.pow_one] at hc
  intro h
  have := Nat.dvd_gcd (Nat.dvd_refl p) h
  rw [hc] at this
  have := Nat.le_of_dvd Nat.one_pos this; have := hp.1; omega

theorem E_dvd {q p p' : Nat} (hp' : p' ∈ qprimes q) (hne : p' ≠ p) :
    p' ^ Xp q p' ∣ Epstar q p := by
  rw [Epstar_eq]
  exact dvd_pprod _ _ (List.mem_filter.mpr ⟨hp', by simp [hne]⟩)

theorem E_pos {q p : Nat} (hq : 1 < q) : 0 < Epstar q p := by
  rw [Epstar_eq]
  have hL := filter_primes (show 1 ≤ q by omega) p
  generalize (qprimes q).filter (fun p' => p' != p) = L at hL
  induction L with
  | nil => rw [pprod_nil]; exact Nat.one_pos
  | cons r L ih =>
    rw [pprod_cons]
    exact Nat.mul_pos (Nat.pow_pos (by have := (hL r (List.mem_cons_self ..)).1; omega))
      (ih (fun s hs => hL s (List.mem_cons_of_mem _ hs)))

/-- Level inequality for the other primes: (κ+1)α ≤ ν + X. -/
theorem Xp_ge (q p : Nat) : (κq q + 1) * αp q p ≤ νp q p + Xp q p := by
  unfold Xp
  have := Nat.le_max_right (αp q p) ((κq q + 1) * αp q p - νp q p)
  omega

theorem Xp_ge_alpha (q p : Nat) : αp q p ≤ Xp q p := Nat.le_max_left _ _

/-! ### Shift sums -/

def jsumL (q : Nat) (L : List Nat) (β : Nat → Nat) : Nat :=
  L.foldl (fun acc p => acc + Epstar q p * β p) 0

theorem jsumL_acc (q : Nat) (β : Nat → Nat) :
    ∀ (L : List Nat) (acc : Nat), L.foldl (fun a p => a + Epstar q p * β p) acc = acc + jsumL q L β
  | [], acc => by simp [jsumL]
  | p :: L, acc => by
    show L.foldl (fun a p => a + Epstar q p * β p) (acc + Epstar q p * β p) =
      acc + L.foldl (fun a p => a + Epstar q p * β p) (0 + Epstar q p * β p)
    rw [jsumL_acc q β L, jsumL_acc q β L]; omega

theorem jsumL_cons (q : Nat) (β : Nat → Nat) (p : Nat) (L : List Nat) :
    jsumL q (p :: L) β = Epstar q p * β p + jsumL q L β := by
  show L.foldl (fun a p => a + Epstar q p * β p) (0 + Epstar q p * β p) = _
  rw [jsumL_acc]; omega

theorem jsumL_congr (q : Nat) (β β' : Nat → Nat) :
    ∀ L : List Nat, (∀ p ∈ L, β p = β' p) → jsumL q L β = jsumL q L β'
  | [], _ => rfl
  | p :: L, h => by
    rw [jsumL_cons, jsumL_cons, h p (List.mem_cons_self ..),
      jsumL_congr q β β' L (fun r hr => h r (List.mem_cons_of_mem _ hr))]

/-- Replacing one component changes the sum by E_p (β' p − β p). -/
theorem jsumL_replace (q : Nat) (β β' : Nat → Nat) (p : Nat) :
    ∀ L : List Nat, L.Nodup → p ∈ L → (∀ r, r ≠ p → β' r = β r) →
      jsumL q L β' + Epstar q p * β p = jsumL q L β + Epstar q p * β' p
  | [], _, h, _ => absurd h List.not_mem_nil
  | r :: L, hnd, hp, hβ => by
    rw [jsumL_cons, jsumL_cons]
    have hnd' := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hp with h | h
    · subst h
      rw [jsumL_congr q β' β L (fun s hs => hβ s (fun e => hnd'.1 (e ▸ hs)))]
      omega
    · have hrp : r ≠ p := fun e => hnd'.1 (e ▸ h)
      rw [hβ r hrp]
      have := jsumL_replace q β β' p L hnd'.2 h hβ
      omega

def J0L (q : Nat) (L : List Nat) : Nat :=
  L.foldl (fun acc p => acc + (p ^ αp q p - 1) * Epstar q p) 0

theorem J0L_acc (q : Nat) :
    ∀ (L : List Nat) (acc : Nat), L.foldl (fun a p => a + (p ^ αp q p - 1) * Epstar q p) acc = acc + J0L q L
  | [], acc => by simp [J0L]
  | p :: L, acc => by
    show L.foldl (fun a p => a + (p ^ αp q p - 1) * Epstar q p) (acc + (p ^ αp q p - 1) * Epstar q p) =
      acc + L.foldl (fun a p => a + (p ^ αp q p - 1) * Epstar q p) (0 + (p ^ αp q p - 1) * Epstar q p)
    rw [J0L_acc q L, J0L_acc q L]; omega

theorem jsumL_le (q : Nat) (β : Nat → Nat) :
    ∀ L : List Nat, (∀ p ∈ L, β p < p ^ αp q p) → jsumL q L β ≤ J0L q L
  | [], _ => Nat.le_refl _
  | p :: L, h => by
    rw [jsumL_cons]
    have hJ : J0L q (p :: L) = (p ^ αp q p - 1) * Epstar q p + J0L q L := by
      show L.foldl (fun a p => a + (p ^ αp q p - 1) * Epstar q p) (0 + (p ^ αp q p - 1) * Epstar q p) = _
      rw [J0L_acc]; omega
    rw [hJ]
    have h1 : Epstar q p * β p ≤ (p ^ αp q p - 1) * Epstar q p := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by have := h p (List.mem_cons_self ..); omega)
    have := jsumL_le q β L (fun r hr => h r (List.mem_cons_of_mem _ hr))
    omega

/-- For κ ≥ 1, J₀^* is the full sum. -/
theorem J0star_eq {q : Nat} (hκ : 1 ≤ κq q) : J0star q = J0L q (qprimes q) := by
  unfold J0star
  have : ¬ κq q = 0 := by omega
  simp only [this, ↓reduceIte]
  rfl

/-! ### Base-p digit replacement -/

theorem digit_split {p α v B : Nat} (hp : 2 ≤ p) (hv : v < α) (hB : B < p ^ α) :
    B / p ^ v % p < p ∧ B = (B - B / p ^ v % p * p ^ v) + B / p ^ v % p * p ^ v ∧
      ∀ D, D < p → (B - B / p ^ v % p * p ^ v) + D * p ^ v < p ^ α := by
  have hpv : 0 < p ^ v := Nat.pow_pos (by omega)
  have hd := Nat.mod_lt (B / p ^ v) (show 0 < p by omega)
  have h1 := Nat.mod_add_div B (p ^ v)
  have h2 := Nat.mod_add_div (B / p ^ v) p
  have e3 : B / p ^ v / p = B / p ^ (v + 1) := by rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
  -- B = B % p^v + p^v (d + p * hi)
  generalize hd' : B / p ^ v % p = d at hd h2
  generalize hhi : B / p ^ v / p = hi at h2 e3
  generalize hlo : B % p ^ v = lo at h1
  have hlo' : lo < p ^ v := hlo ▸ Nat.mod_lt _ hpv
  have hB2 : B = lo + p ^ v * d + p ^ (v + 1) * hi := by
    rw [Nat.pow_succ]
    have : p ^ v * (B / p ^ v) = p ^ v * (d + p * hi) := by rw [h2]
    rw [Nat.mul_add, ← Nat.mul_assoc] at this
    omega
  have hdpv : d * p ^ v = p ^ v * d := Nat.mul_comm _ _
  refine ⟨hd, by omega, fun D hD => ?_⟩
  have hrest : B - d * p ^ v = lo + p ^ (v + 1) * hi := by omega
  rw [hrest]
  -- hi < p^(α - v - 1)
  have hα : p ^ α = p ^ (v + 1) * p ^ (α - (v + 1)) := by rw [← Nat.pow_add]; congr 1; omega
  have hhi1 : hi + 1 ≤ p ^ (α - (v + 1)) := by
    match Nat.lt_or_ge hi (p ^ (α - (v + 1))) with
    | Or.inl h => exact h
    | Or.inr h =>
      exfalso
      have : p ^ (v + 1) * p ^ (α - (v + 1)) ≤ p ^ (v + 1) * hi := Nat.mul_le_mul_left _ h
      omega
  have h4 : p ^ (v + 1) * (hi + 1) ≤ p ^ α := by rw [hα]; exact Nat.mul_le_mul_left _ hhi1
  have h5 : D * p ^ v ≤ (p - 1) * p ^ v := Nat.mul_le_mul_right _ (by omega)
  have h6 : (p - 1) * p ^ v + p ^ v = p ^ (v + 1) := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ p), Nat.pow_succ,
      Nat.mul_comm]
  rw [Nat.mul_add, Nat.mul_one] at h4
  omega

/-! ### The digit operation -/

/-- The shift profile with digit v of the p-component at step k set to D. -/
def setD (β : Nat → Nat → Nat) (k p v D : Nat) : Nat → Nat → Nat :=
  fun l => if l = k then (fun r => if r = p then
    (β k p - β k p / p ^ v % p * p ^ v) + D * p ^ v else β k r) else β l

theorem setD_ne (β : Nat → Nat → Nat) {k p v D l : Nat} (h : l ≠ k) :
    setD β k p v D l = β l := by simp only [setD, h, ↓reduceIte]

theorem setD_jsum {q : Nat} (β : Nat → Nat → Nat) {k p v D : Nat} (hp : p ∈ qprimes q) :
    jsumL q (qprimes q) (setD β k p v D k) + Epstar q p * (β k p / p ^ v % p * p ^ v)
      = jsumL q (qprimes q) (β k) + Epstar q p * (D * p ^ v) := by
  have h := jsumL_replace q (β k) (setD β k p v D k) p (qprimes q) (qprimes_nodup q) hp
    (fun r hr => by simp only [setD, hr, ↓reduceIte])
  have hk : setD β k p v D k p = (β k p - β k p / p ^ v % p * p ^ v) + D * p ^ v := by
    simp only [setD, ↓reduceIte]
  rw [hk] at h
  have hle : β k p / p ^ v % p * p ^ v ≤ β k p := by
    have := Nat.mod_add_div (β k p) (p ^ v)
    have h2 := Nat.mod_le (β k p / p ^ v) p
    have h3 : β k p / p ^ v % p * p ^ v ≤ β k p / p ^ v * p ^ v := Nat.mul_le_mul_right _ h2
    have h4 : β k p / p ^ v * p ^ v ≤ β k p := Nat.div_mul_le_self _ _
    omega
  have e : Epstar q p * β k p = Epstar q p * (β k p - β k p / p ^ v % p * p ^ v)
      + Epstar q p * (β k p / p ^ v % p * p ^ v) := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hle]
  rw [Nat.mul_add] at h
  omega

/-- The shift at step k for digit D2 exceeds that for D1 by E_p p^v (D2 − D1). -/
theorem setD_diff {q : Nat} (β : Nat → Nat → Nat) {k p v D1 D2 : Nat} (hp : p ∈ qprimes q)
    (h12 : D1 ≤ D2) :
    jsumL q (qprimes q) (setD β k p v D2 k)
      = jsumL q (qprimes q) (setD β k p v D1 k) + Epstar q p * p ^ v * (D2 - D1) := by
  have h1 := setD_jsum (q := q) β (k := k) (v := v) (D := D1) hp
  have h2 := setD_jsum (q := q) β (k := k) (v := v) (D := D2) hp
  have e : Epstar q p * (D2 * p ^ v) = Epstar q p * (D1 * p ^ v) + Epstar q p * p ^ v * (D2 - D1) := by
    rw [Nat.mul_assoc, ← Nat.mul_add, Nat.mul_comm (p ^ v) (D2 - D1), ← Nat.add_mul,
      Nat.add_sub_cancel' h12]
  omega

/-- Pair lemma for two digit values D1 < D2 < p at step k. -/
theorem op_pair {q m : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) {y0 : Int}
    {b : Nat → Nat} (β : Nat → Nat → Nat) {T k p v D1 D2 : Nat} (hk : 1 ≤ k) (hkT : k ≤ T)
    (hTk : T - k ≤ KM q m + κq q) (hpL : p ∈ qprimes q)
    (hlev : (T - k + 1) * αp q p ≤ (KM q m + 1) * αp q p + νp q p + v)
    (h12 : D1 < D2) (h2p : D2 < p)
    (hI : Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D1 l)) T ∨
      Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D2 l)) T) :
    Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D1 l)) T ∧
    Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D2 l)) T ∧
    (∀ i, k + i ≤ T → ∀ r, IsPrime r → r ∣ q →
      ((r ^ ((KM q m + 1) * vp r q + vp r (uu q) + (if r = p then v else Xp q r) - (i + 1) * vp r q) : Nat) : Int) ∣
        chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D2 l)) (k + i)
        - chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D1 l)) (k + i)) ∧
    ¬ ((p ^ ((KM q m + 1) * αp q p + νp q p + v - (T - k + 1) * αp q p + 1) : Nat) : Int) ∣
        chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D2 l)) T
        - chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D1 l)) T := by
  have hp := (mem_qprimes (show 1 ≤ q by omega)).mp hpL
  have hE := E_not_dvd (q := q) hq hp.1
  have hEpos := E_pos (q := q) (p := p) hq
  have hpv : 0 < p ^ v := Nat.pow_pos (by have := hp.1.1; omega)
  have hΔ : 0 < Epstar q p * p ^ v * (D2 - D1) := Nat.mul_pos (Nat.mul_pos hEpos hpv) (by omega)
  have hJ' : ∀ l, l ≠ k → jsumL q (qprimes q) (setD β k p v D2 l) = jsumL q (qprimes q) (setD β k p v D1 l) :=
    fun l hl => by rw [setD_ne β hl, setD_ne β hl]
  have hJk := setD_diff (q := q) β (k := k) (v := v) hpL (Nat.le_of_lt h12)
  have hef : ∀ r, IsPrime r → r ∣ q → r ^ (if r = p then v else Xp q r) ∣ Epstar q p * p ^ v * (D2 - D1) := by
    intro r hr hrq
    by_cases hrp : r = p
    · simp only [hrp, ↓reduceIte]
      exact Nat.dvd_trans (Nat.dvd_mul_left _ _) (Nat.dvd_mul_right _ _)
    · simp only [hrp, ↓reduceIte]
      exact Nat.dvd_trans (E_dvd ((mem_qprimes (show 1 ≤ q by omega)).mpr ⟨hr, hrq⟩) hrp)
        (Nat.dvd_trans (Nat.dvd_mul_right _ _) (Nat.dvd_mul_right _ _))
  have hlev' : ∀ r, IsPrime r → r ∣ q → (T - k + 1) * vp r q ≤
      (KM q m + 1) * vp r q + vp r (uu q) + (if r = p then v else Xp q r) := by
    intro r hr hrq
    by_cases hrp : r = p
    · simp only [hrp, ↓reduceIte]; exact hlev
    · simp only [hrp, ↓reduceIte]
      have h1 := Xp_ge q r
      have h2 : (T - k + 1) * vp r q ≤ (KM q m + κq q + 1) * vp r q := Nat.mul_le_mul_right _ (by omega)
      have h3 : (KM q m + κq q + 1) * vp r q = (KM q m + 1) * vp r q + κq q * vp r q := by
        rw [show KM q m + κq q + 1 = KM q m + 1 + κq q by omega, Nat.add_mul]
      have h4 : κq q * vp r q ≤ (κq q + 1) * vp r q := Nat.mul_le_mul_right _ (by omega)
      unfold αp νp at h1
      omega
  obtain ⟨hI1, hI2, hdv⟩ := perturb hq hodd hm hk hkT hJ' hJk hΔ _ hef hlev' hI
  refine ⟨hI1, hI2, hdv, ?_⟩
  have hpe : p ^ v ∣ Epstar q p * p ^ v * (D2 - D1) :=
    Nat.dvd_trans (Nat.dvd_mul_left _ _) (Nat.dvd_mul_right _ _)
  have hpe1 : ¬ p ^ (v + 1) ∣ Epstar q p * p ^ v * (D2 - D1) := by
    intro h
    rw [Nat.pow_succ, Nat.mul_comm (Epstar q p) (p ^ v), Nat.mul_assoc] at h
    have h' := Nat.dvd_of_mul_dvd_mul_left hpv h
    rcases isPrime_dvd_mul hp.1 h' with h3 | h3
    · exact hE h3
    · have := Nat.le_of_dvd (by omega) h3; omega
  have hx := perturb_exact hq hodd hm hk hkT hJ' hJk hΔ hI1 hI2 hp.1 hp.2 hpe hpe1
    (i := T - k) (by omega) (by unfold αp νp at hlev; exact hlev)
  rw [show k + (T - k) = T by omega] at hx
  unfold αp νp
  exact hx

theorem int_dvd_of_emod_eq {M x y : Int} (h : x % M = y % M) : M ∣ y - x := by
  have h1 := Int.emod_add_mul_ediv x M
  have h2 := Int.emod_add_mul_ediv y M
  exact ⟨y / M - x / M, by rw [Int.mul_sub]; omega⟩

/-- The digit operation (Lemma 11 with replacement semantics): one base-p digit of the
    p-component of the step-k shift can be chosen to fix the next p-adic digit of an affine
    target at node T, keeping the profile bounded and with controlled perturbation. -/
theorem op_digit {q m : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) {y0 : Int}
    {b : Nat → Nat} (β : Nat → Nat → Nat) (hβ : ∀ l, ∀ r ∈ qprimes q, β l r < r ^ αp q r)
    {T k p v : Nat} (hk : 1 ≤ k) (hkT : k ≤ T) (hTk : T - k ≤ KM q m + κq q)
    (hI : Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β l)) T)
    (hpL : p ∈ qprimes q) (hv : v < αp q p)
    (hlev : (T - k + 1) * αp q p ≤ (KM q m + 1) * αp q p + νp q p + v)
    {A B0 : Int} (hA : ¬ (p : Int) ∣ A)
    (hcur : ((p ^ ((KM q m + 1) * αp q p + νp q p + v - (T - k + 1) * αp q p) : Nat) : Int) ∣
      A * chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β l)) T - B0) :
    ∃ D, D < p ∧ (∀ l, ∀ r ∈ qprimes q, setD β k p v D l r < r ^ αp q r) ∧
      Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D l)) T ∧
      ((p ^ ((KM q m + 1) * αp q p + νp q p + v - (T - k + 1) * αp q p + 1) : Nat) : Int) ∣
        A * chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D l)) T - B0 ∧
      ∀ i, k + i ≤ T → ∀ r, IsPrime r → r ∣ q →
        ((r ^ ((KM q m + 1) * vp r q + vp r (uu q) + (if r = p then v else Xp q r) - (i + 1) * vp r q) : Nat) : Int) ∣
          chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D l)) (k + i)
          - chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β l)) (k + i) := by
  have hp := (mem_qprimes (show 1 ≤ q by omega)).mp hpL
  have hp2 : 2 ≤ p := hp.1.1
  obtain ⟨hd, hBeq, hbnd⟩ := digit_split hp2 hv (hβ k p hpL)
  generalize hdd : β k p / p ^ v % p = d at hd hBeq hbnd
  -- setD at the current digit is β itself
  have hβd : setD β k p v d = β := by
    funext l r
    by_cases hl : l = k
    · subst hl
      by_cases hr : r = p
      · subst hr; simp only [setD, ↓reduceIte, hdd]; omega
      · simp only [setD, hr, ↓reduceIte]
    · simp only [setD, hl, ↓reduceIte]
  have hbndD : ∀ D, D < p → ∀ l, ∀ r ∈ qprimes q, setD β k p v D l r < r ^ αp q r := by
    intro D hD l r hr
    by_cases hl : l = k
    · subst hl
      by_cases hrp : r = p
      · subst hrp; simp only [setD, ↓reduceIte, hdd]; exact hbnd D hD
      · simp only [setD, hrp, ↓reduceIte]; exact hβ _ r hr
    · simp only [setD, hl, ↓reduceIte]; exact hβ l r hr
  -- every digit value gives an integral path, controlled relative to β
  have hall : ∀ D, D < p →
      Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D l)) T ∧
      ∀ i, k + i ≤ T → ∀ r, IsPrime r → r ∣ q →
        ((r ^ ((KM q m + 1) * vp r q + vp r (uu q) + (if r = p then v else Xp q r) - (i + 1) * vp r q) : Nat) : Int) ∣
          chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D l)) (k + i)
          - chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (β l)) (k + i) := by
    intro D hD
    rcases Nat.lt_trichotomy D d with h | h | h
    · have hI' : Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v d l)) T := by
        rw [hβd]; exact hI
      obtain ⟨hI1, _, hdv, _⟩ := op_pair hq hodd hm β hk hkT hTk hpL hlev h hd (Or.inr hI')
      refine ⟨hI1, fun i hi r hr hrq => ?_⟩
      have h1 := hdv i hi r hr hrq
      rw [hβd] at h1
      obtain ⟨c, hc⟩ := h1
      exact ⟨-c, by rw [Int.mul_neg, ← hc]; int_ring⟩
    · subst h; rw [hβd]; exact ⟨hI, fun i _ r _ _ => by rw [Int.sub_self]; exact Int.dvd_zero _⟩
    · have hI' : Integral (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v d l)) T := by
        rw [hβd]; exact hI
      obtain ⟨_, hI2, hdv, _⟩ := op_pair hq hodd hm β hk hkT hTk hpL hlev h hD (Or.inl hI')
      refine ⟨hI2, fun i hi r hr hrq => ?_⟩
      have h1 := hdv i hi r hr hrq
      rw [hβd] at h1; exact h1
  -- the residues modulo p^{h+1}
  generalize hh : (KM q m + 1) * αp q p + νp q p + v - (T - k + 1) * αp q p = h at hcur ⊢
  have hph : ((p ^ h : Nat) : Int) ∣ ((p ^ (h + 1) : Nat) : Int) := by
    exact Int.ofNat_dvd.mpr (Nat.pow_dvd_pow p (Nat.le_succ h))
  have hM0 : (0 : Int) < ((p ^ (h + 1) : Nat) : Int) := by
    have : 0 < p ^ (h + 1) := Nat.pow_pos (by omega); omega
  have hTkT : k + (T - k) = T := by omega
  have hYd : ∀ D, D < p → ((p ^ h : Nat) : Int) ∣
      A * chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D l)) T - B0 := by
    intro D hD
    have h1 := (hall D hD).2 (T - k) (by omega) p hp.1 hp.2
    simp only [↓reduceIte] at h1
    rw [hTkT] at h1
    have e : (KM q m + 1) * vp p q + vp p (uu q) + v - (T - k + 1) * vp p q = h := by
      rw [← hh]; rfl
    rw [e] at h1
    obtain ⟨c1, hc1⟩ := h1
    obtain ⟨c2, hc2⟩ := hcur
    exact ⟨A * c1 + c2, by rw [Int.mul_add, ← hc2, ← Int.mul_assoc, Int.mul_comm _ A, Int.mul_assoc, ← hc1]; int_ring⟩
  let g : Nat → Nat := fun D => ((A * chain (q : Int) (PM q m) y0 b
    (fun l => jsumL q (qprimes q) (setD β k p v D l)) T - B0) % ((p ^ (h + 1) : Nat) : Int)).toNat
  have hgI : ∀ D, ((g D : Nat) : Int) = (A * chain (q : Int) (PM q m) y0 b
      (fun l => jsumL q (qprimes q) (setD β k p v D l)) T - B0) % ((p ^ (h + 1) : Nat) : Int) :=
    fun D => Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have hglt : ∀ D, g D < p ^ (h + 1) := by
    intro D
    have h1 := Int.emod_lt_of_pos (A * chain (q : Int) (PM q m) y0 b
      (fun l => jsumL q (qprimes q) (setD β k p v D l)) T - B0) hM0
    rw [← hgI D] at h1; omega
  have hgdv : ∀ D, D < p → p ^ h ∣ g D := by
    intro D hD
    have h1 := Int.emod_add_mul_ediv (A * chain (q : Int) (PM q m) y0 b
      (fun l => jsumL q (qprimes q) (setD β k p v D l)) T - B0) ((p ^ (h + 1) : Nat) : Int)
    have h2 : ((p ^ h : Nat) : Int) ∣ ((g D : Nat) : Int) := by
      rw [hgI D]
      have h3 := Int.dvd_sub (hYd D hD) (Int.dvd_trans hph (Int.dvd_mul_right _
        ((A * chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D l)) T - B0)
          / ((p ^ (h + 1) : Nat) : Int))))
      rwa [show A * chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D l)) T - B0
        - ((p ^ (h + 1) : Nat) : Int) * ((A * chain (q : Int) (PM q m) y0 b
          (fun l => jsumL q (qprimes q) (setD β k p v D l)) T - B0) / ((p ^ (h + 1) : Nat) : Int))
        = (A * chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D l)) T - B0)
          % ((p ^ (h + 1) : Nat) : Int) by omega] at h3
    exact Int.ofNat_dvd.mp h2
  have hginj : ∀ D1 D2, D1 < D2 → D2 < p → g D1 ≠ g D2 := by
    intro D1 D2 h12 h2p heq
    have hI1 := (hall D1 (by omega)).1
    obtain ⟨_, _, _, hx⟩ := op_pair hq hodd hm β hk hkT hTk hpL hlev h12 h2p (Or.inl hI1)
    rw [hh] at hx
    apply hx
    have h1 : (A * chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D1 l)) T - B0)
        % ((p ^ (h + 1) : Nat) : Int) =
        (A * chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D2 l)) T - B0)
        % ((p ^ (h + 1) : Nat) : Int) := by rw [← hgI, ← hgI, heq]
    have h2 := int_dvd_of_emod_eq h1
    rw [show A * chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D2 l)) T - B0
      - (A * chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D1 l)) T - B0)
      = A * (chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D2 l)) T
        - chain (q : Int) (PM q m) y0 b (fun l => jsumL q (qprimes q) (setD β k p v D1 l)) T) by int_ring] at h2
    -- cancel the unit A
    have hAn : Nat.Coprime (p ^ (h + 1)) A.natAbs :=
      Nat.Coprime.pow_left _ (isPrime_coprime hp.1 (fun hd' => hA (Int.natAbs_dvd_natAbs.mp
        (by rwa [Int.natAbs_natCast]))))
    have h3 := Int.natAbs_dvd_natAbs.mpr h2
    rw [Int.natAbs_natCast, Int.natAbs_mul] at h3
    exact Int.natAbs_dvd_natAbs.mp (by rw [Int.natAbs_natCast]; exact hAn.dvd_of_dvd_mul_left h3)
  -- pigeonhole
  have hL : ((List.range p).map g).Nodup := by
    have : ∀ n, n ≤ p → ((List.range n).map g).Nodup := by
      intro n
      induction n with
      | zero => intro _; exact List.nodup_nil
      | succ n ih =>
        intro hn
        rw [List.range_succ, List.map_append, List.nodup_append]
        refine ⟨ih (by omega), List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
        intro a ha c hc hac
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
        rw [List.map_cons, List.map_nil, List.mem_singleton] at hc
        subst hc
        exact hginj i n (List.mem_range.mp hi) (by omega) hac
    exact this p (Nat.le_refl p)
  have hsub : ∀ x ∈ (List.range p).map g, x ∈ (List.range p).map (fun t => p ^ h * t) := by
    intro x hx
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hx
    have hD' := List.mem_range.mp hD
    obtain ⟨t, ht⟩ := hgdv D hD'
    refine List.mem_map.mpr ⟨t, List.mem_range.mpr ?_, ht.symm⟩
    have h1 := hglt D
    rw [ht, Nat.pow_succ, Nat.mul_comm (p ^ h) p] at h1
    match Nat.lt_or_ge t p with
    | Or.inl hl => exact hl
    | Or.inr hge =>
      exfalso
      have : p ^ h * p ≤ p ^ h * t := Nat.mul_le_mul_left _ hge
      rw [Nat.mul_comm p (p ^ h)] at h1
      omega
  have hfull := nodup_full hL hsub (by simp only [List.length_map]; exact Nat.le_refl _)
  have h0 : 0 ∈ (List.range p).map (fun t => p ^ h * t) :=
    List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), Nat.mul_zero _⟩
  obtain ⟨D, hD, hgD⟩ := List.mem_map.mp (hfull 0 h0)
  have hD' := List.mem_range.mp hD
  refine ⟨D, hD', hbndD D hD', (hall D hD').1, ?_, (hall D hD').2⟩
  have h1 := hgI D
  rw [hgD] at h1
  exact Int.dvd_of_emod_eq_zero h1.symm

end Collatz
