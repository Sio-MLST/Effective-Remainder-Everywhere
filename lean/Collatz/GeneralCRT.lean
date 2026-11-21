import Collatz.GeneralReach

/-! Prime-power products over a list of primes and the prime list `qprimes`
    (pure ℕ, choice-free). No CRT is needed: per-prime separation is done by the
    weights E_p^* (GeneralAOp) and unit cancellation by `int_cancel`. -/

namespace Collatz

/-- ∏_{p ∈ L} p^{f p}. -/
def pprod (f : Nat → Nat) (L : List Nat) : Nat := L.foldl (fun acc p => acc * p ^ f p) 1

theorem pprod_acc (f : Nat → Nat) :
    ∀ (L : List Nat) (acc : Nat), L.foldl (fun a p => a * p ^ f p) acc = acc * pprod f L
  | [], acc => by simp [pprod]
  | p :: L, acc => by
    show L.foldl (fun a p => a * p ^ f p) (acc * p ^ f p) = acc * L.foldl (fun a p => a * p ^ f p) (1 * p ^ f p)
    rw [pprod_acc f L, pprod_acc f L, Nat.one_mul, Nat.mul_assoc]

theorem pprod_nil (f : Nat → Nat) : pprod f [] = 1 := rfl

theorem pprod_cons (f : Nat → Nat) (p : Nat) (L : List Nat) :
    pprod f (p :: L) = p ^ f p * pprod f L := by
  show L.foldl (fun a p => a * p ^ f p) (1 * p ^ f p) = _
  rw [pprod_acc, Nat.one_mul]

/-- Distinct primes are coprime. -/
theorem isPrime_coprime_of_ne {p p' : Nat} (hp : IsPrime p) (hp' : IsPrime p') (hne : p ≠ p') :
    Nat.Coprime p p' := by
  rcases hp.2 _ (Nat.gcd_dvd_left p p') with h | h
  · exact h
  · exfalso
    have hd : p ∣ p' := h ▸ Nat.gcd_dvd_right p p'
    rcases hp'.2 p hd with h1 | h1
    · have := hp.1; omega
    · exact hne h1

theorem coprime_pow_pprod {f : Nat → Nat} {p : Nat} (hp : IsPrime p) (a : Nat) :
    ∀ (L : List Nat), (∀ r ∈ L, IsPrime r) → p ∉ L → Nat.Coprime (p ^ a) (pprod f L)
  | [], _, _ => by rw [pprod_nil]; exact Nat.coprime_one_right _
  | r :: L, hL, hnot => by
    rw [pprod_cons]
    have hr : IsPrime r := hL r (List.mem_cons_self ..)
    have hne : p ≠ r := fun h => hnot (h ▸ List.mem_cons_self ..)
    have hnot' : p ∉ L := fun h => hnot (List.mem_cons_of_mem _ h)
    exact Nat.Coprime.mul_right (Nat.Coprime.pow a (f r) (isPrime_coprime_of_ne hp hr hne))
      (coprime_pow_pprod hp a L (fun s hs => hL s (List.mem_cons_of_mem _ hs)) hnot')

theorem dvd_pprod (f : Nat → Nat) {p : Nat} : ∀ (L : List Nat), p ∈ L → p ^ f p ∣ pprod f L
  | [], h => absurd h (List.not_mem_nil)
  | r :: L, h => by
    rw [pprod_cons]
    rcases List.mem_cons.mp h with h1 | h1
    · subst h1; exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_trans (dvd_pprod f L h1) (Nat.dvd_mul_left _ _)

/-- Pairwise coprime prime powers dividing n: their product divides n. -/
theorem pprod_dvd {f : Nat → Nat} {n : Nat} :
    ∀ (L : List Nat), L.Nodup → (∀ r ∈ L, IsPrime r) → (∀ r ∈ L, r ^ f r ∣ n) → pprod f L ∣ n
  | [], _, _, _ => by rw [pprod_nil]; exact Nat.one_dvd _
  | r :: L, hnd, hL, hdv => by
    rw [pprod_cons]
    have hnd' := List.nodup_cons.mp hnd
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (coprime_pow_pprod (hL r (List.mem_cons_self ..)) _ L
        (fun s hs => hL s (List.mem_cons_of_mem _ hs)) hnd'.1)
      (hdv r (List.mem_cons_self ..))
      (pprod_dvd L hnd'.2 (fun s hs => hL s (List.mem_cons_of_mem _ hs))
        (fun s hs => hdv s (List.mem_cons_of_mem _ hs)))

/-- Prime-power decomposition: if L is a Nodup list of primes containing every prime
    divisor of n ≥ 1, then n = ∏_{p ∈ L} p^{v_p(n)}. -/
theorem pprod_eq {n : Nat} (hn : 1 ≤ n) (L : List Nat) (hnd : L.Nodup)
    (hL : ∀ r ∈ L, IsPrime r) (hall : ∀ r, IsPrime r → r ∣ n → r ∈ L) :
    n = pprod (fun p => vp p n) L := by
  have hP : pprod (fun p => vp p n) L ∣ n :=
    pprod_dvd L hnd hL (fun r hr => (val_vp (hL r hr).1 hn).1)
  obtain ⟨c, hc⟩ := hP
  match Nat.lt_or_ge 1 c with
  | Or.inr hle =>
    match Nat.eq_zero_or_pos c with
    | Or.inl h0 => rw [h0, Nat.mul_zero] at hc; omega
    | Or.inr hpos =>
      have : c = 1 := by omega
      rw [this, Nat.mul_one] at hc; exact hc
  | Or.inl hgt =>
    exfalso
    obtain ⟨r, hr, hrc⟩ := exists_prime_dvd c hgt
    have hrn : r ∣ n := hc ▸ Nat.dvd_trans hrc (Nat.dvd_mul_left _ _)
    have hmem := hall r hr hrn
    have h1 := dvd_pprod (fun p => vp p n) L hmem
    have hv := val_vp hr.1 hn
    have hd : r ^ (vp r n + 1) ∣ n := by
      conv => rhs; rw [hc]
      rw [Nat.pow_succ]
      exact Nat.mul_dvd_mul h1 hrc
    exact hv.2 hd

theorem isPrime_of_isPrimeB {p : Nat} (h : isPrimeB p = true) : IsPrime p := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨h2, hall⟩ := h
  refine ⟨h2, fun a ha => ?_⟩
  have hap : a ≤ p := Nat.le_of_dvd (by omega) ha
  match Nat.lt_or_ge a p with
  | Or.inr hge => exact Or.inr (by omega)
  | Or.inl hlt =>
    rcases hall a hlt with h3 | h3
    · have h3' : a < 2 := h3
      match Nat.eq_zero_or_pos a with
      | Or.inl h0 => subst h0; have := Nat.eq_zero_of_zero_dvd ha; omega
      | Or.inr _ => exact Or.inl (by omega)
    · exact absurd (Nat.mod_eq_zero_of_dvd ha) h3

theorem isPrimeB_of_isPrime {p : Nat} (h : IsPrime p) : isPrimeB p = true := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  refine ⟨h.1, fun a ha => ?_⟩
  match Nat.lt_or_ge a 2 with
  | Or.inl hlt => exact Or.inl hlt
  | Or.inr hge =>
    refine Or.inr (fun h0 => ?_)
    rcases h.2 a (Nat.dvd_of_mod_eq_zero h0) with h1 | h1 <;> omega

theorem mem_qprimes {q p : Nat} (hq : 1 ≤ q) : p ∈ qprimes q ↔ IsPrime p ∧ p ∣ q := by
  unfold qprimes
  rw [List.mem_filter, List.mem_range]
  constructor
  · intro ⟨_, hb⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    exact ⟨isPrime_of_isPrimeB hb.1, Nat.dvd_of_mod_eq_zero hb.2⟩
  · intro ⟨hp, hd⟩
    refine ⟨Nat.lt_succ_of_le (Nat.le_of_dvd hq hd), ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨isPrimeB_of_isPrime hp, Nat.mod_eq_zero_of_dvd hd⟩

theorem nodup_range' : ∀ n, (List.range n).Nodup
  | 0 => by rw [List.range_zero]; exact List.nodup_nil
  | n + 1 => by
    rw [List.range_succ, List.nodup_append]
    refine ⟨nodup_range' n, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro a ha b hb
    rw [List.mem_range] at ha
    rw [List.mem_singleton] at hb
    omega

theorem nodup_filter' (f : Nat → Bool) : ∀ (l : List Nat), l.Nodup → (l.filter f).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    have h' := List.nodup_cons.mp h
    rw [List.filter_cons]
    split
    · exact List.nodup_cons.mpr ⟨fun hm => h'.1 (List.mem_filter.mp hm).1, nodup_filter' f l h'.2⟩
    · exact nodup_filter' f l h'.2

theorem qprimes_nodup (q : Nat) : (qprimes q).Nodup :=
  nodup_filter' _ _ (nodup_range' _)

theorem qprimes_prime {q : Nat} (hq : 1 ≤ q) : ∀ r ∈ qprimes q, IsPrime r :=
  fun _ hr => ((mem_qprimes hq).mp hr).1

/-- Halving: e Col-steps take 2^e y to y. -/
theorem iter_pow2 (q : Nat) : ∀ e y, iter (collatz q) e (2 ^ e * y) = y
  | 0, y => by simp [iter]
  | e + 1, y => by
    show iter (collatz q) e (collatz q (2 ^ (e + 1) * y)) = y
    have : 2 ^ (e + 1) * y = 2 * (2 ^ e * y) := by rw [Nat.pow_succ]; nat_ring
    rw [this, collatz_double]
    exact iter_pow2 q e y

/-- An odd step q·x + 1 = 2^e·y gives x → y. -/
theorem reaches_of_step {q x y e : Nat} (hx : x % 2 = 1) (h : q * x + 1 = 2 ^ e * y) :
    Reaches q x y := by
  refine ⟨e + 1, ?_⟩
  show iter (collatz q) e (collatz q x) = y
  have hc : collatz q x = q * x + 1 := by simp [collatz, hx]
  rw [hc, h]
  exact iter_pow2 q e y

/-- Remove the first occurrence of a. -/
def rem (a : Nat) : List Nat → List Nat
  | [] => []
  | b :: M => if b = a then M else b :: rem a M

theorem rem_length {a : Nat} : ∀ {M : List Nat}, a ∈ M → (rem a M).length + 1 = M.length
  | [], h => absurd h List.not_mem_nil
  | b :: M, h => by
    unfold rem
    by_cases hb : b = a
    · simp only [hb, ↓reduceIte, List.length_cons]
    · simp only [hb, ↓reduceIte, List.length_cons]
      rcases List.mem_cons.mp h with h1 | h1
      · exact absurd h1.symm hb
      · rw [rem_length h1]

theorem mem_rem {a b : Nat} (hne : b ≠ a) : ∀ {M : List Nat}, b ∈ M → b ∈ rem a M
  | [], h => absurd h List.not_mem_nil
  | c :: M, h => by
    unfold rem
    by_cases hc : c = a
    · simp only [hc, ↓reduceIte]
      rcases List.mem_cons.mp h with h1 | h1
      · exact absurd (h1.trans hc) hne
      · exact h1
    · simp only [hc, ↓reduceIte]
      rcases List.mem_cons.mp h with h1 | h1
      · rw [h1]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_rem hne h1)

/-- Pigeonhole: a Nodup list contained in M is no longer than M. -/
theorem nodup_length_le : ∀ {L : List Nat} (M : List Nat), L.Nodup → (∀ x ∈ L, x ∈ M) →
    L.length ≤ M.length
  | [], _, _, _ => Nat.zero_le _
  | a :: L, M, hnd, hsub => by
    have hnd' := List.nodup_cons.mp hnd
    have ha : a ∈ M := hsub a (List.mem_cons_self ..)
    have hL : ∀ x ∈ L, x ∈ rem a M := fun x hx =>
      mem_rem (fun h => hnd'.1 (by rw [← h]; exact hx)) (hsub x (List.mem_cons_of_mem _ hx))
    have := nodup_length_le (rem a M) hnd'.2 hL
    have h2 := rem_length ha
    rw [List.length_cons]
    omega

end Collatz
