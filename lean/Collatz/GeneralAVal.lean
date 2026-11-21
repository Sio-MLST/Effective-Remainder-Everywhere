import Collatz.GeneralATail

/-! Theorem A, Step 1 valuations (generalAB.md Lemma 4) and a general "geometric visit"
    lemma used for Lemmas 5 and 13. Choice-free. -/

namespace Collatz

theorem val_zero_of_not_dvd {p f : Nat} (h : ¬ p ∣ f) : Val p 0 f :=
  ⟨by rw [Nat.pow_zero]; exact Nat.one_dvd _, by rw [Nat.zero_add, Nat.pow_one]; exact h⟩

theorem val_pow {p a x : Nat} (hp : IsPrime p) (hx : Val p a x) : ∀ n, Val p (n * a) (x ^ n)
  | 0 => by
    rw [Nat.zero_mul, Nat.pow_zero]
    exact ⟨Nat.one_dvd _, fun h => by
      have := Nat.le_of_dvd Nat.one_pos (by rwa [Nat.zero_add, Nat.pow_one] at h); have := hp.1; omega⟩
  | n + 1 => by
    rw [Nat.succ_mul, Nat.pow_succ]
    exact val_mul hp (val_pow hp hx n) hx

/-- For p ∣ q prime: Val p α_p q, with α_p ≥ 1. -/
theorem val_q {q p : Nat} (hq : 1 < q) (hp : IsPrime p) (hpq : p ∣ q) :
    Val p (vp p q) q ∧ 1 ≤ vp p q :=
  ⟨val_vp hp.1 (by omega), one_le_vp hp.1 (by omega) hpq⟩

/-- v_p(u_q) = v_p(u) for p ∣ q. -/
theorem val_uq {q p : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hp : IsPrime p) (hpq : p ∣ q) :
    Val p (vp p (uu q)) (uqq q) := by
  have hu := (uu_spec hq hodd).2
  have hv := val_vp hp.1 (show 0 < uu q by omega)
  generalize vp p (uu q) = v at hv ⊢
  have hvle : v ≤ Nat.log2 (uu q) + 1 := Nat.le_succ_of_le (val_le_log2 hp.1 (by omega) hv.1)
  have h1 : p ^ v ∣ q ^ (Nat.log2 (uu q) + 1) :=
    Nat.dvd_trans (Nat.pow_dvd_pow p hvle) (pow_dvd_pow_of_dvd' hpq _)
  refine ⟨Nat.dvd_gcd hv.1 h1, fun h => hv.2 (Nat.dvd_trans h (Nat.gcd_dvd_left _ _))⟩

/-- Lemma 1(2) for 2^d: v_p(2^{dN} − 1) = α_p + ν_p + v_p(N). -/
theorem val_2dN {q p N : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hp : IsPrime p) (hpq : p ∣ q)
    (hN : 0 < N) : Val p (vp p q + vp p (uu q) + vp p N) (2 ^ (dq q * N) - 1) := by
  have hdu : 2 ^ dq q = 1 + q * uu q := (uu_spec hq hodd).1
  have hu := (uu_spec hq hodd).2
  obtain ⟨hvq, hα⟩ := val_q hq hp hpq
  have hvu := val_vp hp.1 (show 0 < uu q by omega)
  have hx := val_mul hp hvq hvu
  have e : vp p q + vp p (uu q) = (vp p q + vp p (uu q) - 1) + 1 := by omega
  rw [e] at hx
  have h := lemma1_val hp (odd_of_dvd_odd hpq hodd) hx hN
  rw [← e] at h
  rw [Nat.pow_mul, hdu]; exact h

/-- Λ = q^{K+1} u_q. -/
def LamA (q m : Nat) : Nat := q ^ (KM q m + 1) * uqq q

/-- Lemma 4: v_p(2^{NP} − 1) = (K+1)α_p + ν_p + v_p(N). -/
theorem val_2PN {q m p N : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) (hp : IsPrime p)
    (hpq : p ∣ q) (hN : 0 < N) :
    Val p ((KM q m + 1) * vp p q + vp p (uu q) + vp p N) (2 ^ (N * PM q m) - 1) := by
  obtain ⟨f, hP, hf⟩ := PM_struct hq hodd hm
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · have := PM_pos hq hodd hm; rw [hP, h, Nat.mul_zero] at this; omega
    · exact h
  have hpf : ¬ p ∣ f := fun h => by
    have := Nat.dvd_gcd h hpq
    rw [hf] at this
    have := Nat.le_of_dvd Nat.one_pos this; have := hp.1; omega
  have hM : 0 < q ^ KM q m * f * N := Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by omega)) hf0) hN
  have h := val_2dN hq hodd hp hpq hM
  have hvM : Val p (KM q m * vp p q + 0 + vp p N) (q ^ KM q m * f * N) :=
    val_mul hp (val_mul hp (val_pow hp (val_q hq hp hpq).1 _) (val_zero_of_not_dvd hpf))
      (val_vp hp.1 hN)
  rw [val_unique (val_vp hp.1 hM) hvM] at h
  have e1 : N * PM q m = dq q * (q ^ KM q m * f * N) := by
    rw [hP]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have e2 : vp p q + vp p (uu q) + (KM q m * vp p q + 0 + vp p N)
      = (KM q m + 1) * vp p q + vp p (uu q) + vp p N := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  rw [e1, ← e2]; exact h

/-- Primes dividing N_q, Λ, q^k·u_q, … divide q. -/
theorem prime_dvd_q_of_dvd_qU {q p k : Nat} (hp : IsPrime p) (h : p ∣ q ^ k * uqq q) : p ∣ q := by
  rcases isPrime_dvd_mul hp h with h1 | h1
  · exact isPrime_dvd_pow hp k h1
  · exact isPrime_dvd_pow hp _ (Nat.dvd_trans h1 (uq_dvd_pow q (uu q)))

theorem val_qkU {q p k : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hp : IsPrime p) (hpq : p ∣ q) :
    Val p (k * vp p q + vp p (uu q)) (q ^ k * uqq q) :=
  val_mul hp (val_pow hp (val_q hq hp hpq).1 k) (val_uq hq hodd hp hpq)

/-- Divisibility from all prime-power valuations, for moduli whose primes divide q. -/
theorem dvd_of_val_le {q X Y : Nat} (hq : 1 < q) (hX : 1 ≤ X)
    (hXq : ∀ r, IsPrime r → r ∣ X → r ∣ q)
    (h : ∀ p, IsPrime p → p ∣ q → p ^ vp p X ∣ Y) : X ∣ Y := by
  have hL := qprimes_prime (show 1 ≤ q by omega)
  rw [pprod_eq hX (qprimes q) (qprimes_nodup q) hL
    (fun r hr hrX => (mem_qprimes (by omega)).mpr ⟨hr, hXq r hr hrX⟩)]
  exact pprod_dvd _ (qprimes_nodup q) hL
    (fun r hr => have h' := (mem_qprimes (show 1 ≤ q by omega)).mp hr; h r h'.1 h'.2)

/-- Λ ∣ 2^{NP} − 1. -/
theorem Lam_dvd {q m : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) (N : Nat) :
    LamA q m ∣ 2 ^ (N * PM q m) - 1 := by
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0; rw [Nat.zero_mul, Nat.pow_zero]; exact Nat.dvd_zero _
  apply dvd_of_val_le hq (Nat.mul_pos (Nat.pow_pos (by omega)) (uqq_pos hq hodd))
    (fun r hr h => prime_dvd_q_of_dvd_qU hr h)
  intro p hp hpq
  have hv := val_qkU (k := KM q m + 1) hq hodd hp hpq
  have hL : 0 < q ^ (KM q m + 1) * uqq q := Nat.mul_pos (Nat.pow_pos (by omega)) (uqq_pos hq hodd)
  rw [show vp p (q ^ (KM q m + 1) * uqq q) = (KM q m + 1) * vp p q + vp p (uu q) from
    val_unique (val_vp hp.1 hL) hv]
  exact Nat.dvd_trans (Nat.pow_dvd_pow p (Nat.le_add_right _ _)) (val_2PN hq hodd hm hp hpq hN).1

theorem div_lt_of_lt_mul' {x L W : Nat} (h : x < L * W) : x / L < W := by
  match Nat.lt_or_ge (x / L) W with
  | Or.inl hl => exact hl
  | Or.inr hge =>
    exfalso
    have h1 : L * W ≤ L * (x / L) := Nat.mul_le_mul_left L hge
    have h2 : L * (x / L) ≤ x := Nat.mul_div_le x L
    omega

/-! ### Pigeonhole: a full Nodup sublist -/

theorem nodup_full {L M : List Nat} (hnd : L.Nodup) (hsub : ∀ x ∈ L, x ∈ M)
    (hlen : M.length ≤ L.length) : ∀ x ∈ M, x ∈ L := by
  intro x hx
  match Decidable.em (x ∈ L) with
  | Or.inl h => exact h
  | Or.inr h =>
    exfalso
    have hsub' : ∀ y ∈ L, y ∈ rem x M := fun y hy =>
      mem_rem (fun e => h (by rw [← e]; exact hy)) (hsub y hy)
    have h1 := nodup_length_le _ hnd hsub'
    have h2 := rem_length hx
    omega

/-- Geometric visit: if v_p(g^Δ − 1) = v_p(L₀) + v_p(Δ) for all p ∣ q and Δ ≥ 1, and the
    primes of L₀, W divide q (with q ∣ L₀), then g^j (j < W) hits every class ≡ 1 (mod L₀)
    modulo L₀·W. -/
theorem geom_visit {q g L0 W : Nat} (hq : 1 < q) (hL0 : 1 ≤ L0) (hqL : q ∣ L0) (hW : 1 ≤ W)
    (hL0q : ∀ r, IsPrime r → r ∣ L0 → r ∣ q) (hWq : ∀ r, IsPrime r → r ∣ W → r ∣ q)
    (hg1 : 1 ≤ g) (hgL : g % L0 = 1 % L0)
    (hval : ∀ p Δ, IsPrime p → p ∣ q → 0 < Δ → p ^ (vp p L0 + vp p Δ) ∣ g ^ Δ - 1 ∧
      ¬ p ^ (vp p L0 + vp p Δ + 1) ∣ g ^ Δ - 1) :
    ∀ z, z % L0 = 1 % L0 → ∃ j, j < W ∧ g ^ j % (L0 * W) = z % (L0 * W) := by
  have hLW : 0 < L0 * W := Nat.mul_pos hL0 hW
  -- g is coprime to L0 W
  have hcop : Nat.Coprime g (L0 * W) := by
    apply coprime_of_no_prime
    intro p hp hpg hpLW
    have hpq : p ∣ q := by
      rcases isPrime_dvd_mul hp hpLW with h | h
      · exact hL0q p hp h
      · exact hWq p hp h
    have hpL : p ∣ L0 := Nat.dvd_trans hpq hqL
    have h1 : g % p = 1 % p := by
      rw [← Nat.mod_mod_of_dvd g hpL, hgL, Nat.mod_mod_of_dvd 1 hpL]
    have h2 : g % p = 0 := Nat.mod_eq_zero_of_dvd hpg
    have h3 : 1 % p = 1 := Nat.mod_eq_of_lt hp.1
    omega
  -- injectivity
  have hinj : ∀ i j, i < j → j < W → g ^ i % (L0 * W) ≠ g ^ j % (L0 * W) := by
    intro i j hij hjW heq
    have hΔ : 0 < j - i := by omega
    have hdiv : L0 * W ∣ g ^ (j - i) - 1 := by
      have e : g ^ j = g ^ i * g ^ (j - i) := by rw [← Nat.pow_add]; congr 1; omega
      have h1 : L0 * W ∣ g ^ i * (g ^ (j - i) - 1) := by
        have hle : g ^ i ≤ g ^ j := Nat.pow_le_pow_right hg1 (by omega)
        have := Nat.sub_mod_eq_zero_of_mod_eq heq.symm
        rw [e, ← Nat.mul_sub_one] at this
        exact Nat.dvd_of_mod_eq_zero this
      exact (Nat.Coprime.pow_left i hcop).symm.dvd_of_dvd_mul_left h1
    have hWd : W ∣ j - i := by
      apply dvd_of_val_le hq hW hWq
      intro p hp hpq
      have hv := hval p (j - i) hp hpq hΔ
      have hvLW := val_vp hp.1 hLW
      have hvL := val_vp hp.1 (show 0 < L0 by omega)
      have hvW := val_vp hp.1 (show 0 < W by omega)
      have hm := val_mul hp hvL hvW
      rw [val_unique hvLW hm] at hvLW
      have hle : vp p L0 + vp p W ≤ vp p L0 + vp p (j - i) := by
        match Nat.lt_or_ge (vp p L0 + vp p (j - i)) (vp p L0 + vp p W) with
        | Or.inr h => exact h
        | Or.inl h =>
          exact absurd (Nat.dvd_trans (Nat.pow_dvd_pow p (by omega)) (Nat.dvd_trans hvLW.1 hdiv)) hv.2
      exact Nat.dvd_trans (Nat.pow_dvd_pow p (by omega)) (val_vp hp.1 hΔ).1
    have := Nat.le_of_dvd hΔ hWd
    omega
  -- the lists
  have hA : ((List.range W).map (fun j => g ^ j % (L0 * W))).Nodup := by
    have : ∀ n, n ≤ W → ((List.range n).map (fun j => g ^ j % (L0 * W))).Nodup := by
      intro n
      induction n with
      | zero => intro _; exact List.nodup_nil
      | succ n ih =>
        intro hn
        rw [List.range_succ, List.map_append, List.nodup_append]
        refine ⟨ih (by omega), List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
        intro a ha b hb hab
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
        rw [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb
        exact hinj i n (List.mem_range.mp hi) (by omega) hab
    exact this W (Nat.le_refl W)
  have hsub : ∀ x ∈ (List.range W).map (fun j => g ^ j % (L0 * W)),
      x ∈ (List.range W).map (fun i => 1 % L0 + L0 * i) := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    have hgj : g ^ j % L0 = 1 % L0 := pow_mod_one _ _ _ hgL
    have hm : g ^ j % (L0 * W) % L0 = 1 % L0 := by
      rw [Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right L0 W), hgj]
    refine List.mem_map.mpr ⟨g ^ j % (L0 * W) / L0, List.mem_range.mpr ?_, ?_⟩
    · have := Nat.mod_lt (g ^ j) hLW
      exact div_lt_of_lt_mul' this
    · have := Nat.mod_add_div (g ^ j % (L0 * W)) L0
      rw [hm] at this; exact this
  have hfull := nodup_full hA hsub (by simp only [List.length_map]; exact Nat.le_refl _)
  intro z hz
  have hzm : z % (L0 * W) ∈ (List.range W).map (fun i => 1 % L0 + L0 * i) := by
    refine List.mem_map.mpr ⟨z % (L0 * W) / L0, List.mem_range.mpr ?_, ?_⟩
    · exact div_lt_of_lt_mul' (Nat.mod_lt z hLW)
    · have := Nat.mod_add_div (z % (L0 * W)) L0
      rw [Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right L0 W), hz] at this; exact this
  obtain ⟨j, hj, hjz⟩ := List.mem_map.mp (hfull _ hzm)
  exact ⟨j, List.mem_range.mp hj, hjz⟩

end Collatz
