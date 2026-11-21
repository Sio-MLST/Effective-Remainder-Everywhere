import Collatz.GeneralACore
import Collatz.GeneralLift

/-! Theorem A (generalAB.md, Sections 3–4): assembly from `core_A`, Proposition 1, and the
    parameter inequalities for E^*(a), E^{**}. -/

namespace Collatz

theorem iter_zero (q : Nat) : ∀ k, iter (collatz q) k 0 = 0
  | 0 => rfl
  | k + 1 => by
    show iter (collatz q) k (collatz q 0) = 0
    have : collatz q 0 = 0 := by simp [collatz]
    rw [this]; exact iter_zero q k

theorem reaches_pos {q x t : Nat} (ht : 1 ≤ t) (h : Reaches q x t) : 1 ≤ x := by
  rcases Nat.eq_zero_or_pos x with h0 | h0
  · subst h0; obtain ⟨k, hk⟩ := h; rw [iter_zero] at hk; omega
  · exact h0

theorem B0_mono {q m a a' : Nat} (h : a ≤ a') : B0 q m a ≤ B0 q m a' := by
  unfold B0
  split
  · exact Nat.mul_le_mul_left _ h
  · exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _

theorem Qt_mono {q m n n' : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) (h : n ≤ n') :
    Qt q m n ≤ Qt q m n' :=
  Nat.mul_le_mul_right _ (Wt_mono hq hodd hm h)

theorem pow_log2_le {N : Nat} (hN : 1 ≤ N) : 2 ^ Nat.log2 N ≤ N :=
  (Nat.le_log2 (by omega)).mp (Nat.le_refl _)

/-- First parameter inequality: 2^{α+Q̃(n)}(B+M+1) ≤ (B+1) t 2^{α+Q̃₀+max(c,Z)}. -/
theorem param_ineq1 (α Q0 Qn c Z B M t : Nat) (hQ : Qn ≤ Q0) (ht : 1 ≤ t) (hc : M + 1 ≤ 2 ^ c) :
    2 ^ (α + Qn) * (B + M + 1) ≤ (B + 1) * t * 2 ^ (α + Q0 + max c Z) := by
  have h1 : B + M + 1 ≤ (B + 1) * 2 ^ (max c Z) := by
    have h2 : 2 ^ c ≤ 2 ^ (max c Z) := Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
    have h3 : (B + 1) * (M + 1) ≤ (B + 1) * 2 ^ (max c Z) :=
      Nat.mul_le_mul_left _ (Nat.le_trans hc h2)
    have h4 : B + M + 1 ≤ (B + 1) * (M + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.one_mul]
      have := Nat.zero_le (B * M); omega
    omega
  have h5 : 2 ^ (α + Qn) ≤ 2 ^ (α + Q0) := Nat.pow_le_pow_right (by omega) (by omega)
  calc 2 ^ (α + Qn) * (B + M + 1) ≤ 2 ^ (α + Q0) * ((B + 1) * 2 ^ (max c Z)) :=
        Nat.mul_le_mul h5 h1
    _ = (B + 1) * 1 * 2 ^ (α + Q0 + max c Z) := by
        rw [Nat.pow_add 2 (α + Q0), Nat.mul_one]; simp only [Nat.mul_left_comm]
    _ ≤ (B + 1) * t * 2 ^ (α + Q0 + max c Z) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ht)

/-- Second parameter inequality: 2^{α+Q̃(n)+X} t ≤ (B+1) t 2^{α+Q̃₀+max(c, X − ⌊log₂ q^S⌋)} q^{n+S}. -/
theorem param_ineq2 (α Q0 Qn c X S n B t q : Nat) (hq : 1 ≤ q) (hQ : Qn ≤ Q0) :
    2 ^ (α + Qn + X) * t ≤ (B + 1) * t * 2 ^ (α + Q0 + max c (X - Nat.log2 (q ^ S))) * q ^ (n + S) := by
  have hqS : 1 ≤ q ^ S := Nat.pow_pos (by omega)
  have hL := pow_log2_le hqS
  have key : 2 ^ X ≤ 2 ^ (max c (X - Nat.log2 (q ^ S))) * q ^ S := by
    match Nat.lt_or_ge X (Nat.log2 (q ^ S)) with
    | Or.inl hlt =>
      have h1 : 2 ^ X ≤ 2 ^ Nat.log2 (q ^ S) := Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hlt)
      have h2 : q ^ S ≤ 2 ^ (max c (X - Nat.log2 (q ^ S))) * q ^ S :=
        Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))
      omega
    | Or.inr hge =>
      have e : 2 ^ X = 2 ^ (X - Nat.log2 (q ^ S)) * 2 ^ Nat.log2 (q ^ S) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [e]
      exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)) hL
  have h5 : 2 ^ (α + Qn) ≤ 2 ^ (α + Q0) := Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : q ^ S ≤ q ^ (n + S) := Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _)
  calc 2 ^ (α + Qn + X) * t = 2 ^ (α + Qn) * 2 ^ X * t := by rw [Nat.pow_add]
    _ ≤ 2 ^ (α + Q0) * (2 ^ (max c (X - Nat.log2 (q ^ S))) * q ^ (n + S)) * t :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul h5 (Nat.le_trans key (Nat.mul_le_mul_left _ h6)))
    _ = 1 * t * 2 ^ (α + Q0 + max c (X - Nat.log2 (q ^ S))) * q ^ (n + S) := by
        rw [Nat.pow_add 2 (α + Q0), Nat.one_mul]; simp only [Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (B + 1) * t * 2 ^ (α + Q0 + max c (X - Nat.log2 (q ^ S))) * q ^ (n + S) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))

theorem nfA_le {q m : Nat} (r : Nat) : nfA q m r ≤ alphaM m := by
  unfold nfA
  have := ones_le_length _ (tailw_bits q (alphaM m) (r % 2 ^ alphaM m))
  rwa [tailw_length] at this

/-- **Theorem A** (Coverage). -/
theorem general_theorem_A {q t : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (ht : 1 ≤ t) :
    TheoremA q t := by
  intro hx m hm
  obtain ⟨x0, hRx0, hHx0⟩ := hx
  have hd := dq_isOrder2 hq hodd
  have hdK : 1 ≤ dq q * q ^ KM q m := Nat.mul_pos hd.1 (Nat.pow_pos (by omega))
  have hc := ceilLog2_spec (MM q m + 1)
  have hQ : ∀ r, Qt q m (nfA q m r) ≤ Qt q m (alphaM m) := fun r => Qt_mono hq hodd hm (nfA_le r)
  refine ⟨nfA q m, fun r r' h => by unfold nfA; rw [h], fun r => nfA_le r, fun r B => ?_⟩
  -- the two parameter inequalities, for a given exponent bound
  have I1 : ∀ Z, 2 ^ (alphaM m + Qt q m (nfA q m r)) * (B + MM q m + 1) ≤
      (B + 1) * t * 2 ^ (alphaM m + Qt q m (alphaM m) + max (ceilLog2 (MM q m + 1)) Z) :=
    fun Z => param_ineq1 _ _ _ _ Z B (MM q m) t (hQ r) ht hc
  haveI hdA : DecidablePred (fun a => HypHa q a t) := fun a => by unfold HypHa; exact inferInstance
  have hdH : Decidable (HypH q t) :=
    decidable_of_iff (∃ a, a < dq q + 1 ∧ (1 ≤ a ∧ HypHa q a t))
      ⟨fun ⟨a, h1, h2, h3⟩ => ⟨a, h2, Nat.le_of_lt_succ h1, h3⟩,
        fun ⟨a, h1, h2, h3⟩ => ⟨a, Nat.lt_succ_of_le h2, h1, h3⟩⟩
  cases hdH with
  | isTrue hH =>
    -- if κ = 0, t satisfies (H) with a = 1 (Proposition 1)
    have hκ1 : κq q = 0 → HypHa q 1 t := by
      intro h0
      have hP := general_prop1 hq hodd ht
      obtain ⟨_, _, _, _, hk0, _⟩ := hP.2.2 (hP.2.1.1 (hP.1.1 ⟨t, ⟨0, rfl⟩, hH⟩))
      exact (hk0 h0).2
    clear hRx0 hHx0
    obtain ⟨a', ha1', haD', hHa'⟩ := hH
    have hsp := srch_spec (fun a => HypHa q a t) (dq q) 1 ⟨a', ha1', by omega, hHa'⟩
    have hge := srch_ge (fun a => HypHa q a t) (dq q) 1
    generalize hamin : srch (fun a => HypHa q a t) (dq q) 1 = amin at hsp hge
    obtain ⟨hHmin, hmin⟩ := hsp
    have hleA : ∀ a, 1 ≤ a → HypHa q a t → amin ≤ a := fun a ha1 hHa =>
      match Nat.lt_or_ge a amin with
      | Or.inl hlt => absurd hHa (hmin a ha1 hlt)
      | Or.inr h => h
    have hamD : amin ≤ dq q := Nat.le_trans (hleA a' ha1' hHa') haD'
    have hκa : κq q = 0 → amin = 1 := fun h0 => by
      have := hleA 1 (Nat.le_refl 1) (hκ1 h0); omega
    obtain ⟨w, hRw, hwm, hBw, hdisj⟩ := core_A hq hodd hm ht hge hamD hκa hHmin r B
    refine ⟨w, hRw, hwm, hBw, fun a ha1 _ hHa => ⟨?_, ?_, ?_⟩, fun hn => absurd ⟨a', ha1', haD', hHa'⟩ hn⟩
    · rcases hdisj with h | h
      · exact Or.inl h
      · right
        refine Nat.lt_of_lt_of_le h (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) ?_))
        have := B0_mono (q := q) (m := m) (hleA a ha1 hHa); omega
    · exact I1 _
    · have e : alphaM m + Qt q m (nfA q m r) + dq q * q ^ KM q m - 1
          + (sM q m - 1) * J0star q * PM q m + B0 q m a
          = alphaM m + Qt q m (nfA q m r) + (dq q * q ^ KM q m - 1
            + (sM q m - 1) * J0star q * PM q m + B0 q m a) := by omega
      rw [e]
      exact param_ineq2 _ _ _ _ _ (sM q m) (nfA q m r) B t q (by omega) (hQ r)
  | isFalse hH =>
    -- t does not satisfy (H): use Proposition 1
    have hP := general_prop1 hq hodd ht
    obtain ⟨x, hRx, _, hsz, hk0, hk1⟩ := hP.2.2 (hP.2.1.1 (hP.1.1 ⟨x0, hRx0, hHx0⟩))
    clear hP hHx0
    have hκ : 1 ≤ κq q := by
      rcases Nat.eq_zero_or_pos (κq q) with h0 | h0
      · exact absurd ⟨1, Nat.le_refl 1, hd.1, (hk0 h0).2⟩ hH
      · exact h0
    have hHa1 : HypHa q 1 x := ⟨0, hd.1, by rw [Int.pow_zero, Int.one_mul, Int.pow_one]; exact hk1 hκ⟩
    have hx1 := reaches_pos ht hRx
    obtain ⟨w, hRw, hwm, hBw, hdisj⟩ := core_A hq hodd hm hx1 (Nat.le_refl 1) hd.1 (fun _ => rfl) hHa1 r B
    refine ⟨w, reaches_trans q hRw hRx, hwm, hBw,
      fun a ha1 haD hHa => absurd ⟨a, ha1, haD, hHa⟩ hH, fun _ => ⟨?_, ?_, ?_⟩⟩
    · rcases hdisj with h | h
      · exact Or.inl h
      · right
        have hqk : 0 < q ^ (κq q + 1) := Nat.pow_pos (by omega)
        have e1 : nfA q m r + sM q m + κq q + 1 = (nfA q m r + sM q m) + (κq q + 1) := by omega
        rw [e1, Nat.pow_add, ← Nat.mul_assoc]
        have h2 := Nat.mul_lt_mul_of_pos_right h hqk
        refine Nat.lt_of_lt_of_le h2 ?_
        rw [Nat.mul_assoc]
        refine Nat.le_trans (Nat.mul_le_mul_left _ hsz) ?_
        rw [← Nat.mul_assoc, ← Nat.pow_add]
        apply Nat.le_of_eq
        congr 2
        rw [Nat.mul_comm (dq q * q) (κq q + 1), ← Nat.mul_assoc]
    · exact I1 _
    · have e : alphaM m + Qt q m (nfA q m r) + dq q * q ^ KM q m - 1
          + (sM q m - 1) * J0star q * PM q m + B0 q m 1 + (κq q + 1) * dq q * q
          = alphaM m + Qt q m (nfA q m r) + (dq q * q ^ KM q m - 1
            + (sM q m - 1) * J0star q * PM q m + B0 q m 1 + (κq q + 1) * dq q * q) := by omega
      have e2 : nfA q m r + sM q m + κq q + 1 = nfA q m r + (sM q m + κq q + 1) := by omega
      rw [e, e2]
      exact param_ineq2 _ _ _ _ _ (sM q m + κq q + 1) (nfA q m r) B t q (by omega) (hQ r)

end Collatz
