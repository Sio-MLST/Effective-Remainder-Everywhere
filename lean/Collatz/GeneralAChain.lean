import Collatz.GeneralAStart

/-! Chain helpers for Theorem A (any odd q > 1, no NonWieferich): reachability along an
    integral path, the size bound q^i y_i ≤ 2^{Σ a_l} y₀, and independence of integrality
    at the last step from its shift. Choice-free. -/

namespace Collatz

/-- Along an integral path with y₀ = Y₀ ≥ 1 and b ≥ 1, every y_i is a natural number with
    y_i → Y₀. -/
theorem chain_reach {q : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (P : Nat) (y0 : Int)
    (b J : Nat → Nat) (n : Nat) (hI : Integral (q : Int) P y0 b J n) (hy0 : 1 ≤ y0)
    (hb : ∀ l, 1 ≤ l → l ≤ n → 1 ≤ b l) (Y0 : Nat) (hY0 : (Y0 : Int) = y0) :
    ∀ i, i ≤ n → ∃ yi : Nat, (yi : Int) = chain (q : Int) P y0 b J i ∧ Reaches q yi Y0
  | 0, _ => ⟨Y0, hY0, ⟨0, rfl⟩⟩
  | i + 1, hi => by
    obtain ⟨yi, hyi, hr⟩ := chain_reach hq hodd P y0 b J n hI hy0 hb Y0 hY0 i (by omega)
    have rel := chain_rel hI i (by omega)
    have hpos := chain_pos q (by omega) P y0 b J n hI hy0 hb (i + 1) hi
    obtain ⟨yN, hyN⟩ : ∃ y : Nat, (y : Int) = chain (q : Int) P y0 b J (i + 1) :=
      ⟨(chain (q : Int) P y0 b J (i + 1)).toNat, Int.toNat_of_nonneg (by omega)⟩
    refine ⟨yN, hyN, ?_⟩
    have hb1 := hb (i + 1) (by omega) hi
    have hnat : q * yN + 1 = 2 ^ (b (i + 1) + J (i + 1) * P) * yi := by
      apply Int.ofNat_inj.1
      simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow, Int.natCast_one]
      rw [hyN, hyi, Int.pow_add]
      exact rel
    have hodd' : yN % 2 = 1 := by
      have hev : 2 ^ (b (i + 1) + J (i + 1) * P) * yi % 2 = 0 := by
        have e : b (i + 1) + J (i + 1) * P = (b (i + 1) + J (i + 1) * P - 1) + 1 := by omega
        rw [e, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
        exact Nat.mul_mod_right _ _
      have hm := Nat.mul_mod q yN 2
      rw [hodd] at hm
      rcases Nat.mod_two_eq_zero_or_one yN with h | h
      · rw [h] at hm; omega
      · exact h
    exact reaches_trans q (reaches_of_step hodd' hnat) hr

/-- Size along an integral path: q^i y_i ≤ 2^{Σ_{l ≤ i} (b_l + J_l P)} y₀. -/
theorem chain_qsize {q : Nat} (hq : 1 < q) (P : Nat) (y0 : Int) (b J : Nat → Nat) (n : Nat)
    (hI : Integral (q : Int) P y0 b J n) (hy0 : 1 ≤ y0) (hb : ∀ l, 1 ≤ l → l ≤ n → 1 ≤ b l) :
    ∀ i, i ≤ n → (q : Int) ^ i * chain (q : Int) P y0 b J i
      ≤ (2 : Int) ^ (asum (fun l => b l + J l * P) i) * y0
  | 0, _ => by
    show (q : Int) ^ 0 * y0 ≤ (2 : Int) ^ 0 * y0
    rw [Int.pow_zero, Int.pow_zero]; exact Int.le_refl _
  | i + 1, hi => by
    have ih := chain_qsize hq P y0 b J n hI hy0 hb i (by omega)
    have rel := chain_rel hI i (by omega)
    have hpos := chain_pos q (by omega) P y0 b J n hI hy0 hb i (by omega)
    have hAs : (2 : Int) ^ (asum (fun l => b l + J l * P) (i + 1))
        = (2 : Int) ^ (b (i + 1)) * (2 : Int) ^ (J (i + 1) * P) * (2 : Int) ^ (asum (fun l => b l + J l * P) i) := by
      show (2 : Int) ^ (asum (fun l => b l + J l * P) i + (b (i + 1) + J (i + 1) * P)) = _
      rw [Int.pow_add, Int.pow_add]; int_ring
    rw [hAs]
    have hA : 0 ≤ (2 : Int) ^ (b (i + 1)) * (2 : Int) ^ (J (i + 1) * P) :=
      Int.mul_nonneg (Int.le_of_lt (Int.pow_pos (by omega))) (Int.le_of_lt (Int.pow_pos (by omega)))
    have hqi : 0 ≤ (q : Int) ^ i := Int.le_of_lt (Int.pow_pos (by omega))
    have h1 : (q : Int) ^ (i + 1) * chain (q : Int) P y0 b J (i + 1)
        ≤ (q : Int) ^ i * ((2 : Int) ^ (b (i + 1)) * (2 : Int) ^ (J (i + 1) * P) * chain (q : Int) P y0 b J i) := by
      rw [Int.pow_succ, Int.mul_assoc, ← rel]
      have := Int.mul_le_mul_of_nonneg_left (show (q : Int) * chain (q : Int) P y0 b J (i + 1)
        ≤ (q : Int) * chain (q : Int) P y0 b J (i + 1) + 1 by omega) hqi
      exact this
    have h2 : (q : Int) ^ i * ((2 : Int) ^ (b (i + 1)) * (2 : Int) ^ (J (i + 1) * P) * chain (q : Int) P y0 b J i)
        = (2 : Int) ^ (b (i + 1)) * (2 : Int) ^ (J (i + 1) * P) * ((q : Int) ^ i * chain (q : Int) P y0 b J i) := by
      int_ring
    have h3 := Int.mul_le_mul_of_nonneg_left ih hA
    rw [h2] at h1
    have e : (2 : Int) ^ (b (i + 1)) * (2 : Int) ^ (J (i + 1) * P) *
        ((2 : Int) ^ (asum (fun l => b l + J l * P) i) * y0)
        = (2 : Int) ^ (b (i + 1)) * (2 : Int) ^ (J (i + 1) * P) * (2 : Int) ^ (asum (fun l => b l + J l * P) i) * y0 := by
      int_ring
    rw [e] at h3
    exact Int.le_trans h1 h3

/-- Replacing the last shift keeps integrality (d ∣ P, so q ∣ 2^{jP} − 1). -/
theorem integral_update_last {q : Nat} {P : Nat} {y0 : Int} {b J : Nat → Nat} {s : Nat}
    (hP : (q : Int) ∣ (2 : Int) ^ P - 1) (hI : Integral (q : Int) P y0 b J s) (j : Nat) :
    Integral (q : Int) P y0 b (fun l => if l = s then j else J l) s := by
  intro i hi
  have hc : chain (q : Int) P y0 b (fun l => if l = s then j else J l) i = chain (q : Int) P y0 b J i :=
    (chain_congr (q : Int) P y0 b J _ i (fun l h1 h2 => by
      have : ¬ l = s := by omega
      simp only [this, ↓reduceIte])).symm
  rw [hc]
  by_cases hs : i + 1 = s
  · simp only [hs, ↓reduceIte]
    have h1 := hI i hi
    rw [hs] at h1
    have hG : ∀ k : Nat, (q : Int) ∣ (2 : Int) ^ (k * P) - 1 := fun k => pow_mod_one_int _ P k hP
    rw [step_int_iff _ _ _ _ j (hG j)]
    exact (step_int_iff _ _ _ _ (J s) (hG (J s))).mp h1
  · simp only [hs, ↓reduceIte]; exact hI i hi

end Collatz
