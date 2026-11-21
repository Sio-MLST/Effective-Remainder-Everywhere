import Collatz.GeneralProp1

/-! Natural-number form of Hypothesis (H), used by the Edge z → c_a lemma.
    HypHa q a x (Int divisibility) gives  2^{i0} · x · bco ≡ 1 (mod N_q)  in ℕ. -/

namespace Collatz

theorem bco_cast (q a : Nat) (hq : 1 < q) (hodd : q % 2 = 1) :
    ((bco q a : Nat) : Int) = (2 : Int) ^ a - (q : Int) + (Nqq q : Int) := by
  have h2 : q ≤ Nqq q := Nat.le_mul_of_pos_right q (uqq_pos hq hodd)
  have h1 : q ≤ 2 ^ a + Nqq q := Nat.le_trans h2 (Nat.le_add_left _ _)
  unfold bco
  rw [Int.ofNat_sub h1, Int.natCast_add, Int.natCast_pow]
  have e2 : ((2 : Nat) : Int) = 2 := rfl
  rw [e2]
  omega

theorem bco_pos (q a : Nat) (hq : 1 < q) (hodd : q % 2 = 1) : 1 ≤ bco q a := by
  have h2 : q ≤ Nqq q := Nat.le_mul_of_pos_right q (uqq_pos hq hodd)
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  unfold bco
  omega

/-- Hypothesis (H) for x ≥ 1 gives 2^{i0}·x·bco ≡ 1 (mod N_q) in ℕ. -/
theorem hypha_nat {q a x : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hx : 1 ≤ x)
    (hH : HypHa q a x) : ∃ i0, i0 < dq q ∧ 2 ^ i0 * x * bco q a % Nqq q = 1 % Nqq q := by
  obtain ⟨i0, hi0, hdvd⟩ := hH
  refine ⟨i0, hi0, ?_⟩
  have hN := Nqq_gt hq hodd
  have hbp := bco_pos q a hq hodd
  have hY : 1 ≤ 2 ^ i0 * x * bco q a :=
    Nat.mul_pos (Nat.mul_pos Nat.one_le_two_pow hx) hbp
  -- cast of Y − 1 equals the Int expression plus N·2^{i0}x
  have hcastY : ((2 ^ i0 * x * bco q a : Nat) : Int)
      = (2 : Int) ^ i0 * (x : Int) * ((2 : Int) ^ a - (q : Int) + (Nqq q : Int)) := by
    rw [Int.natCast_mul, Int.natCast_mul, Int.natCast_pow, bco_cast q a hq hodd]
    have e2 : ((2 : Nat) : Int) = 2 := rfl
    rw [e2]
  have hcastSub : (((2 ^ i0 * x * bco q a) - 1 : Nat) : Int)
      = ((2 ^ i0 * x * bco q a : Nat) : Int) - 1 := by
    rw [Int.ofNat_sub hY]; rfl
  have hEq : (((2 ^ i0 * x * bco q a) - 1 : Nat) : Int)
      = ((2 : Int) ^ i0 * (x : Int) * ((2 : Int) ^ a - (q : Int)) - 1)
        + (Nqq q : Int) * ((2 : Int) ^ i0 * (x : Int)) := by
    rw [hcastSub, hcastY]
    simp only [Int.mul_add, Int.mul_sub, Int.mul_comm, Int.mul_left_comm, Int.add_sub_assoc]
    omega
  have hdvdN : (Nqq q : Int) ∣ (((2 ^ i0 * x * bco q a) - 1 : Nat) : Int) := by
    rw [hEq]
    exact Int.dvd_add hdvd (Int.dvd_mul_right _ _)
  have hdvdNat : Nqq q ∣ (2 ^ i0 * x * bco q a) - 1 := Int.ofNat_dvd.mp hdvdN
  obtain ⟨c, hc⟩ := hdvdNat
  have hYc : 2 ^ i0 * x * bco q a = Nqq q * c + 1 := by omega
  rw [hYc]
  simp [Nat.add_mod, Nat.mul_mod_right]

end Collatz
