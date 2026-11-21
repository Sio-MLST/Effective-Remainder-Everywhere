import Collatz.CoveringTS

namespace Collatz

theorem backstep_reaches (q : Nat) [NonWieferich q] (y y' a : Nat) (ha : 1 ≤ a)
    (h : q * y + 1 = 2 ^ a * y') : Reaches q y y' := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  have h2 : q * y + 1 = 2 * (2 ^ a' * y') := by rw [h, Nat.pow_succ]; ac_rfl
  have hyodd : y % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy
    · have hqy : (q * y) % 2 = 0 := by rw [Nat.mul_mod, hy]; simp
      omega
    · exact hy
  have hc : collatz q y = q * y + 1 := by
    unfold collatz; simp [show ¬ (y % 2 = 0) by omega]
  have h1 : Reaches q y (q * y + 1) := ⟨1, by simp [iter, hc]⟩
  have h2' : Reaches q (q * y + 1) y' := by
    have := reaches_pow2 q y' (a' + 1)
    rw [← h] at this
    exact this
  exact reaches_trans q h1 h2'

theorem cover_int (q u K M : Nat) (hp : q % 2 = 1) (hq3 : 3 ≤ q) (hu : Nat.Coprime q u)
    (X : Int) (hX : (q : Int) ^ (K + 1) ∣ X - 1) :
    ∃ t : Nat, t < q ^ M ∧ ∀ j : Nat, j % q ^ M = t →
      (q : Int) ^ (K + 1 + M) ∣ ((1 + q ^ (K + 1) * u : Nat) : Int) ^ j - X := by
  have hq1 : 1 < q := by omega
  have hQ1 : 1 < q ^ (K + 1) := Nat.lt_of_lt_of_le hq1 (Nat.le_self_pow (by omega) q)
  have hmm : 1 < q ^ (K + 1 + M) := Nat.lt_of_lt_of_le hq1 (Nat.le_self_pow (by omega) q)
  have hmI : ((q ^ (K + 1 + M) : Nat) : Int) = (q : Int) ^ (K + 1 + M) := Int.natCast_pow _ _
  have hQI : ((q ^ (K + 1) : Nat) : Int) = (q : Int) ^ (K + 1) := Int.natCast_pow _ _
  have hqM : (q : Int) ^ (K + 1 + M) = (q : Int) ^ (K + 1) * (q : Int) ^ M := Int.pow_add _ _ _
  have hmpos : (0 : Int) < (q : Int) ^ (K + 1 + M) := by rw [← hmI]; omega
  have hmne : (q : Int) ^ (K + 1 + M) ≠ 0 := by omega
  obtain ⟨Y, hY⟩ : ∃ Y : Nat, (Y : Int) = X % (q : Int) ^ (K + 1 + M) :=
    ⟨(X % (q : Int) ^ (K + 1 + M)).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ hmne)⟩
  have hYlt' : (Y : Int) < (q : Int) ^ (K + 1 + M) := by
    rw [hY]; exact Int.emod_lt_of_pos _ hmpos
  have hYlt : Y < q ^ (K + 1 + M) := by
    rw [← hmI] at hYlt'; omega
  have hYmod : Y % q ^ (K + 1) = 1 := by
    have h1 : (Y : Int) % (q : Int) ^ (K + 1) = 1 := by
      rw [hY, Int.emod_emod_of_dvd _ ⟨(q : Int) ^ M, hqM⟩]
      obtain ⟨g0, hg0⟩ := hX
      have hXe : X = 1 + (q : Int) ^ (K + 1) * g0 := by omega
      rw [hXe, Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by omega) (by rw [← hQI]; omega)
    have h2 := Int.natCast_emod Y (q ^ (K + 1))
    rw [hQI] at h2
    omega
  obtain ⟨t, ht, hte⟩ := unit_power_cover (u := u) hp hq3 (by omega : 1 ≤ K + 1) hu M Y hYmod
  refine ⟨t, ht, fun j hj => ?_⟩
  have hper : (1 + q ^ (K + 1) * u) ^ (q ^ M) % q ^ (K + 1 + M) = 1 :=
    (order_iff hp hq3 (by omega : 1 ≤ K + 1) hu M (q ^ M)).2 (Nat.dvd_refl _)
  have hjdec : j = t + q ^ M * (j / q ^ M) := by
    have := Nat.div_add_mod j (q ^ M); omega
  have hgj : (1 + q ^ (K + 1) * u) ^ j % q ^ (K + 1 + M) = Y := by
    have e1 : (1 + q ^ (K + 1) * u) ^ j
        = (1 + q ^ (K + 1) * u) ^ t * ((1 + q ^ (K + 1) * u) ^ (q ^ M)) ^ (j / q ^ M) := by
      conv => lhs; rw [hjdec]
      rw [Nat.pow_add, Nat.pow_mul]
    have hk : ((1 + q ^ (K + 1) * u) ^ (q ^ M)) ^ (j / q ^ M) % q ^ (K + 1 + M) = 1 := by
      rw [Nat.pow_mod, hper, Nat.one_pow, Nat.mod_eq_of_lt hmm]
    rw [e1, Nat.mul_mod, hk, Nat.mul_one, Nat.mod_mod, hte, Nat.mod_eq_of_lt hYlt]
  have hdm := Nat.div_add_mod ((1 + q ^ (K + 1) * u) ^ j) (q ^ (K + 1 + M))
  rw [hgj] at hdm
  have hcast : (((1 + q ^ (K + 1) * u) ^ j : Nat) : Int)
      = (q : Int) ^ (K + 1 + M) * (((1 + q ^ (K + 1) * u) ^ j / q ^ (K + 1 + M) : Nat) : Int) + (Y : Int) := by
    rw [← hmI]
    have := congrArg (fun n : Nat => (n : Int)) hdm
    simp only [Int.natCast_add, Int.natCast_mul] at this
    exact this.symm
  rw [Int.natCast_pow] at hcast
  have hY2 : (Y : Int) = X - (q : Int) ^ (K + 1 + M) * (X / (q : Int) ^ (K + 1 + M)) := by
    rw [hY, Int.emod_def]
  refine ⟨(((1 + q ^ (K + 1) * u) ^ j / q ^ (K + 1 + M) : Nat) : Int) - X / (q : Int) ^ (K + 1 + M), ?_⟩
  rw [Int.mul_sub]
  omega


end Collatz
