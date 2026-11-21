import Collatz.GeneralAChain

/-! Theorem A, Lemma 13 (tight wide step) and the least-k₀ choice of Step 5
    (generalAB.md). Choice-free. -/

namespace Collatz

theorem mq_pos {q m : Nat} (hm : 1 ≤ m) : 1 ≤ mqM q m := by
  have := Nat.gcd_pos_of_pos_left (q ^ oddM m) (oddM_pos (m := m) hm)
  exact this

theorem qKU_pos {q m : Nat} (hq : 1 < q) (hodd : q % 2 = 1) : 0 < q ^ KM q m * uqq q :=
  Nat.mul_pos (Nat.pow_pos (by omega)) (uqq_pos hq hodd)

theorem Wt_mul {q m n : Nat} :
    q ^ KM q m * uqq q * Wt q m n = Nat.lcm (q ^ n * mqM q m) (q ^ KM q m * uqq q) :=
  Nat.mul_div_cancel' (Nat.dvd_lcm_right _ _)

theorem Wt_pos {q m n : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) : 1 ≤ Wt q m n := by
  have hL : 0 < Nat.lcm (q ^ n * mqM q m) (q ^ KM q m * uqq q) :=
    Nat.lcm_pos (Nat.mul_pos (Nat.pow_pos (by omega)) (mq_pos hm)) (qKU_pos hq hodd)
  rw [← Wt_mul] at hL
  rcases Nat.eq_zero_or_pos (Wt q m n) with h | h
  · rw [h, Nat.mul_zero] at hL; omega
  · exact h

theorem Wt_primes {q m n : Nat} (_hq : 1 < q) (_hodd : q % 2 = 1) :
    ∀ r, IsPrime r → r ∣ Wt q m n → r ∣ q := by
  intro r hr h
  have h1 : r ∣ Nat.lcm (q ^ n * mqM q m) (q ^ KM q m * uqq q) := by
    rw [← Wt_mul]; exact Nat.dvd_trans h (Nat.dvd_mul_left _ _)
  have h2 : r ∣ (q ^ n * mqM q m) * (q ^ KM q m * uqq q) :=
    Nat.dvd_trans h1 (Nat.lcm_dvd (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _))
  rcases isPrime_dvd_mul hr h2 with h3 | h3
  · rcases isPrime_dvd_mul hr h3 with h4 | h4
    · exact isPrime_dvd_pow hr n h4
    · exact isPrime_dvd_pow hr _ (Nat.dvd_trans h4 (mq_dvd_pow q m))
  · exact prime_dvd_q_of_dvd_qU hr h3

theorem Wt_mono {q m n n' : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) (h : n ≤ n') :
    Wt q m n ≤ Wt q m n' := by
  unfold Wt
  apply Nat.div_le_div_right
  apply Nat.le_of_dvd
  · exact Nat.lcm_pos (Nat.mul_pos (Nat.pow_pos (by omega)) (mq_pos hm)) (qKU_pos hq hodd)
  · exact Nat.lcm_dvd (Nat.dvd_trans (Nat.mul_dvd_mul_right (Nat.pow_dvd_pow q h) _)
      (Nat.dvd_lcm_left _ _)) (Nat.dvd_lcm_right _ _)

/-- Int divisibility of a difference of naturals gives equal residues. -/
theorem nat_mod_of_int_dvd {a b M : Nat} (h : (M : Int) ∣ (a : Int) - (b : Int)) : a % M = b % M := by
  obtain ⟨c, hc⟩ := h
  have h1 : (a : Int) = (b : Int) + (M : Int) * c := by omega
  have h2 : ((a % M : Nat) : Int) = ((b % M : Nat) : Int) := by
    rw [Int.natCast_emod, Int.natCast_emod, h1, Int.add_mul_emod_self_left]
  exact_mod_cast h2

/-- 2^{WP} ≡ 1 (mod Λ W) for W with primes dividing q. -/
theorem LamW_dvd {q m W : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m) (hW : 1 ≤ W)
    (hWq : ∀ r, IsPrime r → r ∣ W → r ∣ q) : LamA q m * W ∣ 2 ^ (W * PM q m) - 1 := by
  have hL := LamA_pos (m := m) hq hodd
  apply dvd_of_val_le hq (Nat.mul_pos hL hW)
    (fun r hr h => by
      rcases isPrime_dvd_mul hr h with h1 | h1
      · exact prime_dvd_q_of_dvd_LamA hr h1
      · exact hWq r hr h1)
  intro p hp hpq
  have hv := val_mul hp (val_vp hp.1 hL) (val_vp hp.1 (show 0 < W by omega))
  rw [val_unique (val_vp hp.1 (Nat.mul_pos hL hW)) hv]
  have hvL := val_qkU (k := KM q m + 1) hq hodd hp hpq
  have hLe : vp p (LamA q m) = (KM q m + 1) * vp p q + vp p (uu q) :=
    val_unique (val_vp hp.1 hL) hvL
  rw [hLe]
  exact (val_2PN hq hodd hm hp hpq hW).1

/-- Lemma 13 with the least k₀ (Step 5). -/
theorem gwide_step {q m n s : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hm : 1 ≤ m)
    {y0 : Int} {b J : Nat → Nat} (hs1 : 1 ≤ s) (hI : Integral (q : Int) (PM q m) y0 b J s)
    (hJs : J s = 0) (hy0 : 1 ≤ y0) (hb : ∀ l, 1 ≤ l → l ≤ s → 1 ≤ b l) (hbP : b s ≤ PM q m)
    (ρ Θ : Nat) (hρ : ((q ^ KM q m * uqq q : Nat) : Int) ∣ chain (q : Int) (PM q m) y0 b J s - ρ) :
    ∃ j Y Ys : Nat, (Y : Int) = chain (q : Int) (PM q m) y0 b J (s - 1) ∧
      (Ys : Int) = chain (q : Int) (PM q m) y0 b (fun l => if l = s then j else J l) s ∧
      Integral (q : Int) (PM q m) y0 b (fun l => if l = s then j else J l) s ∧
      q * Ys + 1 = 2 ^ (b s + j * PM q m) * Y ∧ Θ ≤ Ys ∧
      Ys % (q ^ KM q m * uqq q * Wt q m n) = ρ % (q ^ KM q m * uqq q * Wt q m n) ∧
      (b s + j * PM q m ≤ Wt q m n * PM q m ∨
        2 ^ (b s + j * PM q m) * Y ≤ 2 ^ (Wt q m n * PM q m) * (q * Θ)) := by
  have hL := LamA_pos (m := m) hq hodd
  have hLg := LamA_gt (m := m) hq hodd
  have hW := Wt_pos (n := n) hq hodd hm
  have hP0 := PM_pos hq hodd hm
  generalize hWd : Wt q m n = W at hW ⊢
  generalize hPd : PM q m = P at hP0 hI hρ hbP ⊢
  have hWq : ∀ r, IsPrime r → r ∣ W → r ∣ q := fun r hr h => Wt_primes (n := n) hq hodd r hr (hWd ▸ h)
  have hqL : q ∣ LamA q m := Nat.dvd_trans (Nqq_dvd q) (by rw [LamA_eq]; exact Nat.dvd_mul_right _ _)
  have hLam1 : (LamA q m : Int) ∣ (2 : Int) ^ P - 1 := by
    have h := Lam_dvd (m := m) hq hodd hm 1
    rw [Nat.one_mul, hPd] at h
    have e : ((2 ^ P - 1 : Nat) : Int) = (2 : Int) ^ P - 1 := by
      rw [Int.ofNat_sub Nat.one_le_two_pow]; push_cast; rfl
    rw [← e]; exact Int.ofNat_dvd.mpr h
  have hPq : (q : Int) ∣ (2 : Int) ^ P - 1 := Int.dvd_trans (Int.ofNat_dvd.mpr hqL) hLam1
  have hs' : s - 1 + 1 = s := by omega
  -- Y and the j_s = 0 relation
  have hYp := chain_pos q (by omega) P y0 b J s hI hy0 hb (s - 1) (by omega)
  have hY0p := chain_pos q (by omega) P y0 b J s hI hy0 hb s (Nat.le_refl s)
  obtain ⟨Y, hY⟩ : ∃ Y : Nat, (Y : Int) = chain (q : Int) P y0 b J (s - 1) :=
    ⟨_, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨Y0, hY0⟩ : ∃ Y : Nat, (Y : Int) = chain (q : Int) P y0 b J s :=
    ⟨_, Int.toNat_of_nonneg (by omega)⟩
  have rel0 := chain_rel hI (s - 1) (by omega)
  rw [hs', hJs, Nat.zero_mul, Int.pow_zero, Int.mul_one] at rel0
  have hrel0 : q * Y0 + 1 = 2 ^ b s * Y := by
    apply Int.ofNat_inj.1; push_cast; rw [hY0, hY]; exact rel0
  -- 2^{b_s} Y is a unit mod Λ W
  have hLW1 : 1 < LamA q m * W := Nat.lt_of_lt_of_le hLg (Nat.le_mul_of_pos_right _ hW)
  have hcop : Nat.gcd (2 ^ b s * Y) (LamA q m * W) = 1 := by
    apply coprime_of_no_prime
    intro p hp hpY hpLW
    have hpq : p ∣ q := by
      rcases isPrime_dvd_mul hp hpLW with h1 | h1
      · exact prime_dvd_q_of_dvd_LamA hp h1
      · exact hWq p hp h1
    have h1 : (2 ^ b s * Y) % p = 1 % p := by
      rw [← hrel0, Nat.add_mod, Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right_of_dvd hpq _), Nat.zero_add,
        Nat.mod_mod]
    have h2 : (2 ^ b s * Y) % p = 0 := Nat.mod_eq_zero_of_dvd hpY
    have := Nat.mod_eq_of_lt hp.1
    omega
  obtain ⟨inv, w, hinv⟩ := nat_bez _ _ hLW1 hcop
  -- residue of 2^{b_s} Y mod Λ
  have hρN : Y0 % (q ^ KM q m * uqq q) = ρ % (q ^ KM q m * uqq q) :=
    nat_mod_of_int_dvd (by rw [hY0]; exact hρ)
  have hLeq : LamA q m = q * (q ^ KM q m * uqq q) := by
    unfold LamA; rw [Nat.pow_succ]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have hYL : 2 ^ b s * Y % LamA q m = (q * ρ + 1) % LamA q m := by
    rw [← hrel0, hLeq, Nat.add_mod, Nat.mul_mod_mul_left, hρN, ← Nat.mul_mod_mul_left, ← Nat.add_mod]
  have hz : (q * ρ + 1) * inv % LamA q m = 1 % LamA q m := by
    have hd : LamA q m ∣ LamA q m * W := Nat.dvd_mul_right _ _
    rw [Nat.mul_mod, ← hYL, ← Nat.mul_mod, hinv, ← Nat.mod_mod_of_dvd _ hd, Nat.mul_add_mod,
      Nat.mod_mod_of_dvd _ hd]
  -- geometric visit
  obtain ⟨j', hj', hj'e⟩ := geom_visit (g := 2 ^ P) (L0 := LamA q m) (W := W) hq (by omega) hqL hW
    (fun r hr h => prime_dvd_q_of_dvd_LamA hr h) hWq Nat.one_le_two_pow
    (by
      have h := Lam_dvd (m := m) hq hodd hm 1
      rw [Nat.one_mul, hPd] at h
      exact mod_eq_of_sub_mod_zero Nat.one_le_two_pow (Nat.mod_eq_zero_of_dvd h))
    (fun p Δ hp hpq hΔ => by
      have hv := val_2PN hq hodd hm hp hpq hΔ
      rw [hPd] at hv
      have hvL := val_qkU (k := KM q m + 1) hq hodd hp hpq
      rw [val_unique (val_vp hp.1 hL) hvL, ← Nat.pow_mul, Nat.mul_comm P Δ]
      exact hv)
    ((q * ρ + 1) * inv) hz
  -- (2^P)^W ≡ 1 (mod Λ W)
  have hWP : (2 ^ P) ^ W % (LamA q m * W) = 1 % (LamA q m * W) := by
    have h := LamW_dvd hq hodd hm hW hWq
    rw [hPd, Nat.mul_comm W P, Nat.pow_mul] at h
    exact mod_eq_of_sub_mod_zero (Nat.one_le_pow _ _ Nat.one_le_two_pow) (Nat.mod_eq_zero_of_dvd h)
  -- least k₀
  have hY1 : 1 ≤ Y := by omega
  have hwit : q * Θ + 1 ≤ 2 ^ (b s + (j' + (q * Θ + 1) * W) * P) * Y := by
    have h1 : q * Θ + 1 ≤ (j' + (q * Θ + 1) * W) * P := by
      have := Nat.le_mul_of_pos_right (q * Θ + 1) hW
      have := Nat.le_mul_of_pos_right (j' + (q * Θ + 1) * W) hP0
      omega
    have h2 : (j' + (q * Θ + 1) * W) * P < 2 ^ ((j' + (q * Θ + 1) * W) * P) := Nat.lt_two_pow_self
    have h3 : 2 ^ ((j' + (q * Θ + 1) * W) * P) ≤ 2 ^ (b s + (j' + (q * Θ + 1) * W) * P) :=
      Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _)
    have h4 : 2 ^ (b s + (j' + (q * Θ + 1) * W) * P) ≤ 2 ^ (b s + (j' + (q * Θ + 1) * W) * P) * Y :=
      Nat.le_mul_of_pos_right _ hY1
    omega
  have hsp := srch_spec (fun k => q * Θ + 1 ≤ 2 ^ (b s + (j' + k * W) * P) * Y) (q * Θ + 1) 0
    ⟨q * Θ + 1, Nat.zero_le _, by omega, hwit⟩
  generalize hk0d : srch (fun k => q * Θ + 1 ≤ 2 ^ (b s + (j' + k * W) * P) * Y) (q * Θ + 1) 0 = k0 at hsp
  obtain ⟨hk0, hmin⟩ := hsp
  -- the updated path
  refine ⟨j' + k0 * W, Y, ?_⟩
  have hI' := integral_update_last hPq hI (j' + k0 * W)
  have hcs1 : chain (q : Int) P y0 b (fun l => if l = s then j' + k0 * W else J l) (s - 1)
      = chain (q : Int) P y0 b J (s - 1) :=
    (chain_congr (q : Int) P y0 b J _ (s - 1) (fun l h1 h2 => by
      have : ¬ l = s := by omega
      simp only [this, ↓reduceIte])).symm
  have rel1 := chain_rel hI' (s - 1) (by omega)
  rw [hs', hcs1] at rel1
  simp only [↓reduceIte] at rel1
  have hb' : ∀ l, 1 ≤ l → l ≤ s → 1 ≤ b l := hb
  have hYsp := chain_pos q (by omega) P y0 b _ s hI' hy0 hb' s (Nat.le_refl s)
  obtain ⟨Ys, hYs⟩ : ∃ Y : Nat, (Y : Int) = chain (q : Int) P y0 b
      (fun l => if l = s then j' + k0 * W else J l) s := ⟨_, Int.toNat_of_nonneg (by omega)⟩
  have hrel1 : q * Ys + 1 = 2 ^ (b s + (j' + k0 * W) * P) * Y := by
    apply Int.ofNat_inj.1; push_cast; rw [hYs, hY, Int.pow_add]; exact rel1
  refine ⟨Ys, hY, hYs, hI', hrel1, ?_, ?_, ?_⟩
  · have : q * Θ + 1 ≤ q * Ys + 1 := by rw [hrel1]; exact hk0
    exact Nat.le_of_mul_le_mul_left (by omega : q * Θ ≤ q * Ys) (by omega : 0 < q)
  · -- residue modulo q^K u_q W
    have hpow : (2 ^ P) ^ (j' + k0 * W) % (LamA q m * W) = (2 ^ P) ^ j' % (LamA q m * W) := by
      rw [Nat.mul_comm k0 W]; exact pow_mod_period hWP j' k0
    have hres : (q * Ys + 1) % (LamA q m * W) = (q * ρ + 1) % (LamA q m * W) := by
      rw [hrel1, Nat.pow_add, Nat.mul_comm (j' + k0 * W) P, Nat.pow_mul]
      have e1 : 2 ^ b s * (2 ^ P) ^ (j' + k0 * W) * Y = (2 ^ b s * Y) * (2 ^ P) ^ (j' + k0 * W) := by
        simp only [Nat.mul_comm, Nat.mul_assoc]
      rw [e1, Nat.mul_mod, hpow, hj'e, ← Nat.mul_mod]
      have e2 : 2 ^ b s * Y * ((q * ρ + 1) * inv) = (q * ρ + 1) * (2 ^ b s * Y * inv) := by
        simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      rw [e2, hinv, Nat.mul_add, Nat.mul_one, Nat.add_comm, Nat.mul_left_comm, Nat.add_mul_mod_self_left]
    have h1 : (1 + q * Ys) % (LamA q m * W) = (1 + q * ρ) % (LamA q m * W) := by
      rw [Nat.add_comm 1, Nat.add_comm 1]; exact hres
    have h2 := mod_eq_of_add_mod_eq h1
    rw [hLeq, Nat.mul_assoc, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at h2
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) h2
  · rcases Nat.eq_zero_or_pos k0 with h0 | h0
    · left
      rw [h0, Nat.zero_mul, Nat.add_zero]
      have : (j' + 1) * P ≤ W * P := Nat.mul_le_mul_right P hj'
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    · right
      have hn := hmin (k0 - 1) (Nat.zero_le _) (by omega)
      have hle : 2 ^ (b s + (j' + (k0 - 1) * W) * P) * Y ≤ q * Θ := by omega
      have e : b s + (j' + k0 * W) * P = (b s + (j' + (k0 - 1) * W) * P) + W * P := by
        have : k0 * W = (k0 - 1) * W + W := by
          conv => lhs; rw [show k0 = (k0 - 1) + 1 by omega]
          rw [Nat.add_mul, Nat.one_mul]
        rw [this]; simp only [Nat.add_mul]; omega
      rw [e, Nat.pow_add, Nat.mul_comm (2 ^ (b s + (j' + (k0 - 1) * W) * P)) (2 ^ (W * P)),
        Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ hle

end Collatz
