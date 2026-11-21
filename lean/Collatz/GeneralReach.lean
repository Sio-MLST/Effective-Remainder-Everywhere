import Collatz.GeneralEdge

/-! Step 1 of the general development (generalAB.md, Section 2): the shared decomposition
    lemma `reaches_decomp` and Proposition 1, direction (1) ⇒ (2).
    Choice-free: only Nat/Int arithmetic and the already-proved residue lemmas. -/

namespace Collatz

/-- Shared decomposition. If `N` Col-steps take `x` to `t`, then either no odd step occurs
    (`x = 2^k t`), or `x = 2^{k₀} w_m` for a backward chain of m ≥ 1 odd steps in R_q(t). -/
theorem reaches_decomp {q : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (t : Nat) (ht : 1 ≤ t) :
    ∀ (N x : Nat), iter (collatz q) N x = t →
      x = 2 ^ N * t ∨
      (∃ m w k k0, 1 ≤ m ∧ Chain q t m w k ∧ x = 2 ^ k0 * w m)
  | 0, x, h => by
    have h' : x = t := h
    exact Or.inl (by rw [Nat.pow_zero, Nat.one_mul]; exact h')
  | N + 1, x, h => by
    have h' : iter (collatz q) N (collatz q x) = t := h
    by_cases hx : x % 2 = 0
    · have hc : collatz q x = x / 2 := by simp [collatz, hx]
      rw [hc] at h'
      have hx2 : x = 2 * (x / 2) := by omega
      rcases reaches_decomp hq hodd t ht N (x / 2) h' with hk | ⟨m, w, k, k0, hm, hch, hk⟩
      · refine Or.inl ?_
        rw [hx2, hk, Nat.pow_succ]
        simp only [Nat.mul_comm, Nat.mul_left_comm]
      · refine Or.inr ⟨m, w, k, k0 + 1, hm, hch, ?_⟩
        rw [hx2, hk, Nat.pow_succ]
        simp only [Nat.mul_comm, Nat.mul_left_comm]
    · have hxo : x % 2 = 1 := by omega
      have hx1 : 1 ≤ x := by omega
      have hc : collatz q x = q * x + 1 := by simp [collatz, hx]
      rw [hc] at h'
      rcases reaches_decomp hq hodd t ht N (q * x + 1) h' with hk | ⟨m, w, k, k0, hm, hch, hk⟩
      · -- chain of length one: w_1 = x
        refine Or.inr ⟨1, fun _ => x, fun _ => N, 0, Nat.le_refl 1, ?_, by simp⟩
        refine ⟨fun l _ _ => ⟨hxo, hx1⟩, ?_, fun l h1 h2 => absurd h2 (by omega)⟩
        exact hk
      · -- prepend x as the new far end of the chain
        have hqx : (q * x) % 2 = 1 := by rw [Nat.mul_mod, hodd, hxo]
        have hwm := hch.1 m (by omega) (Nat.le_refl _)
        refine Or.inr ⟨m + 1, fun l => if l = m + 1 then x else w l,
          fun l => if l = m + 1 then k0 else k l, 0, by omega, ?_, by simp⟩
        refine ⟨fun l h1 h2 => ?_, ?_, fun l h1 h2 => ?_⟩
        · by_cases hl : l = m + 1
          · simp only [hl, ↓reduceIte]; exact ⟨hxo, hx1⟩
          · simp only [hl, ↓reduceIte]; exact hch.1 l h1 (by omega)
        · have hne : ¬ (1 = m + 1) := by omega
          simp only [hne, ↓reduceIte]
          exact hch.2.1
        · by_cases hl : l = m
          · subst hl
            have e2 : ¬ (l = l + 1) := by omega
            have hk0 : 1 ≤ k0 := by
              rcases Nat.eq_zero_or_pos k0 with h0 | h0
              · subst h0
                simp at hk
                omega
              · exact h0
            simp only [e2, ↓reduceIte]
            exact ⟨hk, hk0⟩
          · have hne1 : ¬ (l + 1 = m + 1) := by omega
            have hne2 : ¬ (l = m + 1) := by omega
            simp only [hne1, hne2, ↓reduceIte]
            exact hch.2.2 l h1 (by omega)

/-- 2^s y ≡ 1 (mod q) forces y ∈ V_q. -/
theorem Vq_of_pow {q y s : Nat} (hq : 1 < q) (hodd : q % 2 = 1)
    (h : 2 ^ s * y % q = 1 % q) : Vq q y := by
  have hi : y % q = 2 ^ (s * (dq q - 1)) % q := z_mod_pow_of_inv hq hodd h
  exact ⟨coprime_Nqq_of_coprime hq (coprime_of_mod_pow2 hodd hi), s * (dq q - 1), hi⟩

/-- A relation q·w + 1 = 2^k·y makes y lie in V_q. -/
theorem Vq_of_rel {q w y k : Nat} (hq : 1 < q) (hodd : q % 2 = 1)
    (h : q * w + 1 = 2 ^ k * y) : Vq q y :=
  Vq_of_pow hq hodd (by rw [← h, Nat.mul_add_mod])

/-- The odd backward step from y: if q·w + 1 = 2^k·y then w ≡ c₀(y) (mod u_q). -/
theorem w_mod_uq {q y w k : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hy : Vq q y) (hy1 : 1 ≤ y)
    (h : q * w + 1 = 2 ^ k * y) : w % uqq q = c0 q y % uqq q := by
  have hd := dq_isOrder2 hq hodd
  have hdu : 2 ^ dq q = 1 + q * uu q := (uu_spec hq hodd).1
  have hdvdU : uqq q ∣ uu q := Nat.gcd_dvd_left _ _
  obtain ⟨r, hr⟩ := hdvdU
  have e1 : q * (2 ^ dq q * w + uu q) + 1 = 2 ^ dq q * (q * w + 1) := by
    rw [hdu]
    nat_ring
  have hW : q * (2 ^ dq q * w + uu q) + 1 = 2 ^ (k + dq q) * y := by
    rw [e1, h, Nat.pow_add]
    simp only [Nat.mul_comm, Nat.mul_assoc]
  obtain ⟨j, _, hWj⟩ := step_form hq hodd hy.2 hy1 (by have := hd.1; omega) hW
  have hcj := cj_formula hq hodd hy.2 hy1 j
  have eA : 2 ^ dq q * w + uu q = w + uqq q * (q * r * w + r) := by
    rw [hdu, hr]
    nat_ring
  have eB : cj q y j = c0 q y + uqq q * (2 ^ a0 q y * y * r * Ssum (dq q) j) := by
    rw [hcj, hr]
    nat_ring
  have key : w + uqq q * (q * r * w + r) = c0 q y + uqq q * (2 ^ a0 q y * y * r * Ssum (dq q) j) := by
    rw [← eA, hWj, eB]
  have hmod : (w + uqq q * (q * r * w + r)) % uqq q
      = (c0 q y + uqq q * (2 ^ a0 q y * y * r * Ssum (dq q) j)) % uqq q := by
    rw [key]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at hmod
  exact hmod

/-- A chain step is an edge of 𝒢_q. -/
theorem edge_of_rel {q y w k : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hy1 : 1 ≤ y)
    (h : q * w + 1 = 2 ^ k * y) (hw : Vq q w) : Edge q y w :=
  ⟨Vq_of_rel hq hodd h, hw, w_mod_uq hq hodd (Vq_of_rel hq hodd h) hy1 h⟩

/-- An odd chain of length m+1 anchored at t gives a 𝒢_q-path of length m+1 from t to its far end. -/
theorem chain_gpath {q : Nat} (hq : 1 < q) (hodd : q % 2 = 1) :
    ∀ (m t : Nat) (w k : Nat → Nat), 1 ≤ t → Chain q t (m + 1) w k → Vq q (w (m + 1)) →
      GPath q (m + 1) t (w (m + 1))
  | 0, t, w, k, ht, hch, hV => by
    have hw1 : w 1 % 2 = 1 ∧ 1 ≤ w 1 := hch.1 1 (Nat.le_refl 1) (Nat.le_refl 1)
    exact ⟨w 1, edge_of_rel hq hodd ht hch.2.1 hV, hV, rfl⟩
  | m + 1, t, w, k, ht, hch, hV => by
    have hw1 : w 1 % 2 = 1 ∧ 1 ≤ w 1 := hch.1 1 (Nat.le_refl 1) (Nat.succ_le_succ (Nat.zero_le _))
    have hsub : Chain q (w 1) (m + 1) (fun l => w (l + 1)) (fun l => k (l + 1)) := by
      refine ⟨fun l h1 h2 => hch.1 (l + 1) (Nat.succ_le_succ (Nat.zero_le _)) (Nat.succ_le_succ h2), ?_, fun l h1 h2 => ?_⟩
      · exact (hch.2.2 1 (Nat.le_refl 1) (Nat.succ_lt_succ (Nat.succ_pos m))).1
      · exact hch.2.2 (l + 1) (Nat.succ_le_succ (Nat.zero_le _)) (Nat.succ_lt_succ h2)
    have ih := chain_gpath hq hodd m (w 1) (fun l => w (l + 1)) (fun l => k (l + 1)) hw1.2 hsub hV
    exact ⟨w 1, edge_of_rel hq hodd ht hch.2.1 (GPath_Vq ih), ih⟩

/-- Hypothesis (H) in ℕ form gives (H) in Int form (inverse of `hypha_nat`). -/
theorem hypha_of_nat {q a y i0 : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (_hy : 1 ≤ y)
    (hi0 : i0 < dq q) (hi : 2 ^ i0 * y * bco q a % Nqq q = 1 % Nqq q) : HypHa q a y := by
  have hN := Nqq_gt hq hodd
  have hbp := bco_pos q a hq hodd
  have hmod1 : 2 ^ i0 * y * bco q a % Nqq q = 1 := by rw [hi, Nat.mod_eq_of_lt hN]
  have hdiv := Nat.div_add_mod (2 ^ i0 * y * bco q a) (Nqq q)
  rw [hmod1] at hdiv
  generalize hc : (2 ^ i0 * y * bco q a) / Nqq q = c at hdiv
  refine ⟨i0, hi0, ?_⟩
  have hI : (2 : Int) ^ i0 * (y : Int) * ((bco q a : Nat) : Int) = (Nqq q : Int) * (c : Int) + 1 := by
    exact_mod_cast hdiv.symm
  rw [bco_cast q a hq hodd] at hI
  exact ⟨(c : Int) - (2 : Int) ^ i0 * (y : Int), by int_ring⟩

/-- Congruence of a Nat relation with a shifted exponent: from 2^{i0}·(2^k·y)·bco ≡ 1 mod N_q
    we get Vq y and Rcore y (the exponent is reduced mod d). -/
theorem rel_gives {q y k i0 a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (ha1 : 1 ≤ a)
    (haD : a ≤ dq q) (hy : 1 ≤ y)
    (hrel : 2 ^ i0 * (2 ^ k * y) * bco q a % Nqq q = 1 % Nqq q) : Vq q y ∧ Rcore q y := by
  have hN := Nqq_gt hq hodd
  have hb : bco q a % q = 2 ^ a % q := bco_mod_q q a hq hodd
  have hVq : Vq q y := by
    refine Vq_of_pow (s := i0 + k + a) hq hodd ?_
    have h1 := mod_q_of_mod_N (Nqq_dvd q) hrel
    have e2 : 2 ^ i0 * (2 ^ k * y) * bco q a % q = 2 ^ i0 * (2 ^ k * y) * 2 ^ a % q := by
      rw [Nat.mul_mod, hb, ← Nat.mul_mod]
    have e3 : 2 ^ (i0 + k + a) * y = 2 ^ i0 * (2 ^ k * y) * 2 ^ a := by
      rw [Nat.pow_add, Nat.pow_add]
      simp only [Nat.mul_comm, Nat.mul_assoc]
    rw [e3, ← e2, h1]
  have hdpos := (dq_isOrder2 hq hodd).1
  have hpow : 2 ^ (i0 + k) % Nqq q = 2 ^ ((i0 + k) % dq q) % Nqq q := by
    conv => lhs; rw [← Nat.mod_add_div (i0 + k) (dq q)]
    exact pow_Nqq_of_dvd (k := (i0 + k) / dq q) hq hodd ((i0 + k) % dq q)
  have hm : ∀ A B C : Nat, A % Nqq q = B % Nqq q → A * C % Nqq q = B * C % Nqq q :=
    fun A B C h => by rw [Nat.mul_mod, h, ← Nat.mul_mod]
  have hR1 : 2 ^ ((i0 + k) % dq q) * y % Nqq q = 2 ^ (i0 + k) * y % Nqq q :=
    hm _ _ _ hpow.symm
  have hR2 : 2 ^ ((i0 + k) % dq q) * y * bco q a % Nqq q = 2 ^ (i0 + k) * y * bco q a % Nqq q :=
    hm _ _ _ hR1
  have hR3 : 2 ^ (i0 + k) * y * bco q a = 2 ^ i0 * (2 ^ k * y) * bco q a := by
    rw [Nat.pow_add]
    simp only [Nat.mul_comm, Nat.mul_assoc]
  have hR4 : 2 ^ ((i0 + k) % dq q) * y * bco q a % Nqq q = 1 % Nqq q := by
    rw [hR2, hR3]; exact hrel
  exact ⟨hVq, hVq.1, a, ha1, haD, hypha_of_nat hq hodd hy (Nat.mod_lt _ hdpos) hR4⟩

/-- Proposition 1, direction (1) ⇒ (2): an element x ∈ R_q(t) satisfying (H) yields
    t ∈ V_q with a 𝒢_q-path from t to R_core. -/
theorem prop1_one_to_two {q t x : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (ht : 1 ≤ t)
    (hR : Reaches q x t) (hH : HypH q x) :
    Vq q t ∧ ∃ n z, GPath q n t z ∧ Rcore q z := by
  obtain ⟨N, hN⟩ := hR
  obtain ⟨a, ha1, haD, hHa⟩ := hH
  rcases reaches_decomp hq hodd t ht N x hN with hk | ⟨m, w, k, k0, hm, hch, hk⟩
  · -- no odd step: x = 2^k t, and t itself satisfies (H)
    have hx1 : 1 ≤ x := by rw [hk]; exact Nat.mul_pos (Nat.pow_pos (Nat.succ_pos 1)) ht
    obtain ⟨i0, _, hrel0⟩ := hypha_nat hq hodd hx1 hHa
    rw [hk] at hrel0
    obtain ⟨hVt, hRt⟩ := rel_gives hq hodd ha1 haD ht hrel0
    exact ⟨hVt, 0, t, ⟨hVt, rfl⟩, hRt⟩
  · -- an odd chain: the far end w_m is the target of a path from t
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
    have hwm : 1 ≤ w (m' + 1) := (hch.1 (m' + 1) (Nat.succ_le_succ (Nat.zero_le _)) (Nat.le_refl _)).2
    have hx1 : 1 ≤ x := by
      rw [hk]; exact Nat.mul_pos (Nat.pow_pos (Nat.succ_pos 1)) hwm
    obtain ⟨i0, _, hrel0⟩ := hypha_nat hq hodd hx1 hHa
    rw [hk] at hrel0
    obtain ⟨hVw, hRw⟩ := rel_gives hq hodd ha1 haD hwm hrel0
    have hG := chain_gpath hq hodd m' t w k ht hch hVw
    exact ⟨Vq_of_rel hq hodd hch.2.1, m' + 1, w (m' + 1), hG, hRw⟩

end Collatz
