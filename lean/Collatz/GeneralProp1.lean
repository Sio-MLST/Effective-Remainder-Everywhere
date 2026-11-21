import Collatz.GeneralCa

/-! Proposition 1 of generalAB.md (Section 2), Lean side.
    STATUS (WIP, see README):
      * PROVED: the self-loop Edge(c_a, c_a) (`ca_edge_loop`), and the (2)⇒(3) direction
        of `Prop1` part 2 when the Rcore path has length n ≥ κ (`prop1_two_to_three_long`).
      * WIP (unproved): Edge z c_a for z ∈ Rcore (needed when n < κ); and the (3)⇒(2)
        direction, which is the CRT/digit construction (markdown Prop 1, third implication). -/

namespace Collatz

/-- Nat identity: c₀(c_a) + U·c_a = c_a + U·w, where bco·c_a = N·w + 1. -/
theorem ca_c0_identity {q a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (ha1 : 1 ≤ a) (haD : a ≤ dq q) :
    c0 q (ca q a) + uqq q * ca q a = ca q a + uqq q * ((bco q a * ca q a) / Nqq q) := by
  have hN := Nqq_gt hq hodd
  have hVc := ca_Vq hq hodd ha1 haD
  have hcpos := Vq_pos hq hodd hVc
  have hc0 := c0_spec hq hodd hVc hcpos
  rw [a0_ca hq hodd ha1 haD] at hc0
  have hinv := ca_inv (a := a) hq hodd
  have hdiv := Nat.div_add_mod (bco q a * ca q a) (Nqq q)
  rw [hinv, Nat.mod_eq_of_lt hN] at hdiv
  have hbq : bco q a + q = 2 ^ a + Nqq q := by
    have h1 : q ≤ Nqq q := Nat.le_mul_of_pos_right q (uqq_pos hq hodd)
    have h2 : q ≤ 2 ^ a + Nqq q := Nat.le_trans h1 (Nat.le_add_left _ _)
    unfold bco; omega
  generalize hw : bco q a * ca q a / Nqq q = w at hdiv ⊢
  generalize hc0v : c0 q (ca q a) = c0v at hc0 ⊢
  generalize hcv : ca q a = c at hdiv hc0 ⊢
  -- hdiv : Nqq q * w + 1 = bco q a * c ; hc0 : q * c0v + 1 = 2^a * c
  have G : (bco q a + q) * c = (2 ^ a + Nqq q) * c := by rw [hbq]
  rw [Nat.add_mul, Nat.add_mul] at G
  have hdivc : bco q a * c = Nqq q * w + 1 := hdiv.symm
  have hN1 : q * (uqq q * c) = Nqq q * c := (Nat.mul_assoc _ _ _).symm
  have hN2 : q * (uqq q * w) = Nqq q * w := (Nat.mul_assoc _ _ _).symm
  apply Nat.eq_of_mul_eq_mul_left (show 0 < q by omega)
  rw [Nat.mul_add, Nat.mul_add]
  omega

/-- The self-loop: Edge(c_a, c_a) for 1 ≤ a ≤ d. -/
theorem ca_edge_loop {q a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (ha1 : 1 ≤ a) (haD : a ≤ dq q) :
    Edge q (ca q a) (ca q a) := by
  refine ⟨ca_Vq hq hodd ha1 haD, ca_Vq hq hodd ha1 haD, ?_⟩
  have h := ca_c0_identity hq hodd ha1 haD
  have : c0 q (ca q a) % uqq q = ca q a % uqq q := by
    have h' : c0 q (ca q a) + uqq q * ca q a = ca q a + uqq q * ((bco q a * ca q a) / Nqq q) := h
    rw [← Nat.add_mul_mod_self_left (c0 q (ca q a)) (uqq q) (ca q a), h']
    rw [Nat.add_mul_mod_self_left]
  exact this.symm

/-- Self-loop iterated: GPath m (c_a) (c_a) for every m. -/
theorem ca_gpath_loop {q a : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (ha1 : 1 ≤ a) (haD : a ≤ dq q) :
    ∀ m, GPath q m (ca q a) (ca q a)
  | 0 => ⟨ca_Vq hq hodd ha1 haD, rfl⟩
  | m + 1 => ⟨ca q a, ca_edge_loop hq hodd ha1 haD, ca_gpath_loop hq hodd ha1 haD m⟩

/-- (2)⇒(3), the case n ≥ κ: an Rcore-path of length n ≥ κ from t truncates to length κ. -/
theorem prop1_two_to_three_long {q t z n κ : Nat} (hq : 1 < q) (hodd : q % 2 = 1)
    (hk : κ ≤ n) (hP : GPath q n t z) : ∃ c, GPath q κ t c := by
  have e : n = κ + (n - κ) := by omega
  rw [e] at hP
  obtain ⟨c, hc1, _⟩ := GPath_split hq hodd κ (n - κ) t z hP
  exact ⟨c, hc1⟩

end Collatz
