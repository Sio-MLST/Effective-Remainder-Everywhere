import Collatz.GeneralVisit

/-! Step 1 (closes P1): the graph 𝒢_q is well defined on residue classes mod N_q.
    If z ≡ z' (mod N_q) and both lie in V_q, then a₀(z) = a₀(z') and
    c₀(z) ≡ c₀(z') (mod u_q). Hence Edge and GPath are invariant under
    replacing a representative by another one in the same class. -/

namespace Collatz

theorem mod_q_of_mod_N {q N z z' : Nat} (hqN : q ∣ N) (h : z % N = z' % N) :
    z % q = z' % q := by
  rw [← Nat.mod_mod_of_dvd z hqN, ← Nat.mod_mod_of_dvd z' hqN, h]

theorem coprime_congr_N {y y' N : Nat} (h : y % N = y' % N) (hc : Nat.Coprime y N) :
    Nat.Coprime y' N := by
  have e1 : Nat.gcd y N = Nat.gcd (y % N) N := by
    rw [Nat.gcd_comm, Nat.gcd_rec]
  have e2 : Nat.gcd y' N = Nat.gcd (y' % N) N := by
    rw [Nat.gcd_comm, Nat.gcd_rec]
  unfold Nat.Coprime at hc ⊢
  rw [e2, ← h, ← e1]; exact hc

theorem Nqq_dvd (q : Nat) : q ∣ Nqq q := Nat.dvd_mul_right q (uqq q)

theorem Vq_congr {q z z' : Nat} (hz : Vq q z)
    (h : z % Nqq q = z' % Nqq q) : Vq q z' := by
  obtain ⟨hc, i, hi⟩ := hz
  refine ⟨coprime_congr_N h hc, i, ?_⟩
  rw [← mod_q_of_mod_N (Nqq_dvd q) h]; exact hi

/-- a₀ is constant on classes mod N_q. -/
theorem a0_congr {q z z' : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hz : Vq q z)
    (h : z % Nqq q = z' % Nqq q) : a0 q z = a0 q z' := by
  have hz' := Vq_congr hz h
  have hi := hz.2
  have hs := a0_spec hq hodd hi
  have hs' := a0_spec hq hodd hz'.2
  obtain ⟨hA1, hAD, hAp, hAu⟩ := hs
  obtain ⟨_, _, _, hBu⟩ := hs'
  have hmq := mod_q_of_mod_N (Nqq_dvd q) h
  have hmod : 2 ^ a0 q z * z' % q = 1 % q := by
    rw [Nat.mul_mod, ← hmq, ← Nat.mul_mod]; exact hAp
  exact hBu (a0 q z) hA1 hAD hmod

/-- Exact identity q·c₀(z) + 1 = 2^{a₀(z)} z for z ∈ V_q. -/
theorem c0_spec {q z : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hz : Vq q z)
    (hz1 : 1 ≤ z) : q * c0 q z + 1 = 2 ^ a0 q z * z := by
  have := (cj_spec hq hodd hz.2 hz1 0).1
  rw [c0_eq_cj0, Nat.mul_zero, Nat.add_zero] at *
  simpa [cj, Nat.mul_zero, Nat.add_zero] using this

/-- Shift identity: z' = z + N_q k gives c₀(z') = c₀(z) + u_q (2^{a₀} k). -/
theorem c0_shift {q z k : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hz : Vq q z) (hz1 : 1 ≤ z) :
    c0 q (z + Nqq q * k) = c0 q z + uqq q * (2 ^ a0 q z * k) := by
  have hzk : z % Nqq q = (z + Nqq q * k) % Nqq q := by
    rw [Nat.add_mul_mod_self_left]
  have hz' : Vq q (z + Nqq q * k) := Vq_congr hz hzk
  have ha : a0 q (z + Nqq q * k) = a0 q z := (a0_congr hq hodd hz hzk).symm
  have hz1' : 1 ≤ z + Nqq q * k := by omega
  have hA := c0_spec hq hodd hz' hz1'
  have hB := c0_spec hq hodd hz hz1
  rw [ha] at hA
  have hq0 : 0 < q := by omega
  have e1 : 2 ^ a0 q z * (z + Nqq q * k) = 2 ^ a0 q z * z + q * (uqq q * (2 ^ a0 q z * k)) := by
    rw [Nat.mul_add]
    congr 1
    rw [show Nqq q = q * uqq q from rfl]
    ac_rfl
  rw [e1] at hA
  apply Nat.eq_of_mul_eq_mul_left hq0
  rw [Nat.mul_add]
  omega

/-- If z ≤ z' and z ≡ z' (mod N_q), then z' = z + N_q k for k = (z' - z)/N_q. -/
theorem shift_of_mod_eq {N z z' : Nat} (hle : z ≤ z') (h : z % N = z' % N) :
    z' = z + N * ((z' - z) / N) := by
  have hm := Nat.sub_mod_eq_zero_of_mod_eq h.symm
  have hd := Nat.div_add_mod (z' - z) N
  rw [hm, Nat.add_zero] at hd
  omega

/-- c₀ mod u_q is constant on classes mod N_q (both in V_q). -/
theorem c0_mod_congr {q z z' : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hz : Vq q z)
    (hz1 : 1 ≤ z) (hz' : Vq q z') (hz1' : 1 ≤ z') (h : z % Nqq q = z' % Nqq q) :
    c0 q z % uqq q = c0 q z' % uqq q := by
  match Nat.le_total z z' with
  | Or.inl hle =>
    have hk := shift_of_mod_eq hle h
    rw [hk, c0_shift hq hodd hz hz1, Nat.add_mul_mod_self_left]
  | Or.inr hge =>
    have hk := shift_of_mod_eq hge h.symm
    rw [hk, c0_shift hq hodd hz' hz1', Nat.add_mul_mod_self_left]

theorem Vq_pos {q z : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (hz : Vq q z) : 1 ≤ z := by
  match Nat.eq_zero_or_pos z with
  | Or.inl h0 =>
    exfalso
    have hc := hz.1
    rw [h0] at hc
    unfold Nat.Coprime at hc
    rw [Nat.gcd_zero_left] at hc
    have hN : 2 ≤ Nqq q := by
      have hu := (uu_spec hq hodd).2
      have : 0 < uqq q := uqq_pos hq hodd
      rw [show Nqq q = q * uqq q from rfl]
      have : 2 ≤ q * uqq q := Nat.le_trans (by omega) (Nat.le_mul_of_pos_right q this)
      exact this
    omega
  | Or.inr h => exact h

/-- Edge depends on its source only through the class mod N_q. -/
theorem Edge_congr_source {q z z2 w : Nat} (hq : 1 < q) (hodd : q % 2 = 1)
    (hE : Edge q z w) (h : z % Nqq q = z2 % Nqq q) : Edge q z2 w := by
  obtain ⟨hz, hw, hcw⟩ := hE
  have hz2 := Vq_congr hz h
  refine ⟨hz2, hw, ?_⟩
  rw [hcw]
  exact c0_mod_congr hq hodd hz (Vq_pos hq hodd hz) hz2 (Vq_pos hq hodd hz2) h

theorem GPath_Vq {q m z b : Nat} (hP : GPath q m z b) :
    Vq q z := by
  cases m with
  | zero => exact hP.1
  | succ m' =>
    obtain ⟨w, hE, _⟩ := hP
    exact hE.1

/-- GPath is invariant under changing the source representative within its class. -/
theorem GPath_congr_source {q : Nat} (hq : 1 < q) (hodd : q % 2 = 1) :
    ∀ (n z z2 t : Nat), z % Nqq q = z2 % Nqq q → GPath q n z t → GPath q n z2 t
  | 0, z, z2, t, h, hP => by
    refine ⟨Vq_congr hP.1 h, ?_⟩
    rw [← h]; exact hP.2
  | n + 1, z, z2, t, h, hP => by
    obtain ⟨w, hE, hR⟩ := hP
    exact ⟨w, Edge_congr_source hq hodd hE h, hR⟩

/-- Concatenation of paths. -/
theorem GPath_trans {q : Nat} (hq : 1 < q) (hodd : q % 2 = 1) :
    ∀ (n m z a b : Nat), GPath q n z a → GPath q m a b → GPath q (n + m) z b
  | 0, m, z, a, b, hP, hQ => by
    rw [Nat.zero_add]
    exact GPath_congr_source hq hodd m a z b (by rw [hP.2]) hQ
  | n + 1, m, z, a, b, hP, hQ => by
    obtain ⟨w, hE, hR⟩ := hP
    have e : n + 1 + m = (n + m) + 1 := by omega
    rw [e]
    exact ⟨w, hE, GPath_trans hq hodd n m w a b hR hQ⟩

/-- Splitting a path at an intermediate class (truncation). -/
theorem GPath_split {q : Nat} (hq : 1 < q) (hodd : q % 2 = 1) :
    ∀ (n m z b : Nat), GPath q (n + m) z b → ∃ c, GPath q n z c ∧ GPath q m c b
  | 0, m, z, b, hP => by
    rw [Nat.zero_add] at hP
    exact ⟨z, ⟨GPath_Vq hP, rfl⟩, hP⟩
  | n + 1, m, z, b, hP => by
    have e : n + 1 + m = (n + m) + 1 := by omega
    rw [e] at hP
    obtain ⟨w, hE, hR⟩ := hP
    obtain ⟨c, hc1, hc2⟩ := GPath_split hq hodd n m w b hR
    exact ⟨c, ⟨w, hE, hc1⟩, hc2⟩

end Collatz
