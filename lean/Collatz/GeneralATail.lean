import Collatz.GeneralAParams

/-! Theorem A, Step 2 (generalAB.md, Lemmas 7–8): the 2-adic tail, for any odd q ≥ 3.
    `tailw q α x` is the parity word of the first α steps S_δ(z) = (q^δ z + δ)/2 from x,
    `tailv q α x` the value reached. Choice-free. -/

namespace Collatz

/-- One tail step S_δ(x) with δ = x mod 2. -/
def tstep (q x : Nat) : Nat := if x % 2 = 0 then x / 2 else (q * x + 1) / 2

def tailw (q : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | α + 1, x => (x % 2) :: tailw q α (tstep q x)

def tailv (q : Nat) : Nat → Nat → Nat
  | 0, x => x
  | α + 1, x => tailv q α (tstep q x)

theorem tailw_bits (q : Nat) : ∀ α x, ∀ e ∈ tailw q α x, e ≤ 1
  | 0, _, e, h => absurd h List.not_mem_nil
  | α + 1, x, e, h => by
    unfold tailw at h
    rcases List.mem_cons.mp h with h1 | h1
    · have := Nat.mod_lt x (show 0 < 2 by omega); omega
    · exact tailw_bits q α _ e h1

theorem tailw_length (q : Nat) : ∀ α x, (tailw q α x).length = α
  | 0, _ => rfl
  | α + 1, x => by unfold tailw; rw [List.length_cons, tailw_length q α]

theorem half_mod {a b n : Nat} (ha : a % 2 = 0) (hb : b % 2 = 0)
    (h : a % 2 ^ (n + 1) = b % 2 ^ (n + 1)) : (a / 2) % 2 ^ n = (b / 2) % 2 ^ n := by
  have ea : a = 2 * (a / 2) := by omega
  have eb : b = 2 * (b / 2) := by omega
  rw [ea, eb, Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at h
  omega

theorem tstep_mod {q x x' n : Nat} (hodd : q % 2 = 1) (h : x % 2 ^ (n + 1) = x' % 2 ^ (n + 1)) :
    tstep q x % 2 ^ n = tstep q x' % 2 ^ n := by
  have h2 : x % 2 = x' % 2 := by
    have hd : 2 ∣ 2 ^ (n + 1) := ⟨2 ^ n, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    rw [← Nat.mod_mod_of_dvd x hd, h, Nat.mod_mod_of_dvd x' hd]
  unfold tstep
  by_cases hx : x % 2 = 0
  · have hx' : x' % 2 = 0 := by omega
    simp only [hx, hx', ↓reduceIte]
    exact half_mod hx hx' h
  · have hx' : ¬ x' % 2 = 0 := by omega
    simp only [hx, hx', ↓reduceIte]
    have hqx : (q * x + 1) % 2 = 0 := by
      have : (q * x) % 2 = 1 := by rw [Nat.mul_mod, hodd]; omega
      omega
    have hqx' : (q * x' + 1) % 2 = 0 := by
      have : (q * x') % 2 = 1 := by rw [Nat.mul_mod, hodd]; omega
      omega
    apply half_mod hqx hqx'
    rw [Nat.add_mod, Nat.mul_mod, h, ← Nat.mul_mod, ← Nat.add_mod]

/-- The tail word depends only on x mod 2^α. -/
theorem tailw_mod {q : Nat} (hodd : q % 2 = 1) : ∀ α x x', x % 2 ^ α = x' % 2 ^ α →
    tailw q α x = tailw q α x'
  | 0, _, _, _ => rfl
  | α + 1, x, x', h => by
    unfold tailw
    have h2 : x % 2 = x' % 2 := by
      have hd : 2 ∣ 2 ^ (α + 1) := ⟨2 ^ α, by rw [Nat.pow_succ, Nat.mul_comm]⟩
      rw [← Nat.mod_mod_of_dvd x hd, h, Nat.mod_mod_of_dvd x' hd]
    rw [h2, tailw_mod hodd α _ _ (tstep_mod hodd h)]

/-- 2^α · S_σ(x) = q^{ones σ} x + Φ(σ). -/
theorem tail_identity {q : Nat} (hodd : q % 2 = 1) : ∀ α x,
    2 ^ α * tailv q α x = q ^ ones (tailw q α x) * x + kappa q (tailw q α x)
  | 0, x => by simp [tailv, tailw, ones, kappa]
  | α + 1, x => by
    unfold tailv tailw
    simp only [ones, kappa]
    have ih := tail_identity hodd α (tstep q x)
    generalize tailw q α (tstep q x) = w at ih ⊢
    have hS : 2 * tstep q x = q ^ (x % 2) * x + x % 2 := by
      by_cases hx : x % 2 = 0
      · have hs : tstep q x = x / 2 := by simp only [tstep, hx, ↓reduceIte]
        rw [hs, hx, Nat.pow_zero, Nat.one_mul, Nat.add_zero]; omega
      · have h1 : x % 2 = 1 := by omega
        have hs : tstep q x = (q * x + 1) / 2 := by simp only [tstep, hx, ↓reduceIte]
        have : (q * x) % 2 = 1 := by rw [Nat.mul_mod, hodd, h1]
        rw [hs, h1, Nat.pow_one]
        omega
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ α) 2, Nat.mul_assoc, ih, Nat.pow_add, Nat.mul_add]
    rw [show 2 * (q ^ ones w * tstep q x) = q ^ ones w * (2 * tstep q x) by
      simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc], hS]
    simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc,
      Nat.add_comm]

/-- Sharp bound: x + 1 ≤ 2^α Q implies S_σ(x) + 1 ≤ q^{ones σ} Q. -/
theorem tail_bound {q : Nat} (hq3 : 3 ≤ q) (hodd : q % 2 = 1) : ∀ α x Q,
    x + 1 ≤ 2 ^ α * Q → tailv q α x + 1 ≤ q ^ ones (tailw q α x) * Q
  | 0, x, Q, h => by simp only [tailv, tailw, ones, Nat.pow_zero, Nat.one_mul] at h ⊢; exact h
  | α + 1, x, Q, h => by
    unfold tailv tailw
    simp only [ones]
    by_cases hx : x % 2 = 0
    · have hs : tstep q x = x / 2 := by simp only [tstep, hx, ↓reduceIte]
      have h' : x / 2 + 1 ≤ 2 ^ α * Q := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ α) 2, Nat.mul_assoc] at h
        omega
      rw [← hs] at h'
      have := tail_bound hq3 hodd α _ Q h'
      rw [hx, Nat.add_zero]; exact this
    · have h1 : x % 2 = 1 := by omega
      have hs : tstep q x = (q * x + 1) / 2 := by simp only [tstep, hx, ↓reduceIte]
      have hqx : (q * x) % 2 = 1 := by rw [Nat.mul_mod, hodd, h1]
      have h' : tstep q x + 1 ≤ 2 ^ α * (q * Q) := by
        rw [hs]
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ α) 2, Nat.mul_assoc] at h
        have hq1 : q * (x + 1) ≤ q * (2 * (2 ^ α * Q)) := Nat.mul_le_mul_left q h
        have e : 2 ^ α * (q * Q) = q * (2 ^ α * Q) := Nat.mul_left_comm _ _ _
        rw [e]
        rw [Nat.mul_add, Nat.mul_one] at hq1
        rw [Nat.mul_left_comm q 2] at hq1
        omega
      have := tail_bound hq3 hodd α _ (q * Q) h'
      rw [h1, Nat.pow_succ]
      rw [Nat.mul_assoc]; exact this

/-- x → S_σ(x). -/
theorem reaches_tailv {q : Nat} (hodd : q % 2 = 1) : ∀ α x, Reaches q x (tailv q α x)
  | 0, x => ⟨0, rfl⟩
  | α + 1, x => by
    unfold tailv
    refine reaches_trans q ?_ (reaches_tailv hodd α (tstep q x))
    by_cases hx : x % 2 = 0
    · have hs : tstep q x = x / 2 := by simp only [tstep, hx, ↓reduceIte]
      rw [hs]
      have e : x = 2 * (x / 2) := by omega
      refine ⟨1, ?_⟩
      show iter (collatz q) 0 (collatz q x) = x / 2
      conv => lhs; rw [e]
      rw [collatz_double]; rfl
    · have h1 : x % 2 = 1 := by omega
      have hs : tstep q x = (q * x + 1) / 2 := by simp only [tstep, hx, ↓reduceIte]
      have hqx : (q * x) % 2 = 1 := by rw [Nat.mul_mod, hodd, h1]
      apply reaches_of_step (e := 1) h1
      rw [hs, Nat.pow_one]; omega

/-- Lemma 8 (tail matching). -/
theorem tail_match {q m α M rb B y : Nat} (hq3 : 3 ≤ q) (hodd : q % 2 = 1)
    (hm : m = 2 ^ α * M)
    (hρy : tailv q α rb + q ^ ones (tailw q α rb) * (B + 1) ≤ y)
    (hdiv : q ^ ones (tailw q α rb) * M ∣ y - tailv q α rb) :
    ∃ w, B < w ∧ w % m = rb % m ∧ Reaches q w y ∧ q ^ ones (tailw q α rb) * w ≤ 2 ^ α * y := by
  generalize hn : ones (tailw q α rb) = n at hρy hdiv
  generalize hρ : tailv q α rb = ρ at hρy hdiv
  have hqn : 0 < q ^ n := Nat.pow_pos (by omega)
  obtain ⟨c, hc⟩ := hdiv
  have hy : y = ρ + q ^ n * (M * c) := by
    rw [Nat.mul_assoc] at hc
    have : ρ ≤ y := by have := Nat.mul_pos hqn (Nat.succ_pos B); omega
    omega
  have hzB : B + 1 ≤ M * c := by
    have h1 : q ^ n * (B + 1) ≤ q ^ n * (M * c) := by omega
    exact Nat.le_of_mul_le_mul_left h1 hqn
  have h2a : 0 < 2 ^ α := Nat.pow_pos (by omega)
  have hwr : (rb + 2 ^ α * (M * c)) % 2 ^ α = rb % 2 ^ α := by
    rw [Nat.add_mul_mod_self_left]
  have hword : tailw q α (rb + 2 ^ α * (M * c)) = tailw q α rb := tailw_mod hodd α _ _ hwr
  have hid := tail_identity hodd α (rb + 2 ^ α * (M * c))
  have hid0 := tail_identity hodd α rb
  rw [hword, hn] at hid
  rw [hn, hρ] at hid0
  have hval : tailv q α (rb + 2 ^ α * (M * c)) = y := by
    apply Nat.eq_of_mul_eq_mul_left h2a
    rw [hid, hy, Nat.mul_add, Nat.mul_add, hid0]
    simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm]
  refine ⟨rb + 2 ^ α * (M * c), ?_, ?_, ?_, ?_⟩
  · have := Nat.le_mul_of_pos_left (M * c) h2a
    omega
  · rw [hm, ← Nat.mul_assoc, Nat.mul_comm (2 ^ α * M) c, Nat.mul_comm c, Nat.add_mul_mod_self_left]
  · have := reaches_tailv hodd α (rb + 2 ^ α * (M * c))
    rw [hval] at this; exact this
  · have : 2 ^ α * y = q ^ n * (rb + 2 ^ α * (M * c)) + kappa q (tailw q α rb) := by
      rw [← hval, hid]
    omega

end Collatz
