import Collatz.Dynamics

namespace Collatz


theorem bezout (m n : Nat) : ∃ x y : Int, ((Nat.gcd m n : Nat) : Int) = x * m + y * n := by
  induction m, n using Nat.gcd.induction with
  | H0 n => exact ⟨0, 1, by simp⟩
  | H1 m n hm ih =>
    obtain ⟨x, y, hxy⟩ := ih
    refine ⟨y - x * ((n / m : Nat) : Int), x, ?_⟩
    rw [Nat.gcd_rec m n]
    have hdiv : ((n % m : Nat) : Int) + (m : Int) * ((n / m : Nat) : Int) = (n : Int) := by
      have h := Nat.mod_add_div n m
      omega
    rw [hxy]
    have : (((n % m : Nat)) : Int) = (n : Int) - (m : Int) * ((n / m : Nat) : Int) := by omega
    rw [this]
    (first | nat_ring | int_ring)

theorem nat_bez (a m' : Nat) (hm : 1 < m') (h : Nat.gcd a m' = 1) :
    ∃ k w : Nat, a * k = m' * w + 1 := by
  obtain ⟨x, y, hxy⟩ := bezout a m'
  rw [h] at hxy
  have hm0 : (0:Int) < m' := by omega
  have hr0 := Int.emod_nonneg x (by omega : (m':Int) ≠ 0)
  have hr1 := Int.emod_lt_of_pos x hm0
  have hq := Int.emod_add_mul_ediv x m'
  generalize x % m' = r at *
  generalize x / m' = c at *
  subst hq
  have key : r * a = 1 - (y + c * a) * m' := by
    simp only [Int.add_mul, Int.mul_add, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Int.add_comm, Int.add_left_comm] at hxy ⊢
    omega
  generalize hz : y + c * a = z at key
  have hra : 0 ≤ r * a := Int.mul_nonneg hr0 (by omega)
  have hz0 : z ≤ 0 := by
    cases Int.lt_or_le 0 z with
    | inl hp =>
      have : (m':Int) ≤ z * m' := by
        have := Int.mul_le_mul_of_nonneg_right (show (1:Int) ≤ z by omega) (show (0:Int) ≤ m' by omega)
        simpa using this
      omega
    | inr hp => exact hp
  refine ⟨r.toNat, (-z).toNat, ?_⟩
  have : ((a * r.toNat : Nat) : Int) = ((m' * (-z).toNat + 1 : Nat) : Int) := by
    push_cast
    rw [Int.toNat_of_nonneg hr0, Int.toNat_of_nonneg (by omega)]
    (first | nat_ring | int_ring)
  exact_mod_cast this

theorem mod_of_dvd_mod {a b P Z : Nat} (hZ : Z ∣ P) (h : a % P = b % P) : a % Z = b % Z := by
  rw [← Nat.mod_mod_of_dvd a hZ, h, Nat.mod_mod_of_dvd b hZ]

theorem coprime_p_of_coprime_two_mul {m' q : Nat} (hM : Nat.Coprime m' (2 * q)) : Nat.Coprime m' q :=
  Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_left q 2) hM
theorem coprime_two_of_coprime_two_mul {m' q : Nat} (hM : Nat.Coprime m' (2 * q)) : Nat.Coprime m' 2 :=
  Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right 2 q) hM

section Words
variable (q : Nat)

def ones : List Nat → Nat
  | [] => 0
  | e :: u => ones u + e

def kappa : List Nat → Nat
  | [] => 0
  | e :: u => q ^ ones u * e + 2 * kappa u

theorem collatz_odd [NonWieferich q] (y : Nat) :
    collatz q (2 * y + 1) = 2 * (q * y + (q + 1) / 2) := by
  have := NonWieferich.odd (q := q)
  unfold collatz
  rw [ite_eq_right (by omega)]
  have h : q + 1 = 2 * ((q + 1) / 2) := by omega
  generalize (q + 1) / 2 = c at h ⊢
  (first | nat_ring | int_ring)

theorem word_trajectory [NonWieferich q] : ∀ (u : List Nat), (∀ e ∈ u, e ≤ 1) → ∀ x : Nat,
    2 ^ u.length ∣ q ^ ones u * x + kappa q u →
    ∃ k, iter (collatz q) k x = (q ^ ones u * x + kappa q u) / 2 ^ u.length
  | [], _, x, _ => ⟨0, by simp [ones, kappa, iter]⟩
  | e :: u, hu, x, h => by
    have he : e = 0 ∨ e = 1 := by have := hu e (by simp); omega
    have hu' : ∀ d ∈ u, d ≤ 1 := fun d hd => hu d (by simp [hd])
    have hp : q ^ ones u % 2 = 1 := powp_odd q _
    have hc : q + 1 = 2 * ((q + 1) / 2) := by have := NonWieferich.odd (q := q); omega
    have h2 : 2 ∣ 2 ^ (u.length + 1) := by rw [Nat.pow_succ, Nat.mul_comm]; exact Nat.dvd_mul_right 2 (2 ^ u.length)
    have hpow : 2 ^ (u.length + 1) = 2 * 2 ^ u.length := by rw [Nat.pow_succ, Nat.mul_comm]
    simp only [List.length_cons, ones, kappa] at h ⊢
    rcases he with rfl | rfl
    · have h0 := Nat.dvd_trans h2 h
      obtain ⟨y, hy | hy⟩ : ∃ y, x = 2 * y ∨ x = 2 * y + 1 := ⟨x / 2, by omega⟩
      · subst hy
        have hn : q ^ (ones u + 0) * (2 * y) + (q ^ ones u * 0 + 2 * kappa q u)
            = 2 * (q ^ ones u * y + kappa q u) := by simp [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.zero_add, Nat.add_zero]
        rw [hn, hpow] at h
        have h' := (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).1 h
        obtain ⟨k, hk⟩ := word_trajectory u hu' y h'
        refine ⟨k + 1, ?_⟩
        show iter (collatz q) k (collatz q (2 * y)) = _
        rw [collatz_double, hk, hn, hpow, Nat.mul_div_mul_left _ _ (by omega : 0 < 2)]
      · subst hy
        exfalso
        have hn : q ^ (ones u + 0) * (2 * y + 1) + (q ^ ones u * 0 + 2 * kappa q u)
            = 2 * (q ^ ones u * y + kappa q u) + q ^ ones u := by (first | nat_ring | int_ring)
        rw [hn] at h0
        generalize q ^ ones u * y + kappa q u = P at h0
        omega
    · have h0 := Nat.dvd_trans h2 h
      obtain ⟨y, hy | hy⟩ : ∃ y, x = 2 * y ∨ x = 2 * y + 1 := ⟨x / 2, by omega⟩
      · subst hy
        exfalso
        have hn : q ^ (ones u + 1) * (2 * y) + (q ^ ones u * 1 + 2 * kappa q u)
            = 2 * (q ^ ones u * (q * y) + kappa q u) + q ^ ones u := by (rw [Nat.pow_succ]; nat_ring)
        rw [hn] at h0
        generalize q ^ ones u * (q * y) + kappa q u = P at h0
        omega
      · subst hy
        have hn : q ^ (ones u + 1) * (2 * y + 1) + (q ^ ones u * 1 + 2 * kappa q u)
            = 2 * (q ^ ones u * (q * y + (q + 1) / 2) + kappa q u) := by
          rw [Nat.pow_succ]
          generalize (q + 1) / 2 = c at hc ⊢
          (have hQ : q ^ ones u * (q + 1) = q ^ ones u * (2 * c) := (by rw [hc]); nat_ring)
        rw [hn, hpow] at h
        have h' := (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).1 h
        obtain ⟨k, hk⟩ := word_trajectory u hu' (q * y + (q + 1) / 2) h'
        refine ⟨k + 2, ?_⟩
        show iter (collatz q) k (collatz q (collatz q (2 * y + 1))) = _
        rw [collatz_odd, collatz_double, hk, hn, hpow, Nat.mul_div_mul_left _ _ (by omega : 0 < 2)]

theorem reaches_pow2 [NonWieferich q] (w : Nat) : ∀ n, Reaches q (2 ^ n * w) w
  | 0 => ⟨0, by simp [iter]⟩
  | n + 1 => by
    obtain ⟨k, hk⟩ := reaches_pow2 w n
    refine ⟨k + 1, ?_⟩
    rw [iter_add]
    show iter (collatz q) k (collatz q (2 ^ (n + 1) * w)) = w
    rw [show 2 ^ (n + 1) * w = 2 * (2 ^ n * w) by rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc], collatz_double]; exact hk

end Words

theorem pow_two_mod_period (P T : Nat) (hT : 2 ^ T % P = 1 % P) (x y : Nat) (hxy : x % T = y % T) :
    2 ^ x % P = 2 ^ y % P := by
  have key : ∀ z : Nat, 2 ^ z % P = 2 ^ (z % T) % P := by
    intro z
    have hz : 2 ^ z = (2 ^ T) ^ (z / T) * 2 ^ (z % T) := by
      rw [← Nat.pow_mul, ← Nat.pow_add, Nat.div_add_mod]
    rw [hz, Nat.mul_mod, pow_mod_one P (2 ^ T) _ hT, ← Nat.mul_mod, Nat.one_mul]
  rw [key x, key y, hxy]

theorem exists_in_class (a e T : Nat) (hT : 0 < T) :
    ∃ E, e ≤ E ∧ E < e + T ∧ E % T = a % T := by
  refine ⟨e + (a + (T - e % T)) % T, by omega, ?_, ?_⟩
  · have := Nat.mod_lt (a + (T - e % T)) hT
    omega
  · rw [Nat.add_mod e, Nat.mod_mod, Nat.add_mod_mod]
    have h1 := Nat.mod_lt e hT
    have : e % T + (a + (T - e % T)) = a + T := by omega
    rw [this, Nat.add_mod_right]

theorem parity_prefix (q : Nat) [NonWieferich q] : ∀ α x : Nat, ∃ u : List Nat, (∀ e ∈ u, e ≤ 1) ∧
    u.length = α ∧ 2 ^ α ∣ q ^ ones u * x + kappa q u := by
  intro α
  induction α with
  | zero => intro x; exact ⟨[], by simp, rfl, by simp⟩
  | succ α ih =>
    intro x
    have hc : q + 1 = 2 * ((q + 1) / 2) := by have := NonWieferich.odd (q := q); omega
    obtain ⟨y, hy | hy⟩ : ∃ y, x = 2 * y ∨ x = 2 * y + 1 := ⟨x / 2, by omega⟩
    · obtain ⟨u, hu, hl, hd⟩ := ih y
      refine ⟨0 :: u, ?_, by simp [hl], ?_⟩
      · intro e he; simp at he; rcases he with rfl | he; omega; exact hu e he
      · simp only [ones, kappa]
        have hn : q ^ (ones u + 0) * x + (q ^ ones u * 0 + 2 * kappa q u)
            = 2 * (q ^ ones u * y + kappa q u) := by subst hy; (first | nat_ring | int_ring)
        rw [hn, Nat.pow_succ']
        exact Nat.mul_dvd_mul_left 2 hd
    · obtain ⟨u, hu, hl, hd⟩ := ih (q * y + (q + 1) / 2)
      refine ⟨1 :: u, ?_, by simp [hl], ?_⟩
      · intro e he; simp at he; rcases he with rfl | he; omega; exact hu e he
      · simp only [ones, kappa]
        have hn : q ^ (ones u + 1) * x + (q ^ ones u * 1 + 2 * kappa q u)
            = 2 * (q ^ ones u * (q * y + (q + 1) / 2) + kappa q u) := by
          subst hy; rw [Nat.pow_succ]
          generalize (q + 1) / 2 = c at hc ⊢
          (have hQ : q ^ ones u * (q + 1) = q ^ ones u * (2 * c) := (by rw [hc]); nat_ring)
        rw [hn, Nat.pow_succ']
        exact Nat.mul_dvd_mul_left 2 hd

theorem split_coprime (a : Nat) : ∀ X, 1 ≤ X → ∃ A Y k, X = A * Y ∧ Nat.Coprime Y a ∧ A ∣ a ^ k := by
  intro X
  induction X using Nat.strongRecOn with
  | _ X ih =>
    intro hX
    match (inferInstance : Decidable (Nat.gcd X a = 1)) with
    | isTrue hc =>
      exact ⟨1, X, 0, by simp, hc, by simp⟩
    | isFalse hc =>
      have hg1 : Nat.gcd X a ≠ 1 := hc
      have hg0 : 0 < Nat.gcd X a := Nat.gcd_pos_of_pos_left _ (by omega)
      obtain ⟨X1, hX1⟩ := Nat.gcd_dvd_left X a
      have hga := Nat.gcd_dvd_right X a
      generalize Nat.gcd X a = g at hg1 hg0 hX1 hga
      have hX10 : 1 ≤ X1 := by
        match (inferInstance : Decidable (1 ≤ X1)) with
        | isTrue hg => exact hg
        | isFalse h =>
        exfalso
        have : X1 = 0 := by omega
        rw [this, Nat.mul_zero] at hX1; omega
      have hlt : X1 < X := by
        have : X1 * 2 ≤ X1 * g := Nat.mul_le_mul_left _ (by omega)
        have e : X1 * g = g * X1 := Nat.mul_comm _ _
        omega
      obtain ⟨A1, Y, k, h1, h2, h3⟩ := ih X1 hlt hX10
      refine ⟨g * A1, Y, k + 1, ?_, h2, ?_⟩
      · rw [hX1, h1, Nat.mul_assoc]
      · rw [Nat.pow_succ, Nat.mul_comm (a ^ k)]
        exact Nat.mul_dvd_mul hga h3

theorem split_two_power : ∀ m, 1 ≤ m → ∃ α O, m = 2 ^ α * O ∧ O % 2 = 1 := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro hN
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · obtain ⟨α, O, h1, h2⟩ := ih (m / 2) (by omega) (by omega)
      exact ⟨α + 1, O, by rw [Nat.pow_succ, Nat.mul_comm (2 ^ α) 2, Nat.mul_assoc, ← h1]; omega, h2⟩
    · exact ⟨0, m, by simp, h⟩


end Collatz
