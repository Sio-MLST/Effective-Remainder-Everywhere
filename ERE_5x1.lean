/- ERE5: 5x+1 predecessors of w (5 ∤ w) in every residue class mod N. Lean 4.35.0, core only. -/

namespace ERE5

def collatz (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 5 * n + 1

def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter f k (f n)

theorem iter_add (f : Nat → Nat) (m n : Nat) : ∀ x, iter f (m + n) x = iter f m (iter f n x) := by
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; exact ih (f x)

def Reaches (v n : Nat) : Prop := ∃ k, iter collatz k n = v

theorem collatz_double (a : Nat) : collatz (2 * a) = a := by
  unfold collatz; split <;> omega

theorem reaches_trans {a b c : Nat} (h1 : Reaches b a) (h2 : Reaches c b) : Reaches c a := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  exact ⟨k2 + k1, by rw [iter_add, hk1, hk2]⟩

theorem five_dvd_pow (K : Nat) : 5 ∣ 5 ^ (K + 1) := ⟨5 ^ K, by rw [Nat.pow_succ, Nat.mul_comm]⟩

theorem one_lt_pow5 (K : Nat) : 1 < 5 ^ (K + 1) :=
  Nat.one_lt_pow (Nat.succ_ne_zero K) (by decide)

theorem live_mod {m c : Nat} (h5 : 5 ∣ m) (hc : c % 5 ≠ 0) : c % m % 5 ≠ 0 := by
  rw [Nat.mod_mod_of_dvd c h5]; exact hc

theorem sixteen_pow_mod_five (j : Nat) : 16 ^ j % 5 = 1 := by
  induction j with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

theorem two_pow_mod_five_ne (E : Nat) : 2 ^ E % 5 ≠ 0 := by
  induction E with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

theorem pow5_form {j u : Nat} (hj : 1 ≤ j) (hu : u % 5 ≠ 0) :
    ∀ n : Nat, ∃ w : Nat, w % 5 ≠ 0 ∧ (1 + 5 ^ j * u) ^ (5 ^ n) = 1 + 5 ^ (j + n) * w := by
  intro n
  induction n with
  | zero => exact ⟨u, hu, by simp⟩
  | succ n ih =>
    obtain ⟨w, hw, hx⟩ := ih
    obtain ⟨k', hk'⟩ : ∃ k', j + n = k' + 1 := ⟨j + n - 1, by omega⟩
    refine ⟨w + 5 * (2 * 5 ^ k' * w ^ 2 + 10 * (5 ^ k') ^ 2 * w ^ 3
        + 25 * (5 ^ k') ^ 3 * w ^ 4 + 25 * (5 ^ k') ^ 4 * w ^ 5), ?_, ?_⟩
    · generalize 2 * 5 ^ k' * w ^ 2 + 10 * (5 ^ k') ^ 2 * w ^ 3
          + 5 * (5 ^ k') ^ 3 * w ^ 4 + 25 * (5 ^ k') ^ 4 * w ^ 5 = B
      omega
    · rw [Nat.pow_succ, Nat.pow_mul, hx, hk']
      have e2 : j + (n + 1) = k' + 2 := by omega
      have e3 : 5 ^ (k' + 1) = 5 * 5 ^ k' := by rw [Nat.pow_succ]; grind
      have e4 : 5 ^ (k' + 2) = 25 * 5 ^ k' := by rw [Nat.pow_succ, e3]; grind
      rw [e2, e3, e4]
      generalize 5 ^ k' = a
      grind

theorem pow_one_add (s w : Nat) :
    ∀ n : Nat, ∃ z : Nat, (1 + 5 ^ s * w) ^ n = 1 + n * (5 ^ s * w) + 5 ^ (2 * s) * z := by
  intro n
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨n * w ^ 2 + z + z * (5 ^ s * w), ?_⟩
    rw [Nat.pow_succ, hz, Nat.two_mul, Nat.pow_add]
    generalize 5 ^ s = a
    grind

theorem sixteen_pow_mod_eq_one_iff {K m : Nat} : 16 ^ m % 5 ^ (K + 1) = 1 ↔ 5 ^ K ∣ m := by
  induction K generalizing m with
  | zero => simp [sixteen_pow_mod_five]
  | succ K ih =>
    have hK3 : 5 ^ (K + 1 + 1) = 5 * 5 ^ (K + 1) := by grind
    have hpos : 0 < 5 ^ K := Nat.pow_pos (by decide)
    constructor
    · intro h
      have h1 : 16 ^ m % 5 ^ (K + 1) = 1 := by
        rw [← Nat.mod_mod_of_dvd (16 ^ m) (Nat.pow_dvd_pow 5 (by omega : K + 1 ≤ K + 1 + 1)), h]
        exact Nat.mod_eq_of_lt (one_lt_pow5 _)
      obtain ⟨k, hk⟩ := ih.1 h1
      subst hk
      by_cases h3k : k % 5 = 0
      · obtain ⟨k', rfl⟩ : 5 ∣ k := Nat.dvd_of_mod_eq_zero h3k
        exact ⟨k', by grind⟩
      · exfalso
        obtain ⟨w, hw, hx⟩ := pow5_form (j := 1) (u := 3) (by omega) (by omega) K
        obtain ⟨z, hz⟩ := pow_one_add (K + 1) w k
        have e4 : 16 ^ (5 ^ K * k) = (16 ^ 5 ^ K) ^ k := by rw [Nat.pow_mul]
        have e5 : (16 : Nat) = 1 + 5 ^ 1 * 3 := by decide
        rw [e4, e5, hx, show 1 + K = K + 1 by omega, hz] at h
        have hb : 1 + k * (5 ^ (K + 1) * w) + 5 ^ (2 * (K + 1)) * z
            = 1 + 5 ^ (K + 1) * (k * w + 5 ^ (K + 1) * z) := by
          have e : (5:Nat) ^ (2 * (K + 1)) = (5 ^ (K + 1)) ^ 2 := by rw [Nat.mul_comm, Nat.pow_mul]
          rw [e]; generalize 5 ^ (K + 1) = a; grind
        rw [hb, hK3] at h
        have hlt : 1 < 5 * 5 ^ (K + 1) := by have := one_lt_pow5 K; omega
        have hdiv : (5 * 5 ^ (K + 1)) ∣ 5 ^ (K + 1) * (k * w + 5 ^ (K + 1) * z) := by
          have := Nat.mod_eq_of_lt hlt
          have h2 : (1 + 5 ^ (K + 1) * (k * w + 5 ^ (K + 1) * z)) % (5 * 5 ^ (K + 1)) = 1 := h
          have := Nat.sub_mod_eq_zero_of_mod_eq (h2.trans (Nat.mod_eq_of_lt hlt).symm)
          simpa using Nat.dvd_of_mod_eq_zero this
        have hdiv2 : 5 ∣ k * w + 5 ^ (K + 1) * z := by
          rw [Nat.mul_comm 5 (5 ^ (K + 1))] at hdiv
          exact Nat.dvd_of_mul_dvd_mul_left (by have := one_lt_pow5 K; omega) hdiv
        have h31 : 5 ∣ 5 ^ (K + 1) * z := Nat.dvd_trans (five_dvd_pow K) (Nat.dvd_mul_right _ _)
        have h32 : 5 ∣ k * w := (Nat.dvd_add_right h31).1 (by rwa [Nat.add_comm] at hdiv2)
        have := Nat.mod_eq_zero_of_dvd h32
        rw [Nat.mul_mod] at this
        have hk3 : k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
        have hw3 : w % 5 = 1 ∨ w % 5 = 2 ∨ w % 5 = 3 ∨ w % 5 = 4 := by omega
        rcases hk3 with h' | h' | h' | h' <;> rcases hw3 with h'' | h'' | h'' | h'' <;>
          simp [h', h''] at this
    · rintro ⟨k, hk⟩
      have hK3' : 5 ^ (K + 1 + 1) = 25 * 5 ^ K := by
        rw [Nat.pow_succ, Nat.pow_succ]; grind
      have hK2 : 5 ^ (K + 1) = 5 * 5 ^ K := by rw [Nat.pow_succ]; grind
      have hm' : 5 ^ K ∣ 5 ^ K * k := ⟨k, rfl⟩
      have h1 : 16 ^ (5 ^ K * k) % 5 ^ (K + 1) = 1 := ih.2 hm'
      have hdm := Nat.div_add_mod (16 ^ (5 ^ K * k)) (5 ^ (K + 1))
      rw [h1] at hdm
      obtain ⟨t, ht⟩ : ∃ t, 16 ^ (5 ^ K * k) = 5 ^ (K + 1) * t + 1 := ⟨_, hdm.symm⟩
      rw [hK2] at ht
      have hm : m = 5 * (5 ^ K * k) := by rw [hk, hK2]; grind
      have e : 16 ^ m = (16 ^ (5 ^ K * k)) ^ 5 := by rw [hm, Nat.mul_comm 5, Nat.pow_mul]
      have hgt : 1 < 5 ^ (K + 1 + 1) := one_lt_pow5 _
      rw [e, ht, hK3']
      have : (5 * 5 ^ K * t + 1) ^ 5
          = 1 + 25 * 5 ^ K * (t + 10 * 5 ^ K * t ^ 2 + 50 * (5 ^ K) ^ 2 * t ^ 3
              + 125 * (5 ^ K) ^ 3 * t ^ 4 + 125 * (5 ^ K) ^ 4 * t ^ 5) := by
        generalize 5 ^ K = a; grind
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
      rw [← hK3']; exact hgt

theorem two_pow_mod_eq_one_iff {K m : Nat} : 2 ^ m % 5 ^ (K + 1) = 1 ↔ 4 * 5 ^ K ∣ m := by
  constructor
  · intro h
    have h5 : 2 ^ m % 5 = 1 := by
      rw [← Nat.mod_mod_of_dvd (2 ^ m) (five_dvd_pow K), h]
    have hm4 : m % 4 = 0 := by
      obtain ⟨a, r, hm, hr⟩ : ∃ a r, m = 4 * a + r ∧ r < 4 :=
        ⟨m / 4, m % 4, (Nat.div_add_mod m 4).symm, Nat.mod_lt _ (by omega)⟩
      have e : 2 ^ m = 16 ^ a * 2 ^ r := by rw [hm, Nat.pow_add, Nat.pow_mul]
      have h5' : (16 ^ a * 2 ^ r) % 5 = 1 := by rw [← e]; exact h5
      rw [Nat.mul_mod, sixteen_pow_mod_five, Nat.one_mul] at h5'
      rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with h | h | h | h
      · omega
      · rw [h] at h5'; exact absurd h5' (by decide)
      · rw [h] at h5'; exact absurd h5' (by decide)
      · rw [h] at h5'; exact absurd h5' (by decide)
    obtain ⟨n, rfl⟩ : ∃ n, m = 4 * n := ⟨m / 4, by omega⟩
    have e : 2 ^ (4 * n) = 16 ^ n := by rw [Nat.pow_mul]
    rw [e] at h
    exact Nat.mul_dvd_mul_left 4 (sixteen_pow_mod_eq_one_iff.1 h)
  · rintro ⟨q, rfl⟩
    have h : 16 ^ (5 ^ K) % 5 ^ (K + 1) = 1 := sixteen_pow_mod_eq_one_iff.2 (Nat.dvd_refl _)
    have e : 2 ^ (4 * 5 ^ K * q) = (16 ^ (5 ^ K)) ^ q := by
      rw [Nat.mul_assoc, Nat.pow_mul 2 4 (5 ^ K * q), ← Nat.pow_mul 16 (5 ^ K) q]
      try rfl
    rw [e, Nat.pow_mod, h, Nat.one_pow]
    exact Nat.mod_eq_of_lt (one_lt_pow5 K)

theorem mod_cancel_mul_left {m a x y : Nat} (hcop : Nat.Coprime m a) (hxy : y ≤ x)
    (h : (a * x) % m = (a * y) % m) : x % m = y % m := by
  have h1 := Nat.sub_mod_eq_zero_of_mod_eq h
  have h2 : a * x - a * y = a * (x - y) := (Nat.mul_sub a x y).symm
  rw [h2] at h1
  have h3 : m ∣ a * (x - y) := Nat.dvd_of_mod_eq_zero h1
  have h4 : m ∣ x - y := Nat.Coprime.dvd_of_dvd_mul_left hcop h3
  have h5 := Nat.mod_eq_zero_of_dvd h4
  have h6 : x = y + (x - y) := by omega
  rw [h6, Nat.add_mod, h5]; simp

theorem two_pow_inj {K E1 E2 : Nat} (h1 : E1 < 4 * 5 ^ K) (h2 : E2 < 4 * 5 ^ K)
    (h : 2 ^ E1 % 5 ^ (K + 1) = 2 ^ E2 % 5 ^ (K + 1)) : E1 = E2 := by
  have key : ∀ a b : Nat, a ≤ b → b < 4 * 5 ^ K →
      2 ^ a % 5 ^ (K + 1) = 2 ^ b % 5 ^ (K + 1) → a = b := by
    intro a b hab hb h
    have hcop : Nat.Coprime (5 ^ (K + 1)) (2 ^ a) := Nat.Coprime.pow (K + 1) a (by decide)
    have hb' : 2 ^ b = 2 ^ a * 2 ^ (b - a) := by rw [← Nat.pow_add]; congr 1; omega
    have h' : (2 ^ a * 2 ^ (b - a)) % 5 ^ (K + 1) = (2 ^ a * 1) % 5 ^ (K + 1) := by
      rw [← hb', Nat.mul_one]; exact h.symm
    have hpos : 1 ≤ 2 ^ (b - a) := Nat.pow_pos (by decide)
    have h'' := mod_cancel_mul_left hcop hpos h'
    have hd := two_pow_mod_eq_one_iff.1 (by rw [h'']; exact Nat.mod_eq_of_lt (one_lt_pow5 K))
    have : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  rcases Nat.le_total E1 E2 with hle | hle
  · exact key _ _ hle h2 h
  · exact (key _ _ hle h1 h.symm).symm

theorem coprime5 {c : Nat} (hc : c % 5 ≠ 0) : Nat.Coprime 5 c := by
  unfold Nat.Coprime
  rw [Nat.gcd_rec]
  have : c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := by omega
  rcases this with h | h | h | h <;> rw [h] <;> decide

theorem live_mul5 {x y : Nat} (hx : x % 5 ≠ 0) (hy : y % 5 ≠ 0) : (x * y) % 5 ≠ 0 := by
  rw [Nat.mul_mod]
  have hx' : x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by omega
  have hy' : y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by omega
  rcases hx' with h | h | h | h <;> rcases hy' with h' | h' | h' | h' <;> simp [h, h']

theorem mod_cancel_mul_right {m c x y : Nat} (hcop : Nat.Coprime m c)
    (h : (x * c) % m = (y * c) % m) : x % m = y % m := by
  rcases Nat.le_total y x with hle | hle
  · exact mod_cancel_mul_left hcop hle (by rwa [Nat.mul_comm c x, Nat.mul_comm c y])
  · exact (mod_cancel_mul_left hcop hle (by rw [Nat.mul_comm c x, Nat.mul_comm c y]; exact h.symm)).symm

theorem two_generates_live {K c d : Nat} (hc : c % 5 ≠ 0) (hd : d % 5 ≠ 0)
    (hdl : d < 5 ^ (K + 1)) : ∃ j, (2 ^ j * c) % 5 ^ (K + 1) = d := by
  apply Classical.byContradiction
  intro hno
  have hno' : ∀ j, (2 ^ j * c) % 5 ^ (K + 1) ≠ d := fun j hj => hno ⟨j, hj⟩
  have hcop : Nat.Coprime (5 ^ (K + 1)) c := Nat.Coprime.pow_left (K + 1) (coprime5 hc)
  let U : List Nat := (List.range (5 ^ (K + 1))).filter (fun w => decide (w % 5 ≠ 0))
  let L1 : List Nat := (List.range (4 * 5 ^ K)).map (fun E => (2 ^ E * c) % 5 ^ (K + 1))
  have hUnodup : U.Nodup := List.Pairwise.filter _ List.nodup_range
  have hL1nodup : L1.Nodup := by
    unfold L1
    apply List.pairwise_map.2
    apply List.Pairwise.imp_of_mem _ (List.nodup_range)
    intro a b ha hb hab heq
    rw [List.mem_range] at ha hb
    have h1 := mod_cancel_mul_right hcop heq
    exact hab (two_pow_inj ha hb h1)
  have hL1U : L1 ⊆ U := by
    intro w hw
    unfold L1 at hw
    rw [List.mem_map] at hw
    obtain ⟨E, _, rfl⟩ := hw
    unfold U
    rw [List.mem_filter, List.mem_range]
    refine ⟨Nat.mod_lt _ (by omega), ?_⟩
    have := live_mod (five_dvd_pow K) (live_mul5 (two_pow_mod_five_ne E) hc)
    simpa using this
  have hdU : d ∈ U := by
    unfold U; rw [List.mem_filter, List.mem_range]; exact ⟨hdl, by simpa using hd⟩
  have hdL1 : d ∉ L1 := by
    unfold L1
    intro h
    rw [List.mem_map] at h
    obtain ⟨E, _, hE⟩ := h
    exact hno' E hE
  have hcons : (d :: L1).Nodup := List.nodup_cons.2 ⟨hdL1, hL1nodup⟩
  have hcsub : (d :: L1) ⊆ U := by
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hdU
    · exact hL1U hw
  have hlen1 : (d :: L1).length ≤ U.length := hcons.length_le_of_subset hcsub
  have hUsub : U ⊆ (List.range (4 * 5 ^ K)).map (fun j => 5 * (j / 4) + 1 + j % 4) := by
    intro w hw
    unfold U at hw
    rw [List.mem_filter, List.mem_range] at hw
    obtain ⟨hw1, hw2⟩ := hw
    have hw2' : w % 5 ≠ 0 := by simpa using hw2
    rw [List.mem_map]
    refine ⟨4 * (w / 5) + (w % 5 - 1), ?_, ?_⟩
    · rw [List.mem_range]; omega
    · omega
  have hlen2 : U.length ≤ 4 * 5 ^ K := by
    have := hUnodup.length_le_of_subset hUsub
    simpa using this
  have hL1len : L1.length = 4 * 5 ^ K := by simp [L1]
  simp only [List.length_cons] at hlen1
  omega

section Residues
variable (M : Nat) [NeZero M]

def residue (n : Nat) : Fin M := Fin.ofNat M n

theorem residue_val (n : Nat) : (residue M n).val = n % M := Fin.val_ofNat M n

theorem residue_eq_iff (a b : Nat) : residue M a = residue M b ↔ a % M = b % M := by
  constructor
  · intro h; have := congrArg Fin.val h; rwa [residue_val, residue_val] at this
  · intro h; apply Fin.ext; rw [residue_val, residue_val]; exact h

theorem residue_add (a b : Nat) : residue M (a + b) = residue M a + residue M b := by
  apply Fin.ext; rw [Fin.val_add, residue_val, residue_val, residue_val, Nat.add_mod]

theorem residue_mul (a b : Nat) : residue M (a * b) = residue M a * residue M b := by
  apply Fin.ext; rw [Fin.val_mul, residue_val, residue_val, residue_val, Nat.mul_mod]

theorem residue_zero : residue M 0 = (0 : Fin M) := rfl
theorem residue_one : residue M 1 = (1 : Fin M) := rfl
theorem residue_two : residue M 2 = (2 : Fin M) := rfl
theorem residue_five : residue M 5 = (5 : Fin M) := rfl
class TwoFiveInvertible (M : Nat) [NeZero M] : Prop where
  two : ∃ b : Fin M, (2 : Fin M) * b = 1
  five : ∃ b : Fin M, (5 : Fin M) * b = 1

open Classical in
noncomputable def unitInv (a : Fin M) : Fin M := if h : ∃ b : Fin M, a * b = 1 then h.choose else 0

theorem mul_unitInv {a : Fin M} (h : ∃ b : Fin M, a * b = 1) : a * unitInv M a = 1 := by
  unfold unitInv
  split
  · rename_i h'; exact h'.choose_spec
  · rename_i h'; exact absurd h h'

theorem two_mul_unitInv [TwoFiveInvertible M] : (2 : Fin M) * unitInv M 2 = 1 := mul_unitInv M TwoFiveInvertible.two
theorem five_mul_unitInv [TwoFiveInvertible M] : (5 : Fin M) * unitInv M 5 = 1 := mul_unitInv M TwoFiveInvertible.five

theorem hA_id (T r v : Fin M) (h5 : (5 : Fin M) * v = 1) :
    residue M 5 * ((0 : Fin M) + v - T * (0 : Fin M) - r * v) = residue M 1 - r := by
  rw [residue_five, residue_one]
  grind

theorem hB_id (m i i₀ : Nat) (u : Fin M)
    (hu : residue M (2 ^ m) * u = 1) (h5 : (5 : Fin M) * unitInv M 5 = 1) :
    residue M 5 * (residue M (5 * 2 ^ m) * (-(u * unitInv M 5) + unitInv M 5
        - unitInv M 5 * (2 * residue M (2 ^ i₀)) * -(u * unitInv M 5)
        - u * unitInv M 5 * 2 * residue M (2 ^ i) * unitInv M 5))
      = residue M (5 * 2 ^ m + 2 * 2 ^ i₀) - residue M (5 + 2 * 2 ^ i) := by
  rw [residue_mul M 5 (2 ^ m), residue_add M (5 * 2 ^ m) (2 * 2 ^ i₀),
    residue_add M 5 (2 * 2 ^ i), residue_mul M 5 (2 ^ m), residue_mul M 2 (2 ^ i₀),
    residue_mul M 2 (2 ^ i), residue_five, residue_two]
  grind

theorem cancel_invertible {u v a b : Fin M} (hu : u * v = 1) (h : u * a = u * b) : a = b := by
  calc a = (u * v) * a := by rw [hu]; grind
    _ = v * (u * a) := by grind
    _ = v * (u * b) := by rw [h]
    _ = (u * v) * b := by grind
    _ = b := by rw [hu]; grind

def IsInvertible (a : Fin M) : Prop := ∃ b : Fin M, a * b = 1

theorem isInvertible_mul {a b : Fin M} (ha : IsInvertible M a) (hb : IsInvertible M b) : IsInvertible M (a * b) := by
  obtain ⟨ia, hia⟩ := ha
  obtain ⟨ib, hib⟩ := hb
  exact ⟨ib * ia, by
    calc a * b * (ib * ia) = (a * ia) * (b * ib) := by grind
      _ = 1 := by rw [hia, hib]; grind⟩

theorem unitInv_eq_of_mul {a b : Fin M} (h : a * b = 1) : unitInv M a = b :=
  cancel_invertible M h ((mul_unitInv M ⟨b, h⟩).trans h.symm)

theorem isInvertible_unitInv {a : Fin M} (h : IsInvertible M a) : IsInvertible M (unitInv M a) :=
  ⟨a, by have := mul_unitInv M h; grind⟩

end Residues

section Counting
variable {M : Nat}

open Classical in
noncomputable def cardinality (S : Fin M → Prop) : Nat :=
  ((List.finRange M).filter (fun t => decide (S t))).length

open Classical in
theorem mem_cardlist {S : Fin M → Prop} {t : Fin M} :
    t ∈ (List.finRange M).filter (fun t => decide (S t)) ↔ S t := by
  rw [List.mem_filter]; simp [List.mem_finRange]

open Classical in
theorem cardinality_le_of_inj {S T : Fin M → Prop} (g : Fin M → Fin M)
    (hinj : ∀ a b, g a = g b → a = b) (hmap : ∀ t, S t → T (g t)) : cardinality S ≤ cardinality T := by
  unfold cardinality
  have hnd : ((List.finRange M).filter (fun t => decide (S t))).Nodup :=
    List.Pairwise.filter _ (List.nodup_finRange M)
  have hnd2 : (((List.finRange M).filter (fun t => decide (S t))).map g).Nodup := by
    apply List.pairwise_map.2
    apply List.Pairwise.imp_of_mem _ hnd
    intro a b _ _ hab hg
    exact hab (hinj a b hg)
  have hsub : ((List.finRange M).filter (fun t => decide (S t))).map g
      ⊆ (List.finRange M).filter (fun t => decide (T t)) := by
    intro u hu
    rw [List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    rw [mem_cardlist] at ht ⊢
    exact hmap t ht
  have := hnd2.length_le_of_subset hsub
  simpa using this

open Classical in
theorem cardinality_eq_of_sub {S T : Fin M → Prop} (hsub : ∀ t, S t → T t) (hc : cardinality T ≤ cardinality S) :
    ∀ t, T t → S t := by
  intro t0 ht0
  apply Classical.byContradiction
  intro hn
  unfold cardinality at hc
  have hnd : ((List.finRange M).filter (fun t => decide (S t))).Nodup :=
    List.Pairwise.filter _ (List.nodup_finRange M)
  have hnd2 : (t0 :: (List.finRange M).filter (fun t => decide (S t))).Nodup := by
    rw [List.nodup_cons]
    exact ⟨fun h => hn ((mem_cardlist).1 h), hnd⟩
  have hsub2 : (t0 :: (List.finRange M).filter (fun t => decide (S t)))
      ⊆ (List.finRange M).filter (fun t => decide (T t)) := by
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact (mem_cardlist).2 ht0
    · exact (mem_cardlist).2 (hsub u ((mem_cardlist).1 hu))
  have := hnd2.length_le_of_subset hsub2
  simp only [List.length_cons] at this
  omega

open Classical in
theorem cardinality_pos {S : Fin M → Prop} {t0 : Fin M} (h : S t0) : 1 ≤ cardinality S := by
  unfold cardinality
  exact List.length_pos_of_mem ((mem_cardlist).2 h)

end Counting

theorem exists_inv_of_coprime {M : Nat} [NeZero M] (a : Fin M) (hcop : Nat.Coprime M a.val) :
    ∃ b : Fin M, a * b = 1 := by
  have hinj : ∀ s t : Fin M, a * s = a * t → s = t := by
    intro s t h
    have h1 := congrArg Fin.val h
    rw [Fin.val_mul, Fin.val_mul] at h1
    have h2 : (s.val * a.val) % M = (t.val * a.val) % M := by
      rw [Nat.mul_comm s.val, Nat.mul_comm t.val]; exact h1
    have h3 := mod_cancel_mul_right hcop h2
    rw [Nat.mod_eq_of_lt s.isLt, Nat.mod_eq_of_lt t.isLt] at h3
    exact Fin.ext h3
  have hc : cardinality (fun _ : Fin M => True) ≤ cardinality (fun t : Fin M => ∃ s, a * s = t) :=
    cardinality_le_of_inj (fun t => a * t) hinj (fun t _ => ⟨t, rfl⟩)
  exact cardinality_eq_of_sub (S := fun t : Fin M => ∃ s, a * s = t) (T := fun _ : Fin M => True)
    (fun _ _ => trivial) hc 1 trivial

theorem exists_inv_residue {M : Nat} [NeZero M] (n : Nat) (hcop : Nat.Coprime M n) :
    ∃ b : Fin M, residue M n * b = 1 := by
  apply exists_inv_of_coprime
  rw [residue_val]
  unfold Nat.Coprime at hcop ⊢
  rw [Nat.gcd_comm, ← Nat.gcd_rec]; exact hcop

theorem twoFiveInvertible_of_coprime10 {M : Nat} [NeZero M] (h6 : Nat.Coprime M 10) : TwoFiveInvertible M :=
  ⟨exists_inv_residue 2 (Nat.Coprime.coprime_dvd_right (by decide) h6),
   exists_inv_residue 5 (Nat.Coprime.coprime_dvd_right (by decide) h6)⟩

def oneCount : List Nat → Nat
  | [] => 0
  | e :: u => oneCount u + e
def offset : List Nat → Nat
  | [] => 0
  | e :: u => 5 ^ oneCount u * e + 2 * offset u

theorem collatz_odd (y : Nat) : collatz (2 * y + 1) = 10 * y + 6 := by
  unfold collatz; split <;> omega

theorem collatz_ten_mul_add_six (y : Nat) : collatz (10 * y + 6) = 5 * y + 3 := by
  have := collatz_double (5 * y + 3)
  rwa [show 2 * (5 * y + 3) = 10 * y + 6 by omega] at this
theorem integrality : ∀ (u : List Nat), (∀ e ∈ u, e ≤ 1) → ∀ x : Nat,
    2 ^ u.length ∣ 5 ^ oneCount u * x + offset u →
    ∃ k, iter collatz k x = (5 ^ oneCount u * x + offset u) / 2 ^ u.length
  | [], _, x, _ => ⟨0, by simp [oneCount, offset, iter]⟩
  | e :: u, hu, x, h => by
    have he : e = 0 ∨ e = 1 := by have := hu e (by simp); omega
    have hu' : ∀ d ∈ u, d ≤ 1 := fun d hd => hu d (by simp [hd])
    have hp : 5 ^ oneCount u % 2 = 1 := by rw [Nat.pow_mod]; simp
    have h2 : 2 ∣ 2 ^ (u.length + 1) := ⟨2 ^ u.length, by grind⟩
    have hpow : 2 ^ (u.length + 1) = 2 * 2 ^ u.length := by grind
    simp only [List.length_cons, oneCount, offset] at h ⊢
    rcases he with rfl | rfl
    ·
      have h0 := Nat.dvd_trans h2 h
      obtain ⟨y, hy | hy⟩ : ∃ y, x = 2 * y ∨ x = 2 * y + 1 := ⟨x / 2, by omega⟩
      · subst hy
        have hn : 5 ^ (oneCount u + 0) * (2 * y) + (5 ^ oneCount u * 0 + 2 * offset u)
            = 2 * (5 ^ oneCount u * y + offset u) := by grind
        rw [hn, hpow] at h
        have h' := (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).1 h
        obtain ⟨k, hk⟩ := integrality u hu' y h'
        refine ⟨k + 1, ?_⟩
        show iter collatz k (collatz (2 * y)) = _
        rw [collatz_double, hk, hn, hpow, Nat.mul_div_mul_left _ _ (by omega : 0 < 2)]
      · subst hy
        exfalso
        have hn : 5 ^ (oneCount u + 0) * (2 * y + 1) + (5 ^ oneCount u * 0 + 2 * offset u)
            = 2 * (5 ^ oneCount u * y + offset u) + 5 ^ oneCount u := by grind
        rw [hn] at h0
        generalize 5 ^ oneCount u * y + offset u = P at h0
        omega
    ·
      have h0 := Nat.dvd_trans h2 h
      obtain ⟨y, hy | hy⟩ : ∃ y, x = 2 * y ∨ x = 2 * y + 1 := ⟨x / 2, by omega⟩
      · subst hy
        exfalso
        have hn : 5 ^ (oneCount u + 1) * (2 * y) + (5 ^ oneCount u * 1 + 2 * offset u)
            = 2 * (5 ^ oneCount u * (5 * y) + offset u) + 5 ^ oneCount u := by grind
        rw [hn] at h0
        generalize 5 ^ oneCount u * (5 * y) + offset u = P at h0
        omega
      · subst hy
        have hn : 5 ^ (oneCount u + 1) * (2 * y + 1) + (5 ^ oneCount u * 1 + 2 * offset u)
            = 2 * (5 ^ oneCount u * (5 * y + 3) + offset u) := by grind
        rw [hn, hpow] at h
        have h' := (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).1 h
        obtain ⟨k, hk⟩ := integrality u hu' (5 * y + 3) h'
        refine ⟨k + 2, ?_⟩
        show iter collatz k (collatz (collatz (2 * y + 1))) = _
        rw [collatz_odd, collatz_ten_mul_add_six, hk, hn, hpow, Nat.mul_div_mul_left _ _ (by omega : 0 < 2)]

theorem mod_combine_le {P Q n r : Nat} (hPQ : Nat.Coprime P Q) (hle : r ≤ n)
    (hP : n % P = r % P) (hQ : n % Q = r % Q) : n % (P * Q) = r % (P * Q) := by
  have h1 : P ∣ n - r := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hP)
  have h2 : Q ∣ n - r := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hQ)
  obtain ⟨k, hk⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd hPQ h1 h2
  have : n = r + (P * Q) * k := by omega
  rw [this, Nat.add_mul_mod_self_left]

theorem mod_combine {P Q n r : Nat} (hPQ : Nat.Coprime P Q)
    (hP : n % P = r % P) (hQ : n % Q = r % Q) : n % (P * Q) = r % (P * Q) := by
  rcases Nat.le_total r n with h | h
  · exact mod_combine_le hPQ h hP hQ
  · exact (mod_combine_le hPQ h hP.symm hQ.symm).symm

theorem residue_self_val {n : Nat} [NeZero n] (v : Fin n) : residue n v.val = v :=
  Fin.ext (by rw [residue_val, Nat.mod_eq_of_lt v.isLt])

theorem crt_exists {m n : Nat} [NeZero n] (h : Nat.Coprime n m) (a b : Nat) :
    ∃ y, y % m = a % m ∧ y % n = b % n := by
  obtain ⟨v, hv⟩ := exists_inv_residue (M := n) m h
  refine ⟨a + m * (v.val * (b + (n - 1) * a)), Nat.add_mul_mod_self_left a m _, ?_⟩
  have hn1 : residue n (n - 1) + 1 = 0 := by
    rw [← residue_one n, ← residue_add]
    apply Fin.ext; rw [residue_val, show n - 1 + 1 = n by have := NeZero.ne n; omega, Nat.mod_self]; rfl
  rw [← residue_eq_iff]
  rw [residue_add, residue_mul, residue_mul, residue_add, residue_mul, residue_self_val]
  grind

section Period
variable (M : Nat) [NeZero M]

def IsSixteenPeriod (m : Nat) : Prop := residue M (16 ^ m) = 1

theorem isSixteenPeriod_add {m n : Nat} (hm : IsSixteenPeriod M m) (hn : IsSixteenPeriod M n) : IsSixteenPeriod M (m + n) := by
  unfold IsSixteenPeriod at *
  rw [Nat.pow_add, residue_mul, hm, hn]; grind

theorem isSixteenPeriod_mul {n : Nat} (hn : IsSixteenPeriod M n) : ∀ q, IsSixteenPeriod M (n * q) := by
  intro q
  induction q with
  | zero => unfold IsSixteenPeriod; rw [Nat.mul_zero, Nat.pow_zero, residue_one]
  | succ q ih => rw [Nat.mul_succ]; exact isSixteenPeriod_add M ih hn

theorem isSixteenPeriod_cancel {m n : Nat} (hn : IsSixteenPeriod M n) (h : IsSixteenPeriod M (m + n)) : IsSixteenPeriod M m := by
  unfold IsSixteenPeriod at *
  rw [Nat.pow_add, residue_mul, hn] at h
  rw [← h]; grind

theorem isSixteenPeriod_mod {m n : Nat} (hn : IsSixteenPeriod M n) (hm : IsSixteenPeriod M m) : IsSixteenPeriod M (m % n) := by
  have h := Nat.mod_add_div m n
  have h2 : IsSixteenPeriod M (m % n + n * (m / n)) := by rw [h]; exact hm
  exact isSixteenPeriod_cancel M (isSixteenPeriod_mul M hn (m / n)) h2

theorem isSixteenPeriod_gcd : ∀ m n : Nat, IsSixteenPeriod M m → IsSixteenPeriod M n → IsSixteenPeriod M (Nat.gcd m n) := by
  intro m n
  induction m, n using Nat.gcd.induction with
  | H0 n => intro _ hn; rw [Nat.gcd_zero_left]; exact hn
  | H1 m n hm ih =>
    intro h1 h2
    rw [Nat.gcd_rec]
    exact ih (isSixteenPeriod_mod M h1 h2) h1

theorem eq_five_pow_of_dvd : ∀ n d : Nat, d ∣ 5 ^ n → ∃ b, b ≤ n ∧ d = 5 ^ b := by
  intro n
  induction n with
  | zero =>
    intro d hd
    rw [Nat.pow_zero] at hd
    exact ⟨0, Nat.le_refl _, by rw [Nat.pow_zero]; exact Nat.dvd_one.1 hd⟩
  | succ n ih =>
    intro d hd
    by_cases h3 : 5 ∣ d
    · obtain ⟨d', rfl⟩ := h3
      rw [Nat.pow_succ, Nat.mul_comm (5 ^ n) 5] at hd
      obtain ⟨b, hb, hd'⟩ := ih d' (Nat.dvd_of_mul_dvd_mul_left (by decide) hd)
      exact ⟨b + 1, by omega, by rw [hd', Nat.pow_succ]; grind⟩
    · have hcop : Nat.Coprime d 5 := (coprime5 (c := d) (by omega)).symm
      rw [Nat.pow_succ] at hd
      obtain ⟨b, hb, hd'⟩ := ih d (Nat.Coprime.dvd_of_dvd_mul_right hcop hd)
      exact ⟨b, by omega, hd'⟩

theorem exists_min_pow5 : ∀ n : Nat, IsSixteenPeriod M (5 ^ n) →
    ∃ a, a ≤ n ∧ IsSixteenPeriod M (5 ^ a) ∧ ∀ b, b < a → ¬ IsSixteenPeriod M (5 ^ b) := by
  have key : ∀ N n : Nat, n ≤ N → IsSixteenPeriod M (5 ^ n) →
      ∃ a, a ≤ n ∧ IsSixteenPeriod M (5 ^ a) ∧ ∀ b, b < a → ¬ IsSixteenPeriod M (5 ^ b) := by
    intro N
    induction N with
    | zero =>
      intro n hn h
      have : n = 0 := by omega
      subst this
      exact ⟨0, Nat.le_refl _, h, fun b hb => by omega⟩
    | succ N ih =>
      intro n hn h
      by_cases hle : n ≤ N
      · exact ih n hle h
      · by_cases hex : ∃ b, b < n ∧ IsSixteenPeriod M (5 ^ b)
        · obtain ⟨b, hb, hQ⟩ := hex
          obtain ⟨a, ha, h1, h2⟩ := ih b (by omega) hQ
          exact ⟨a, by omega, h1, h2⟩
        · exact ⟨n, Nat.le_refl _, h, fun b hb hQ => hex ⟨b, hb, hQ⟩⟩
  intro n h
  exact key n n (Nat.le_refl _) h

theorem exists_order_pow5 {n : Nat} (h : IsSixteenPeriod M (5 ^ n)) : ∃ a, a ≤ n ∧ ∀ m, IsSixteenPeriod M m ↔ 5 ^ a ∣ m := by
  obtain ⟨a, han, hQa, hmin⟩ := exists_min_pow5 M n h
  refine ⟨a, han, fun m => ⟨fun hm => ?_, fun ⟨q, hq⟩ => ?_⟩⟩
  · have hg := isSixteenPeriod_gcd M m (5 ^ n) hm h
    obtain ⟨b, hb, hgb⟩ := eq_five_pow_of_dvd n _ (Nat.gcd_dvd_right m (5 ^ n))
    rw [hgb] at hg
    have hab : a ≤ b := by
      apply Classical.byContradiction
      intro hlt
      exact hmin b (by omega) hg
    have : 5 ^ a ∣ 5 ^ b := Nat.pow_dvd_pow 5 hab
    rw [← hgb] at this
    exact Nat.dvd_trans this (Nat.gcd_dvd_left m (5 ^ n))
  · rw [hq]; exact isSixteenPeriod_mul M hQa q

theorem five_pow_odd (n : Nat) : 5 ^ n % 2 = 1 := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

end Period

section Least
variable (M : Nat) [NeZero M]
theorem residue_val_self (e : Fin M) : residue M e.val = e := by
  apply Fin.ext; rw [residue_val, Nat.mod_eq_of_lt e.isLt]

theorem residue_self : residue M M = 0 := by
  rw [← residue_zero M]; apply (residue_eq_iff M _ _).2; simp

theorem exists_least (P : Nat → Prop) : (∃ n, P n) → ∃ n, P n ∧ ∀ r, r < n → ¬ P r := by
  rintro ⟨n, hn⟩
  revert hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases h : ∀ r, r < n → ¬ P r
    · exact ⟨n, hn, h⟩
    · obtain ⟨r, hr, hPr⟩ : ∃ r, r < n ∧ P r := by
        apply Classical.byContradiction
        intro hh
        apply h
        intro r hr hp
        exact hh ⟨r, hr, hp⟩
      exact ih r hr hPr

end Least

theorem mod_eq_of_le_sub {m X Y : Nat} (hle : Y ≤ X) (h : (X - Y) % m = 0) : X % m = Y % m := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
  have : X = Y + m * k := by omega
  rw [this, Nat.add_mul_mod_self_left]

theorem mod_add_left_cancel {m e X Y : Nat} (h : (e + X) % m = (e + Y) % m) : X % m = Y % m := by
  rcases Nat.le_total Y X with hle | hle
  · exact mod_eq_of_le_sub hle (by
      have := Nat.sub_mod_eq_zero_of_mod_eq h
      rwa [show e + X - (e + Y) = X - Y by omega] at this)
  · exact (mod_eq_of_le_sub hle (by
      have := Nat.sub_mod_eq_zero_of_mod_eq h.symm
      rwa [show e + Y - (e + X) = Y - X by omega] at this)).symm

theorem isSixteenPeriod_iff (q : Nat) [NeZero q] (n : Nat) : IsSixteenPeriod q n ↔ 16 ^ n % q = 1 % q := by
  unfold IsSixteenPeriod; rw [← residue_one q, residue_eq_iff]

theorem pow_mod_period {b y n : Nat} (h : b ^ y % n = 1 % n) (x : Nat) :
    ∀ N, b ^ (x + y * N) % n = b ^ x % n
  | 0 => by simp
  | N + 1 => by
    rw [Nat.mul_succ, ← Nat.add_assoc, Nat.pow_add, Nat.mul_mod, pow_mod_period h x N, h,
      ← Nat.mul_mod, Nat.mul_one]

theorem four_dvd_of_mod5 {n : Nat} (h : 2 ^ n % 5 = 1) : ∃ d, n = 4 * d := by
  obtain ⟨a, r, hn, hr⟩ : ∃ a r, n = 4 * a + r ∧ r < 4 :=
    ⟨n / 4, n % 4, (Nat.div_add_mod n 4).symm, Nat.mod_lt _ (by omega)⟩
  by_cases h0 : r = 0
  · exact ⟨a, by omega⟩
  · exfalso
    have e : 2 ^ n = 16 ^ a * 2 ^ r := by rw [hn, Nat.pow_add, Nat.pow_mul]
    rw [e, Nat.mul_mod, sixteen_pow_mod_five, Nat.one_mul] at h
    rcases (show r = 1 ∨ r = 2 ∨ r = 3 by omega) with h1 | h1 | h1
    · rw [h1] at h; exact absurd h (by decide)
    · rw [h1] at h; exact absurd h (by decide)
    · rw [h1] at h; exact absurd h (by decide)

theorem mod_of_dvd_mod {a b P Z : Nat} (hZ : Z ∣ P) (h : a % P = b % P) : a % Z = b % Z := by
  rw [← Nat.mod_mod_of_dvd a hZ, h, Nat.mod_mod_of_dvd b hZ]

theorem two_pow_mod_fifteen : ∀ n : Nat, 2 ^ n % 15 = 1 ∨ 2 ^ n % 15 = 2 ∨ 2 ^ n % 15 = 4 ∨ 2 ^ n % 15 = 8
  | 0 => by decide
  | n + 1 => by rw [Nat.pow_succ, Nat.mul_mod]; rcases two_pow_mod_fifteen n with h | h | h | h <;> rw [h] <;> decide

theorem two_pow_mod_three_of_mod_five {n : Nat} (h : 2 ^ n % 5 = 3) : 2 ^ n % 3 = 2 := by
  have h5 : 2 ^ n % 15 % 5 = 2 ^ n % 5 := Nat.mod_mod_of_dvd _ (by decide)
  have h3 : 2 ^ n % 15 % 3 = 2 ^ n % 3 := Nat.mod_mod_of_dvd _ (by decide)
  rcases two_pow_mod_fifteen n with e | e | e | e <;> rw [e] at h5 h3 <;> omega

theorem period_contra (q K i₀ : Nat) [NeZero q] (hq1 : 1 < q) (hq5 : Nat.Coprime q 5)
    (hi₀ : 2 ^ i₀ % 5 ^ (K + 1) = 3 % 5 ^ (K + 1))
    (hA : IsSixteenPeriod q (5 ^ K))
    (hB : ∀ g a' i m : Nat, g % 5 ≠ 0 → a' % 5 ≠ 0 →
      (5 * a' + 1) % 5 ^ (K + 1) = (2 * g) % 5 ^ (K + 1) →
      2 ^ i % 5 ^ (K + 1) = g % 5 ^ (K + 1) → 2 ^ m % 5 ^ (K + 1) = a' % 5 ^ (K + 1) →
      (5 * 2 ^ m + 2 * 2 ^ i₀) % q = (5 + 2 * 2 ^ i) % q) : False := by
  have hP5 : 5 ∣ 5 ^ (K + 1) := five_dvd_pow K
  obtain ⟨α, hαK, hord⟩ := exists_order_pow5 q hA
  have hα : 1 ≤ α := by
    rcases Nat.eq_zero_or_pos α with h0 | h0
    · exfalso
      have h1 := (isSixteenPeriod_iff q 1).1 ((hord 1).2 (by rw [h0]; exact Nat.dvd_refl _))
      have h3 : 15 % q = 0 % q := mod_add_left_cancel (e := 1) (by rw [Nat.pow_one] at h1; exact h1)
      have hq3 : q = 3 := by
        have h15 : q ∣ 3 * 5 := Nat.dvd_of_mod_eq_zero (by rw [h3, Nat.zero_mod])
        have hd := Nat.Coprime.dvd_of_dvd_mul_right hq5 h15
        have := Nat.le_of_dvd (by decide) hd
        rcases (by omega : q = 2 ∨ q = 3) with h | h
        · rw [h] at hd; exact absurd hd (by decide)
        · exact h
      have hP0 : 5 ^ (K + 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd hP5
      obtain ⟨h2, hh2⟩ : ∃ h2, 2 * h2 = 5 ^ (K + 1) + 1 := ⟨(5 ^ (K + 1) + 1) / 2, by
        have hodd : 5 ^ (K + 1) % 2 = 1 := five_pow_odd (K + 1)
        omega⟩
      have hg : (5 + h2) % 5 ≠ 0 := by omega
      obtain ⟨i, hi⟩ := two_generates_live (K := K) (c := 1) (d := (5 + h2) % 5 ^ (K + 1)) (by decide)
        (by rw [Nat.mod_mod_of_dvd _ hP5]; exact hg) (Nat.mod_lt _ (Nat.pow_pos (by omega)))
      rw [Nat.mul_one] at hi
      have h3' : (5 * 2 + 1) % 5 ^ (K + 1) = (2 * (5 + h2)) % 5 ^ (K + 1) := by
        rw [show 2 * (5 + h2) = 11 + 5 ^ (K + 1) by omega, Nat.add_mod_right]
      have hqB := hB (5 + h2) 2 i 1 hg (by decide) h3' hi (by rw [Nat.pow_one])
      rw [hq3] at hqB
      have hi5 : 2 ^ i % 5 = 3 := by have := mod_of_dvd_mod hP5 hi; omega
      have hi₀5 : 2 ^ i₀ % 5 = 3 := mod_of_dvd_mod hP5 hi₀
      have e1 := two_pow_mod_three_of_mod_five hi5
      have e2 := two_pow_mod_three_of_mod_five hi₀5
      omega
    · exact h0
  obtain ⟨α', rfl⟩ : ∃ α', α = α' + 1 := ⟨α - 1, by omega⟩
  have hZi2 : 5 ^ (α' + 2) ∣ 5 ^ (K + 1) := Nat.pow_dvd_pow 5 (by omega)
  have h3a : 5 ^ (α' + 1) = 5 * 5 ^ α' := by rw [Nat.pow_succ, Nat.mul_comm]
  have hα1 : 5 ^ (α' + 1 + 1) = 5 * 5 ^ (α' + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  obtain ⟨h2, hh2⟩ : ∃ h2, 2 * h2 = 5 ^ (K + 1) + 1 := ⟨(5 ^ (K + 1) + 1) / 2, by
    have hodd : 5 ^ (K + 1) % 2 = 1 := five_pow_odd (K + 1)
    omega⟩
  let g := 3 + 5 ^ (α' + 1 + 1) * h2
  let a' := 1 + 5 ^ (α' + 1)
  have hg : g % 5 ≠ 0 := by
    show (3 + 5 ^ (α' + 1 + 1) * h2) % 5 ≠ 0
    rw [hα1, Nat.mul_assoc, Nat.add_mul_mod_self_left]
    decide
  have ha : a' % 5 ≠ 0 := by
    show (1 + 5 ^ (α' + 1)) % 5 ≠ 0
    rw [h3a, Nat.add_mul_mod_self_left]
    decide
  have h2g : 2 * g = (5 * a' + 1) + 5 ^ (α' + 1 + 1) * 5 ^ (K + 1) := by
    show 2 * (3 + 5 ^ (α' + 1 + 1) * h2) = 5 * (1 + 5 ^ (α' + 1)) + 1
        + 5 ^ (α' + 1 + 1) * 5 ^ (K + 1)
    have e : 2 * (5 ^ (α' + 1 + 1) * h2) = 5 ^ (α' + 1 + 1) * (2 * h2) := by grind
    rw [Nat.mul_add, e, hh2, hα1, h3a]; grind
  have h3 : (5 * a' + 1) % 5 ^ (K + 1) = (2 * g) % 5 ^ (K + 1) := by
    rw [h2g, Nat.add_mul_mod_self_right]
  have hgi : g % 5 ^ (α' + 2) = 3 % 5 ^ (α' + 2) := by
    show (3 + 5 ^ (α' + 1 + 1) * h2) % 5 ^ (α' + 2) = 3 % 5 ^ (α' + 2)
    rw [show 5 ^ (α' + 1 + 1) = 5 ^ (α' + 2) by rfl, Nat.mul_comm (5 ^ (α' + 2)) h2,
      Nat.add_mul_mod_self_right]
  have hlive : ∀ x, x % 5 ≠ 0 → ∃ j, 2 ^ j % 5 ^ (K + 1) = x % 5 ^ (K + 1) := by
    intro x hx
    obtain ⟨j, hj⟩ := two_generates_live (K := K) (c := 1) (d := x % 5 ^ (K + 1)) (by decide)
      (by rw [Nat.mod_mod_of_dvd x hP5]; exact hx) (Nat.mod_lt _ (Nat.pow_pos (by omega)))
    exact ⟨j, by rw [Nat.mul_one] at hj; exact hj⟩
  obtain ⟨i, hi⟩ := hlive g hg
  obtain ⟨m, hm⟩ := hlive a' ha
  have hqB := hB g a' i m hg ha h3 hi hm
  have key : ∀ j1 j2 : Nat, j2 ≤ j1 → 2 ^ j1 % 5 ^ (α' + 2) = 2 ^ j2 % 5 ^ (α' + 2) →
      2 ^ j1 % q = 2 ^ j2 % q := by
    intro j1 j2 hle h12
    have hcop : Nat.Coprime (5 ^ (α' + 2)) (2 ^ j2) :=
      Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ (by decide))
    have hc : (2 ^ j2 * 2 ^ (j1 - j2)) % 5 ^ (α' + 2) = (2 ^ j2 * 1) % 5 ^ (α' + 2) := by
      rw [← Nat.pow_add, Nat.mul_one, show j2 + (j1 - j2) = j1 by omega]; exact h12
    have h1' : 2 ^ (j1 - j2) % 5 ^ (α' + 2) = 1 := by
      have h2'' := mod_cancel_mul_left hcop (Nat.pow_pos (by decide)) hc
      rwa [Nat.mod_eq_of_lt (one_lt_pow5 (α' + 1))] at h2''
    obtain ⟨t, ht⟩ := two_pow_mod_eq_one_iff.1 h1'
    have e2 : 2 ^ (4 * 5 ^ (α' + 1)) = 16 ^ (5 ^ (α' + 1)) := by rw [Nat.pow_mul]
    have hper : IsSixteenPeriod q (5 ^ (α' + 1)) := (hord _).2 (Nat.dvd_refl _)
    have hT : 16 ^ (5 ^ (α' + 1)) % q = 1 % q := (isSixteenPeriod_iff q (5 ^ (α' + 1))).1 hper
    have h1q : (1 : Nat) % q = 1 := Nat.mod_eq_of_lt (by omega)
    have hq2 : (16 ^ (5 ^ (α' + 1))) ^ t % q = 1 % q := by
      rw [Nat.pow_mod, hT, h1q, Nat.one_pow, h1q]
    have e : 2 ^ j1 = 2 ^ j2 * 2 ^ (j1 - j2) := by rw [← Nat.pow_add]; congr 1; omega
    rw [e, Nat.mul_mod (2 ^ j2) (2 ^ (j1 - j2)) q, ht, Nat.pow_mul 2 (4 * 5 ^ (α' + 1)) t,
      e2, hq2, h1q, Nat.mul_one, Nat.mod_mod_of_dvd (2 ^ j2) (Nat.dvd_refl q)]
  have h2iq : 2 ^ i % q = 2 ^ i₀ % q := by
    have h1 : 2 ^ i % 5 ^ (α' + 2) = 3 % 5 ^ (α' + 2) := by
      have hz := mod_of_dvd_mod hZi2 hi
      rw [hz, hgi]
    have h2' : 2 ^ i₀ % 5 ^ (α' + 2) = 3 % 5 ^ (α' + 2) := mod_of_dvd_mod hZi2 hi₀
    rcases Nat.le_total i₀ i with hle | hle
    · exact key i i₀ hle (by rw [h1, h2'])
    · exact (key i₀ i hle (by rw [h2', h1])).symm
  have h5 : (5 + 2 * 2 ^ i) % q = (5 + 2 * 2 ^ i₀) % q := by
    rw [Nat.add_mod 5 (2 * 2 ^ i) q, Nat.add_mod 5 (2 * 2 ^ i₀) q,
      Nat.mul_mod 2 (2 ^ i) q, Nat.mul_mod 2 (2 ^ i₀) q, h2iq]
  have hq' : (2 * 2 ^ i₀ + 5 * 2 ^ m) % q = (2 * 2 ^ i₀ + 5) % q := by
    have e1 : 2 * 2 ^ i₀ + 5 * 2 ^ m = 5 * 2 ^ m + 2 * 2 ^ i₀ := Nat.add_comm _ _
    have e2 : 2 * 2 ^ i₀ + 5 = 5 + 2 * 2 ^ i₀ := Nat.add_comm _ _
    rw [e1, e2, ← h5]; exact hqB
  have h5m : (5 * 2 ^ m) % q = 5 % q := mod_add_left_cancel hq'
  have hm1 : 2 ^ m % q = 1 % q := by
    have h5m' : (5 * 2 ^ m) % q = (5 * 1) % q := by rw [Nat.mul_one]; exact h5m
    exact mod_cancel_mul_left hq5 (Nat.pow_pos (by decide)) h5m'
  have h1q : (1 : Nat) % q = 1 := Nat.mod_eq_of_lt (by omega)
  have h16m : 16 ^ m % q = 1 % q := by
    have e : 16 ^ m = (2 ^ m) ^ 4 := by
      rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
    rw [e, Nat.pow_mod, hm1, h1q, Nat.one_pow]
    exact h1q
  have hpm : IsSixteenPeriod q m := (isSixteenPeriod_iff q m).2 h16m
  have hdm : 5 ^ (α' + 1) ∣ m := (hord m).1 hpm
  have hm5 : 2 ^ m % 5 = 1 := by
    have hz := mod_of_dvd_mod hP5 hm
    rw [hz]
    show (1 + 5 ^ (α' + 1)) % 5 = 1
    rw [h3a, Nat.add_mul_mod_self_left]
  obtain ⟨δ, hδ⟩ := four_dvd_of_mod5 hm5
  have hcop45 : Nat.Coprime (5 ^ (α' + 1)) 4 := Nat.Coprime.pow_left _ (by decide)
  have hdδ : 5 ^ (α' + 1) ∣ δ :=
    Nat.Coprime.dvd_of_dvd_mul_left hcop45 (by rw [← hδ]; exact hdm)
  have hL : 16 ^ δ % 5 ^ (α' + 2) = 1 := sixteen_pow_mod_eq_one_iff.2 hdδ
  have e4' : 16 ^ δ = 2 ^ m := by rw [hδ, Nat.pow_mul]
  have hR : 16 ^ δ % 5 ^ (α' + 2) = (1 + 5 ^ (α' + 1)) % 5 ^ (α' + 2) := by
    rw [e4']; exact mod_of_dvd_mod hZi2 hm
  have hcomb : (1 + 5 ^ (α' + 1)) % 5 ^ (α' + 2) = 1 := hR.symm.trans hL
  have hlt : 1 + 5 ^ (α' + 1) < 5 ^ (α' + 2) := by
    have h2p := one_lt_pow5 α'
    have he52 : 5 ^ (α' + 2) = 5 * 5 ^ (α' + 1) := by rw [Nat.pow_succ]; grind
    omega
  have hfin : (1 + 5 ^ (α' + 1)) % 5 ^ (α' + 2) = 1 + 5 ^ (α' + 1) := Nat.mod_eq_of_lt hlt
  rw [hfin] at hcomb
  have hpos : (0:Nat) < 5 ^ (α' + 1) := Nat.pow_pos (by omega)
  omega

def SameMod (n a b : Nat) : Prop := a % n = b % n

inductive Closure (Q w : Nat) : Nat → Prop
  | base (k x : Nat) : SameMod Q x (2 ^ k * w) → Closure Q w x
  | dbl {z : Nat} : Closure Q w z → Closure Q w (2 * z)
  | undo {z x : Nat} : Closure Q w z → SameMod Q (5 * x + 1) (2 * z) → Closure Q w x
  | cong {z x : Nat} : Closure Q w z → SameMod Q x z → Closure Q w x

section Fibres
variable (M : Nat) [NeZero M] (K w : Nat)

def Fibre (a : Nat) (t : Fin M) : Prop :=
  ∃ x, Closure (5 ^ (K + 1) * M) w x ∧ x % 5 ^ (K + 1) = a % 5 ^ (K + 1) ∧ residue M x = t

theorem fibre_mod (a : Nat) : Fibre M K w a = Fibre M K w (a % 5 ^ (K + 1)) := by
  funext t; unfold Fibre; rw [Nat.mod_mod]

theorem fibre_dbl {a : Nat} {t : Fin M} (h : Fibre M K w a t) : Fibre M K w (2 * a) (2 * t) := by
  obtain ⟨x, hx, hxa, rfl⟩ := h
  refine ⟨2 * x, Closure.dbl hx, ?_, ?_⟩
  · rw [Nat.mul_mod, hxa, ← Nat.mul_mod]
  · rw [residue_mul, residue_two]

theorem two_mul_inj [TwoFiveInvertible M] (s t : Fin M) (h : (2 : Fin M) * s = 2 * t) : s = t := by
  have h2 := two_mul_unitInv M
  exact cancel_invertible M (u := 2) (v := unitInv M 2) (by grind) h

theorem fibre_cardinality_dbl_le [TwoFiveInvertible M] (a : Nat) : cardinality (Fibre M K w a) ≤ cardinality (Fibre M K w (2 * a)) :=
  cardinality_le_of_inj (fun t => 2 * t) (two_mul_inj M) (fun _ ht => fibre_dbl M K w ht)

theorem fibre_cardinality_pow_le [TwoFiveInvertible M] (a : Nat) :
    ∀ m, cardinality (Fibre M K w a) ≤ cardinality (Fibre M K w (2 ^ m * a))
  | 0 => by simp
  | m + 1 => by
    have h := fibre_cardinality_dbl_le M K w (2 ^ m * a)
    rw [show 2 * (2 ^ m * a) = 2 ^ (m + 1) * a by rw [Nat.pow_succ]; grind] at h
    exact Nat.le_trans (fibre_cardinality_pow_le a m) h

theorem fibre_cardinality_le_live [TwoFiveInvertible M] {a b : Nat} (ha : a % 5 ≠ 0) (hb : b % 5 ≠ 0) :
    cardinality (Fibre M K w a) ≤ cardinality (Fibre M K w b) := by
  have h5 : 5 ∣ 5 ^ (K + 1) := five_dvd_pow K
  have hb' : (b % 5 ^ (K + 1)) % 5 ≠ 0 := by rw [Nat.mod_mod_of_dvd b h5]; exact hb
  obtain ⟨j, hj⟩ := two_generates_live (K := K) ha hb' (Nat.mod_lt _ (Nat.pow_pos (by omega)))
  have h := fibre_cardinality_pow_le M K w a j
  rw [fibre_mod M K w (2 ^ j * a), hj, ← fibre_mod] at h
  exact h

theorem fibre_cardinality_const [TwoFiveInvertible M] {a b : Nat} (ha : a % 5 ≠ 0) (hb : b % 5 ≠ 0) :
    cardinality (Fibre M K w a) = cardinality (Fibre M K w b) :=
  Nat.le_antisymm (fibre_cardinality_le_live M K w ha hb) (fibre_cardinality_le_live M K w hb ha)

theorem fibre_dbl_iff [TwoFiveInvertible M] {a : Nat} (ha : a % 5 ≠ 0) (t : Fin M) :
    Fibre M K w (2 * a) t ↔ ∃ s, Fibre M K w a s ∧ t = 2 * s := by
  constructor
  · intro ht
    have h2a : (2 * a) % 5 ≠ 0 := by omega
    have hc : cardinality (Fibre M K w (2 * a)) ≤ cardinality (fun t => ∃ s, Fibre M K w a s ∧ t = 2 * s) := by
      rw [fibre_cardinality_const M K w h2a ha]
      exact cardinality_le_of_inj (fun s => 2 * s) (two_mul_inj M) (fun s hs => ⟨s, hs, rfl⟩)
    exact cardinality_eq_of_sub (S := fun t => ∃ s, Fibre M K w a s ∧ t = 2 * s)
      (fun t ⟨s, hs, hts⟩ => hts ▸ fibre_dbl M K w hs) hc t ht
  · rintro ⟨s, hs, rfl⟩; exact fibre_dbl M K w hs

theorem fibre_undo_iff [TwoFiveInvertible M] (hM : Nat.Coprime M 10) {g a' : Nat} (hg : g % 5 ≠ 0) (ha : a' % 5 ≠ 0)
    (h3 : (5 * a' + 1) % 5 ^ (K + 1) = (2 * g) % 5 ^ (K + 1)) (s : Fin M) :
    Fibre M K w a' s ↔ ∃ t, Fibre M K w g t ∧ 5 * s + 1 = 2 * t := by
  have back : ∀ s : Fin M, (∃ t, Fibre M K w g t ∧ 5 * s + 1 = 2 * t) → Fibre M K w a' s := by
    rintro s ⟨t, ⟨x, hx, hxg, rfl⟩, hst⟩
    have hcop : Nat.Coprime M (5 ^ (K + 1)) :=
      Nat.Coprime.pow_right _ (Nat.Coprime.coprime_dvd_right (by decide) hM)
    obtain ⟨y, hy3, hyM⟩ := crt_exists hcop a' s.val
    refine ⟨y, Closure.undo hx ?_, hy3, ?_⟩
    · unfold SameMod
      apply mod_combine (Nat.Coprime.symm hcop)
      · rw [Nat.add_mod, Nat.mul_mod, hy3, ← Nat.mul_mod, ← Nat.add_mod, h3,
          Nat.mul_mod, ← hxg, ← Nat.mul_mod]
      · have hys : residue M y = s := by rw [← residue_self_val s, residue_eq_iff]; exact hyM
        rw [← residue_eq_iff, residue_add, residue_mul, residue_mul, residue_five, residue_one, residue_two, hys, hst]
    · rw [← residue_self_val s, residue_eq_iff]; exact hyM
  constructor
  · intro hs
    have h3i := five_mul_unitInv M
    let φ : Fin M → Fin M := fun t => unitInv M 5 * (2 * t - 1)
    have hφ : ∀ t, 5 * φ t + 1 = 2 * t := by intro t; simp only [φ]; grind
    have hinj : ∀ t t', φ t = φ t' → t = t' := by
      intro t t' h
      apply two_mul_inj M
      have := congrArg (fun z => 5 * z + 1) h
      simp only [hφ] at this; exact this
    have hc : cardinality (Fibre M K w a') ≤ cardinality (fun s => ∃ t, Fibre M K w g t ∧ 5 * s + 1 = 2 * t) := by
      rw [fibre_cardinality_const M K w ha hg]
      exact cardinality_le_of_inj φ hinj (fun t ht => ⟨t, ht, hφ t⟩)
    exact cardinality_eq_of_sub (S := fun s => ∃ t, Fibre M K w g t ∧ 5 * s + 1 = 2 * t) back hc s hs
  · exact back s

def Stabilizer (h : Fin M → Fin M) : Prop := ∀ t, Fibre M K w 1 t ↔ Fibre M K w 1 (h t)

theorem stabilizer_comp {h1 h2 : Fin M → Fin M} (a : Stabilizer M K w h1) (b : Stabilizer M K w h2) :
    Stabilizer M K w (fun t => h2 (h1 t)) := fun t => (a t).trans (b (h1 t))

theorem stabilizer_inv {h h' : Fin M → Fin M} (a : Stabilizer M K w h) (hh : ∀ t, h (h' t) = t) :
    Stabilizer M K w h' := fun t => by have := a (h' t); rw [hh] at this; exact this.symm

theorem stabilizer_ext {h h' : Fin M → Fin M} (a : Stabilizer M K w h) (hh : ∀ t, h t = h' t) :
    Stabilizer M K w h' := fun t => by rw [← hh]; exact a t

theorem twoPow_invertible (hM : Nat.Coprime M 10) (m : Nat) : IsInvertible M (residue M (2 ^ m)) :=
  exists_inv_residue (2 ^ m) (Nat.Coprime.pow_right m (Nat.Coprime.coprime_dvd_right (by decide) hM))

theorem fibre_pow [TwoFiveInvertible M] : ∀ m (t : Fin M),
    Fibre M K w (2 ^ m) t ↔ ∃ s, Fibre M K w 1 s ∧ t = residue M (2 ^ m) * s
  | 0, t => by
    simp only [Nat.pow_zero, residue_one]
    exact ⟨fun h => ⟨t, h, by grind⟩, fun ⟨s, hs, hst⟩ => by rw [hst]; grind⟩
  | m + 1, t => by
    have hl : (2 ^ m) % 5 ≠ 0 := two_pow_mod_five_ne m
    rw [show 2 ^ (m + 1) = 2 * 2 ^ m by rw [Nat.pow_succ]; grind, fibre_dbl_iff M K w hl]
    constructor
    · rintro ⟨s', hs', rfl⟩
      obtain ⟨s, hs, rfl⟩ := (fibre_pow m s').1 hs'
      exact ⟨s, hs, by rw [residue_mul, residue_two]; grind⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨residue M (2 ^ m) * s, (fibre_pow m _).2 ⟨s, hs, rfl⟩, by rw [residue_mul, residue_two]; grind⟩

theorem fibre_live [TwoFiveInvertible M] {a m : Nat} (ham : (2 ^ m) % 5 ^ (K + 1) = a % 5 ^ (K + 1)) (t : Fin M) :
    Fibre M K w a t ↔ ∃ s, Fibre M K w 1 s ∧ t = residue M (2 ^ m) * s := by
  rw [fibre_mod M K w a, ← ham, ← fibre_mod]; exact fibre_pow M K w m t

theorem stabilizer_loop [TwoFiveInvertible M] (hM : Nat.Coprime M 10) {g a' i m : Nat} (hg : g % 5 ≠ 0)
    (ha : a' % 5 ≠ 0) (h3 : (5 * a' + 1) % 5 ^ (K + 1) = (2 * g) % 5 ^ (K + 1))
    (hi : (2 ^ i) % 5 ^ (K + 1) = g % 5 ^ (K + 1)) (hm : (2 ^ m) % 5 ^ (K + 1) = a' % 5 ^ (K + 1)) :
    Stabilizer M K w (fun t => unitInv M (residue M (2 ^ m)) * (unitInv M 5 * (2 * (residue M (2 ^ i) * t) - 1))) := by
  have hv := five_mul_unitInv M
  have hu := mul_unitInv M (twoPow_invertible M hM m)
  have hP := mul_unitInv M (twoPow_invertible M hM i)
  intro t
  constructor
  · intro ht
    have hgt : Fibre M K w g (residue M (2 ^ i) * t) := (fibre_live M K w hi _).2 ⟨t, ht, rfl⟩
    have has : Fibre M K w a' (unitInv M 5 * (2 * (residue M (2 ^ i) * t) - 1)) :=
      (fibre_undo_iff M K w hM hg ha h3 _).2 ⟨_, hgt, by grind⟩
    obtain ⟨s', hs', hss⟩ := (fibre_live M K w hm _).1 has
    show Fibre M K w 1 (unitInv M (residue M (2 ^ m)) * (unitInv M 5 * (2 * (residue M (2 ^ i) * t) - 1)))
    rw [hss]
    have : unitInv M (residue M (2 ^ m)) * (residue M (2 ^ m) * s') = s' := by grind
    rw [this]; exact hs'
  · intro ht
    have has : Fibre M K w a' (unitInv M 5 * (2 * (residue M (2 ^ i) * t) - 1)) :=
      (fibre_live M K w hm _).2 ⟨_, ht, by grind⟩
    obtain ⟨t', ht', hst⟩ := (fibre_undo_iff M K w hM hg ha h3 _).1 has
    have htt : t' = residue M (2 ^ i) * t := by
      apply two_mul_inj M; rw [← hst]; grind
    rw [htt] at ht'
    obtain ⟨s, hs, hts⟩ := (fibre_live M K w hi _).1 ht'
    have : t = s := cancel_invertible M (u := residue M (2 ^ i)) hP hts
    rw [this]; exact hs

theorem stabilizer_mul [TwoFiveInvertible M] (hM : Nat.Coprime M 10) {m : Nat} (hm : (2 ^ m) % 5 ^ (K + 1) = 1 % 5 ^ (K + 1)) :
    Stabilizer M K w (fun t => residue M (2 ^ m) * t) := by
  have hP := mul_unitInv M (twoPow_invertible M hM m)
  intro t
  constructor
  · intro ht; exact (fibre_live M K w hm _).2 ⟨t, ht, rfl⟩
  · intro ht
    obtain ⟨s, hs, hts⟩ := (fibre_live M K w hm _).1 ht
    rw [cancel_invertible M hP hts]; exact hs

theorem stabilizer_special_loop [TwoFiveInvertible M] (hM : Nat.Coprime M 10) (i₀ : Nat)
    (hi₀ : 2 ^ i₀ % 5 ^ (K + 1) = 3 % 5 ^ (K + 1)) :
    Stabilizer M K w (fun t => unitInv M 5 * (2 * (residue M (2 ^ i₀) * t) - 1)) := by
  have h := stabilizer_loop M K w hM (g := 3) (a' := 1) (i := i₀) (m := 0) (by decide) (by decide)
    (by rfl) hi₀ rfl
  apply stabilizer_ext M K w h
  intro t
  have h1 : unitInv M (residue M (2 ^ 0)) = 1 := unitInv_eq_of_mul M (by rw [Nat.pow_zero, residue_one]; grind)
  rw [h1]; grind

theorem stabilizer_affine_translation [TwoFiveInvertible M] (hM : Nat.Coprime M 10) (i₀ : Nat)
    (hi₀ : 2 ^ i₀ % 5 ^ (K + 1) = 3 % 5 ^ (K + 1)) {lam μ : Fin M} (hl : IsInvertible M lam)
    (hk : Stabilizer M K w (fun t => lam * t + μ)) :
    Stabilizer M K w
      (fun t => t + (μ + unitInv M 5 - unitInv M 5 * (2 * residue M (2 ^ i₀)) * μ
        - lam * unitInv M 5)) := by
  have hv := five_mul_unitInv M
  have h2 := two_mul_unitInv M
  have hli := mul_unitInv M hl
  have hℓ := stabilizer_special_loop M K w hM i₀ hi₀
  have hc₀i : IsInvertible M (unitInv M 5 * (2 * residue M (2 ^ i₀))) :=
    isInvertible_mul M (isInvertible_unitInv M TwoFiveInvertible.five)
      (isInvertible_mul M TwoFiveInvertible.two (twoPow_invertible M hM i₀))
  have hℓv := mul_unitInv M hc₀i
  have hℓi : Stabilizer M K w
      (fun t => unitInv M (unitInv M 5 * (2 * residue M (2 ^ i₀))) * (t + unitInv M 5)) :=
    stabilizer_inv M K w hℓ (fun t => by grind)
  have hki : Stabilizer M K w (fun t => unitInv M lam * (t - μ)) :=
    stabilizer_inv M K w hk (fun t => by grind)
  have hc := stabilizer_comp M K w (stabilizer_comp M K w (stabilizer_comp M K w hℓi hki) hℓ) hk
  exact stabilizer_ext M K w hc (fun t => by grind)

omit [NeZero M] in
theorem exists_of_cardinality_pos {S : Fin M → Prop} (h : 1 ≤ cardinality S) : ∃ t, S t := by
  classical
  unfold cardinality at h
  obtain ⟨t, ht⟩ := List.exists_mem_of_length_pos h
  exact ⟨t, (mem_cardlist).1 ht⟩

def IsTranslationPeriod (d : Nat) : Prop := Stabilizer M K w (fun t => t + residue M d)

theorem translationPeriod_of_eq {d : Nat} (h : residue M d = 0) : IsTranslationPeriod M K w d :=
  stabilizer_ext M K w (h := fun t => t) (fun _ => Iff.rfl) (fun t => by rw [h]; grind)

theorem translationPeriod_add {a b : Nat} (ha : IsTranslationPeriod M K w a) (hb : IsTranslationPeriod M K w b) : IsTranslationPeriod M K w (a + b) :=
  stabilizer_ext M K w (stabilizer_comp M K w ha hb) (fun t => by rw [residue_add]; grind)

theorem translationPeriod_mul {a : Nat} (ha : IsTranslationPeriod M K w a) : ∀ n, IsTranslationPeriod M K w (a * n)
  | 0 => translationPeriod_of_eq M K w (by rw [Nat.mul_zero]; rfl)
  | n + 1 => by rw [Nat.mul_succ]; exact translationPeriod_add M K w (translationPeriod_mul ha n) ha

theorem translationPeriod_sub {a b : Nat} (ha : IsTranslationPeriod M K w a) (hb : IsTranslationPeriod M K w b) (hle : b ≤ a) :
    IsTranslationPeriod M K w (a - b) := by
  have hbi : Stabilizer M K w (fun t => t - residue M b) := stabilizer_inv M K w hb (fun t => by grind)
  have hab : residue M a = residue M (a - b) + residue M b := by rw [← residue_add, Nat.sub_add_cancel hle]
  exact stabilizer_ext M K w (stabilizer_comp M K w ha hbi) (fun t => by rw [hab]; grind)

theorem mod_of_dvd_sub {q X Y : Nat} (hqM : q ∣ M) (h : q ∣ (residue M X - residue M Y).val) : X % q = Y % q := by
  rw [Fin.sub_def, residue_val, residue_val] at h
  have h1 : q ∣ (M - Y % M) + X % M := by
    have := (Nat.dvd_mod_iff hqM).1 h; rw [Nat.add_comm (M - Y % M)] at this ⊢; exact this
  have hlt : Y % M < M := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne M))
  have h2 : q ∣ (M - Y % M) + Y % M := by rw [Nat.sub_add_cancel (Nat.le_of_lt hlt)]; exact hqM
  have h3 := mod_add_left_cancel (m := q) (e := M - Y % M) (X := X % M) (Y := Y % M)
    (by rw [Nat.eq_zero_of_dvd_of_lt (by exact Nat.dvd_mod_iff (Nat.dvd_refl q) |>.2 h1) (Nat.mod_lt _ (Nat.pos_of_dvd_of_pos hqM (Nat.pos_of_ne_zero (NeZero.ne M)))) ,
        Nat.eq_zero_of_dvd_of_lt (by exact Nat.dvd_mod_iff (Nat.dvd_refl q) |>.2 h2) (Nat.mod_lt _ (Nat.pos_of_dvd_of_pos hqM (Nat.pos_of_ne_zero (NeZero.ne M))))])
  rwa [Nat.mod_mod_of_dvd X hqM, Nat.mod_mod_of_dvd Y hqM] at h3

omit [NeZero M] in
theorem dvd_val_mul {q : Nat} (hqM : q ∣ M) (c z : Fin M) (h : q ∣ z.val) : q ∣ (c * z).val := by
  rw [Fin.val_mul]; exact (Nat.dvd_mod_iff hqM).2 (Nat.dvd_mul_left_of_dvd h _)

theorem translationPeriod_one [TwoFiveInvertible M] (hM : Nat.Coprime M 10) : IsTranslationPeriod M K w 1 := by
  have hM10 : Nat.Coprime M 10 := hM
  obtain ⟨q, ⟨hq0, hqP⟩, hmin⟩ := exists_least (fun n => 0 < n ∧ IsTranslationPeriod M K w n)
    ⟨M, Nat.pos_of_ne_zero (NeZero.ne M), translationPeriod_of_eq M K w (residue_self M)⟩
  have hiff : ∀ d, IsTranslationPeriod M K w d → q ∣ d := by
    intro d hd
    have hm := translationPeriod_sub M K w hd (translationPeriod_mul M K w hqP (d / q)) (Nat.mul_div_le d q)
    rw [show d - q * (d / q) = d % q by have := Nat.div_add_mod d q; omega] at hm
    apply Nat.dvd_of_mod_eq_zero
    apply Classical.byContradiction
    intro hne
    exact hmin (d % q) (Nat.mod_lt _ hq0) ⟨by omega, hm⟩
  have hqM : q ∣ M := hiff M (translationPeriod_of_eq M K w (residue_self M))
  have hval : ∀ z : Fin M, Stabilizer M K w (fun t => t + z) → q ∣ z.val := by
    intro z hz; apply hiff; unfold IsTranslationPeriod; rw [residue_val_self]; exact hz
  rcases Nat.lt_or_ge 1 q with hq1 | hq1
  · exfalso
    haveI : NeZero q := ⟨by omega⟩
    have hq : Nat.Coprime q 5 := Nat.Coprime.coprime_dvd_right (by decide) (Nat.Coprime.coprime_dvd_left hqM hM)
    have hv := five_mul_unitInv M
    have hP5 : 5 ∣ 5 ^ (K + 1) := five_dvd_pow K
    obtain ⟨i₀, hi₀⟩ := two_generates_live (K := K) (c := 1) (d := 3 % 5 ^ (K + 1)) (by decide)
      (by rw [Nat.mod_mod_of_dvd 3 hP5]; decide) (Nat.mod_lt _ (Nat.pow_pos (by omega)))
    rw [Nat.mul_one] at hi₀
    have hA : IsSixteenPeriod q (5 ^ K) := by
      have hm : 2 ^ (4 * 5 ^ K) % 5 ^ (K + 1) = 1 % 5 ^ (K + 1) := by
        rw [two_pow_mod_eq_one_iff.2 (Nat.dvd_refl _), Nat.mod_eq_of_lt (one_lt_pow5 K)]
      have hs := stabilizer_mul M K w hM10 hm
      have hs' : Stabilizer M K w (fun t => residue M (2 ^ (4 * 5 ^ K)) * t + 0) :=
        stabilizer_ext M K w hs (fun t => by grind)
      have ht := hval _ (stabilizer_affine_translation M K w hM10 i₀ hi₀
        (twoPow_invertible M hM10 _) hs')
      have hc := dvd_val_mul M hqM (residue M 5) _ ht
      have e : residue M 5 * ((0 : Fin M) + unitInv M 5 - unitInv M 5 * (2 * residue M (2 ^ i₀)) * 0
          - residue M (2 ^ (4 * 5 ^ K)) * unitInv M 5)
          = residue M 1 - residue M (2 ^ (4 * 5 ^ K)) := hA_id M _ _ _ hv
      rw [e] at hc
      have hz := mod_of_dvd_sub M (X := 1) (Y := 2 ^ (4 * 5 ^ K)) hqM hc
      have ep : 2 ^ (4 * 5 ^ K) = 16 ^ (5 ^ K) := by rw [Nat.pow_mul]
      rw [ep] at hz; exact (isSixteenPeriod_iff q (5 ^ K)).2 hz.symm
    have hB : ∀ g a' i m : Nat, g % 5 ≠ 0 → a' % 5 ≠ 0 →
        (5 * a' + 1) % 5 ^ (K + 1) = (2 * g) % 5 ^ (K + 1) →
        2 ^ i % 5 ^ (K + 1) = g % 5 ^ (K + 1) → 2 ^ m % 5 ^ (K + 1) = a' % 5 ^ (K + 1) →
        (5 * 2 ^ m + 2 * 2 ^ i₀) % q = (5 + 2 * 2 ^ i) % q := by
      intro g a' i m hg ha h3 hi hm
      have hu := mul_unitInv M (twoPow_invertible M hM10 m)
      have hs := stabilizer_loop M K w hM10 hg ha h3 hi hm
      let u := unitInv M (residue M (2 ^ m))
      let lam := u * unitInv M 5 * 2 * residue M (2 ^ i)
      let μ := - (u * unitInv M 5)
      have hs' : Stabilizer M K w (fun t => lam * t + μ) :=
        stabilizer_ext M K w hs (fun t => by simp only [lam, μ, u]; grind)
      have hl : IsInvertible M lam := by
        refine isInvertible_mul M (isInvertible_mul M (isInvertible_mul M
          (isInvertible_unitInv M (twoPow_invertible M hM10 m)) ?_) ?_) (twoPow_invertible M hM10 i)
        · exact isInvertible_unitInv M TwoFiveInvertible.five
        · exact TwoFiveInvertible.two
      have ht := hval _ (stabilizer_affine_translation M K w hM10 i₀ hi₀ hl hs')
      have hc1 := dvd_val_mul M hqM (residue M (5 * 2 ^ m)) _ ht
      have hc2 := dvd_val_mul M hqM (residue M 5) _ hc1
      apply mod_of_dvd_sub M hqM
      have e : residue M 5 * (residue M (5 * 2 ^ m) * (μ + unitInv M 5
          - unitInv M 5 * (2 * residue M (2 ^ i₀)) * μ - lam * unitInv M 5))
          = residue M (5 * 2 ^ m + 2 * 2 ^ i₀) - residue M (5 + 2 * 2 ^ i) :=
        hB_id M m i i₀ u hu hv
      rw [← e]; exact hc2
    exact period_contra q K i₀ hq1 hq hi₀ hA hB
  · have : q = 1 := by omega
    subst this
    exact translationPeriod_mul M K w hqP 1 |> fun h => by simpa using h

theorem fibre_one_full [TwoFiveInvertible M] (hM : Nat.Coprime M 10) (hw : w % 5 ≠ 0) (t : Fin M) : Fibre M K w 1 t := by
  have hw0 : Fibre M K w w (residue M w) :=
    ⟨w, Closure.base 0 w (by unfold SameMod; rw [Nat.pow_zero, Nat.one_mul]), rfl, rfl⟩
  have hc : 1 ≤ cardinality (Fibre M K w 1) := by
    rw [fibre_cardinality_const M K w (by decide) hw]; exact cardinality_pos hw0
  obtain ⟨t0, ht0⟩ := exists_of_cardinality_pos M hc
  have hp : IsTranslationPeriod M K w (t - t0).val := by
    have := translationPeriod_mul M K w (translationPeriod_one M K w hM) (t - t0).val; rwa [Nat.one_mul] at this
  have := (hp t0).1 ht0
  change Fibre M K w 1 (t0 + residue M (t - t0).val) at this
  rw [residue_val_self] at this
  have e : t0 + (t - t0) = t := by grind
  rw [e] at this; exact this

theorem fibre_full_live [TwoFiveInvertible M] (hM : Nat.Coprime M 10) (hw : w % 5 ≠ 0) {a : Nat} (ha : a % 5 ≠ 0)
    (t : Fin M) : Fibre M K w a t := by
  obtain ⟨m, hm⟩ := two_generates_live (K := K) (c := 1) (d := a % 5 ^ (K + 1)) (by decide)
    (by rw [Nat.mod_mod_of_dvd a (five_dvd_pow K)]; exact ha) (Nat.mod_lt _ (Nat.pow_pos (by omega)))
  rw [Nat.mul_one] at hm
  have hM10 : Nat.Coprime M 10 := hM
  have hu := mul_unitInv M (twoPow_invertible M hM10 m)
  exact (fibre_live M K w (m := m) hm t).2
    ⟨unitInv M (residue M (2 ^ m)) * t, fibre_one_full M K w hM hw _, by grind⟩

theorem fibre_full [TwoFiveInvertible M] (hM : Nat.Coprime M 10) (hw : w % 5 ≠ 0) (a : Nat) (t : Fin M) :
    Fibre M K w a t := by
  by_cases ha : a % 5 ≠ 0
  · exact fibre_full_live M K w hM hw ha t
  have hP3 : 5 ^ (K + 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd (five_dvd_pow K)
  obtain ⟨h2, hh2⟩ : ∃ h2, 2 * h2 = 5 ^ (K + 1) + 1 := ⟨(5 ^ (K + 1) + 1) / 2, by
    have := five_pow_odd (K + 1); omega⟩
  have hh23 : h2 % 5 = 3 := by omega
  let g := (5 * a + 1) * h2
  have hg : g % 5 ≠ 0 := by
    show ((5 * a + 1) * h2) % 5 ≠ 0
    rw [show (5 * a + 1) * h2 = h2 + 5 * (a * h2) by grind, Nat.add_mul_mod_self_left]; omega
  have h2g : (2 * g) % 5 ^ (K + 1) = (5 * a + 1) % 5 ^ (K + 1) := by
    show (2 * ((5 * a + 1) * h2)) % _ = _
    rw [show 2 * ((5 * a + 1) * h2) = (5 * a + 1) + (5 * a + 1) * 5 ^ (K + 1) by
      rw [show 2 * ((5 * a + 1) * h2) = (5 * a + 1) * (2 * h2) by grind, hh2]; grind,
      Nat.add_mul_mod_self_right]
  have h2i := two_mul_unitInv M
  obtain ⟨y, hy, hyg, hyt⟩ := fibre_full_live M K w hM hw hg (unitInv M 2 * (5 * t + 1))
  have hcop : Nat.Coprime M (5 ^ (K + 1)) :=
    Nat.Coprime.pow_right _ (Nat.Coprime.coprime_dvd_right (by decide) hM)
  obtain ⟨x, hx3, hxM⟩ := crt_exists hcop a t.val
  have hxt : residue M x = t := by rw [← residue_self_val t, residue_eq_iff]; exact hxM
  refine ⟨x, Closure.undo hy ?_, hx3, hxt⟩
  unfold SameMod
  apply mod_combine (Nat.Coprime.symm hcop)
  · rw [Nat.add_mod, Nat.mul_mod, hx3, ← Nat.mul_mod, ← Nat.add_mod, ← h2g,
      Nat.mul_mod, ← hyg, ← Nat.mul_mod]
  · rw [← residue_eq_iff, residue_add, residue_mul, residue_mul, residue_five, residue_one, residue_two, hxt, hyt]; grind

theorem closure_all (hM : Nat.Coprime M 10) (hw : w % 5 ≠ 0) (x : Nat) : Closure (5 ^ (K + 1) * M) w x := by
  have hM10 : Nat.Coprime M 10 := hM
  haveI : TwoFiveInvertible M := twoFiveInvertible_of_coprime10 hM10
  obtain ⟨x', hx', h1, h2⟩ := fibre_full M K w hM hw x (residue M x)
  apply Closure.cong hx'
  unfold SameMod
  have hcop : Nat.Coprime (5 ^ (K + 1)) M :=
    Nat.Coprime.symm (Nat.Coprime.pow_right _ (Nat.Coprime.coprime_dvd_right (by decide) hM))
  exact mod_combine hcop h1.symm ((residue_eq_iff M x x').1 h2.symm)

end Fibres

theorem exponent_class (M K j w Z k' D' B : Nat) (hM : Nat.Coprime M 10) (hw : w % 5 ≠ 0)
    (hD3 : D' % 5 ≠ 0) (hD : 2 ^ (5 ^ K * D') % M = 1 % M)
    (hZ : Z % (5 ^ (K + 1) * M) = (2 ^ k' * w) % (5 ^ (K + 1) * M)) :
    ∃ k, B ≤ k ∧
      k ≤ 4 * 5 ^ (K + j) * (k' + 1) + 4 * 5 ^ (K + j) * (D' * D' * (4 * 5 ^ (K + j) * (k' + 1))
        + 5 ^ K * D' * B) ∧
      Z % (5 ^ (K + j + 1) * M) = (2 ^ k * w) % (5 ^ (K + j + 1) * M) := by
  have hM3 : Nat.Coprime 5 M := Nat.Coprime.symm (Nat.Coprime.coprime_dvd_right (by decide) hM)
  have hP1 : 5 ^ (K + 1) ∣ 5 ^ (K + j + 1) := Nat.pow_dvd_pow 5 (by omega)
  have hZ3 : Z % 5 ^ (K + 1) = (2 ^ k' * w) % 5 ^ (K + 1) :=
    mod_of_dvd_mod (Nat.dvd_mul_right _ _) hZ
  have hZM : Z % M = (2 ^ k' * w) % M := mod_of_dvd_mod (Nat.dvd_mul_left _ _) hZ
  have hZl : Z % 5 ≠ 0 := by
    rw [mod_of_dvd_mod (five_dvd_pow K) hZ3]; exact live_mul5 (two_pow_mod_five_ne k') hw
  obtain ⟨j00, hj00⟩ := two_generates_live (K := K + j) (c := w) (d := Z % 5 ^ (K + j + 1)) hw
    (by rw [Nat.mod_mod_of_dvd Z (five_dvd_pow (K + j))]; exact hZl)
    (Nat.mod_lt _ (Nat.pow_pos (by omega)))
  let T := 4 * 5 ^ (K + j)
  have hT : 2 ^ T % 5 ^ (K + j + 1) = 1 % 5 ^ (K + j + 1) := by
    rw [two_pow_mod_eq_one_iff.2 (Nat.dvd_refl _), Nat.mod_eq_of_lt (one_lt_pow5 (K + j))]
  have hTpos : 0 < T := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  obtain ⟨j0, hj0lt, hj0⟩ : ∃ j0, j0 < T ∧ (2 ^ j0 * w) % 5 ^ (K + j + 1) = Z % 5 ^ (K + j + 1) := by
    refine ⟨j00 % T, Nat.mod_lt _ hTpos, ?_⟩
    have h1 : 2 ^ j00 % 5 ^ (K + j + 1) = 2 ^ (j00 % T) % 5 ^ (K + j + 1) := by
      have e : j00 = j00 % T + T * (j00 / T) := (Nat.mod_add_div j00 T).symm
      have := pow_mod_period hT (j00 % T) (j00 / T)
      rw [← e] at this; exact this
    rw [Nat.mul_mod, ← h1, ← Nat.mul_mod]; exact hj00
  let k2 := j0 + T * k'
  have hk2P : (2 ^ k2 * w) % 5 ^ (K + j + 1) = Z % 5 ^ (K + j + 1) := by
    rw [Nat.mul_mod, pow_mod_period hT j0 k', ← Nat.mul_mod, hj0]
  have hk2k : k' ≤ k2 := by
    have : 1 ≤ T := by have := Nat.pow_pos (n := K + j) (by omega : 0 < 5); omega
    have := Nat.le_mul_of_pos_left k' this; omega
  have hcw : Nat.Coprime (5 ^ (K + 1)) w := Nat.Coprime.pow_left _ (coprime5 hw)
  have h22 : 2 ^ k2 % 5 ^ (K + 1) = 2 ^ k' % 5 ^ (K + 1) :=
    mod_cancel_mul_right hcw (by rw [mod_of_dvd_mod hP1 hk2P, hZ3])
  obtain ⟨r, hr⟩ : 4 * 5 ^ K ∣ k2 - k' := by
    apply two_pow_mod_eq_one_iff.1
    have hc2 : Nat.Coprime (5 ^ (K + 1)) (2 ^ k') := Nat.Coprime.pow _ _ (by decide)
    have := mod_cancel_mul_right (x := 2 ^ (k2 - k')) (y := 1) hc2
      (by rw [← Nat.pow_add, Nat.sub_add_cancel hk2k, Nat.one_mul, h22])
    rw [this, Nat.mod_eq_of_lt (one_lt_pow5 K)]
  haveI : NeZero D' := ⟨by omega⟩
  have hD'3j : Nat.Coprime D' (5 ^ j) := Nat.Coprime.pow_right _ (Nat.Coprime.symm (coprime5 hD3))
  obtain ⟨v, hv⟩ := exists_inv_residue (M := D') (5 ^ j) hD'3j
  let s := v.val * (D' - 1) * r
  obtain ⟨n0, hn0⟩ : D' ∣ r + 5 ^ j * s := by
    apply Nat.dvd_of_mod_eq_zero
    have hn1 : residue D' (D' - 1) + 1 = 0 := by
      rw [← residue_one D', ← residue_add]
      apply Fin.ext; rw [residue_val, show D' - 1 + 1 = D' by omega, Nat.mod_self]; rfl
    have : residue D' (r + 5 ^ j * s) = 0 := by
      show residue D' (r + 5 ^ j * (v.val * (D' - 1) * r)) = 0
      rw [residue_add, residue_mul, residue_mul, residue_mul, residue_self_val]
      grind
    have h0 := (residue_eq_iff D' _ 0).1 (by rw [this]; rfl)
    rwa [Nat.zero_mod] at h0
  have hk2lt : k2 < T * (k' + 1) := by
    have e : T * (k' + 1) = T * k' + T := by grind
    show j0 + T * k' < _
    omega
  have hrle : r ≤ k2 := by
    have h1 : 0 < 4 * 5 ^ K := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
    have h2 := Nat.le_mul_of_pos_left r h1
    omega
  have hsle : s ≤ D' * D' * (T * (k' + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_of_lt v.isLt) (Nat.sub_le D' 1))
      (Nat.le_trans hrle (Nat.le_of_lt hk2lt))
  refine ⟨k2 + T * (s + 5 ^ K * D' * B), ?_, ?_, ?_⟩
  · have : 1 ≤ T * (5 ^ K * D') := by
      have h1 := Nat.pow_pos (n := K + j) (by omega : 0 < 5)
      have h2 := Nat.pow_pos (n := K) (by omega : 0 < 5)
      have : 1 ≤ D' := by omega
      exact Nat.mul_pos (by omega) (Nat.mul_pos h2 (by omega))
    calc B ≤ T * (5 ^ K * D') * B := Nat.le_mul_of_pos_left B this
      _ = T * (5 ^ K * D' * B) := by rw [Nat.mul_assoc T]
      _ ≤ T * (s + 5 ^ K * D' * B) := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
      _ ≤ k2 + T * (s + 5 ^ K * D' * B) := Nat.le_add_left _ _
  · exact Nat.add_le_add (Nat.le_of_lt hk2lt)
      (Nat.mul_le_mul_left T (Nat.add_le_add hsle (Nat.le_refl _)))
  · have hcopPM : Nat.Coprime (5 ^ (K + j + 1)) M := Nat.Coprime.pow_left _ hM3
    apply mod_combine hcopPM
    · rw [Nat.mul_mod, pow_mod_period hT k2, ← Nat.mul_mod, hk2P]
    · have hk : k2 + T * (s + 5 ^ K * D' * B) = k' + 5 ^ K * D' * (4 * n0 + T * B) := by
        have e1 : k2 = k' + 4 * 5 ^ K * r := (Nat.sub_eq_iff_eq_add' hk2k).1 hr
        have e2 : T = 4 * 5 ^ K * 5 ^ j := by show 4 * 5 ^ (K + j) = _; rw [Nat.pow_add]; grind
        rw [e1, e2]
        have e3 : 4 * 5 ^ K * r + 4 * 5 ^ K * 5 ^ j * s = 5 ^ K * D' * (4 * n0) := by
          rw [show 4 * 5 ^ K * r + 4 * 5 ^ K * 5 ^ j * s = 4 * 5 ^ K * (r + 5 ^ j * s) by grind, hn0]
          grind
        grind
      rw [hZM, hk, Nat.mul_mod (2 ^ (k' + 5 ^ K * D' * (4 * n0 + T * B))), pow_mod_period hD k',
        ← Nat.mul_mod]

theorem mod_lin {Q a b : Nat} (c d : Nat) (h : a % Q = b % Q) : (c * a + d) % Q = (c * b + d) % Q := by
  rw [Nat.add_mod, Nat.mul_mod, h, ← Nat.mul_mod, ← Nat.add_mod]

theorem closure_word (Q w : Nat) {x : Nat} (h : Closure Q w x) :
    ∃ (u : List Nat) (k : Nat), (∀ e ∈ u, e ≤ 1) ∧
      (5 ^ oneCount u * x + offset u) % Q = (2 ^ (u.length + k) * w) % Q := by
  induction h with
  | base k x hx => exact ⟨[], k, by simp, by unfold SameMod at hx; simpa [oneCount, offset] using hx⟩
  | @dbl z hz ih =>
    obtain ⟨u, k, hu, h⟩ := ih
    refine ⟨0 :: u, k, ?_, ?_⟩
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · omega
      · exact hu e he
    · have hh := mod_lin 2 0 h
      have e1 : 5 ^ oneCount (0 :: u) * (2 * z) + offset (0 :: u) = 2 * (5 ^ oneCount u * z + offset u) + 0 := by
        simp only [oneCount, offset, Nat.add_zero, Nat.mul_zero]; grind
      have e2 : 2 ^ ((0 :: u).length + k) * w = 2 * (2 ^ (u.length + k) * w) + 0 := by
        rw [List.length_cons, show u.length + 1 + k = (u.length + k) + 1 by omega, Nat.pow_succ]; grind
      rw [e1, e2]; exact hh
  | @undo z x hz hx ih =>
    obtain ⟨u, k, hu, h⟩ := ih
    refine ⟨1 :: u, k, ?_, ?_⟩
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · omega
      · exact hu e he
    · have hh := mod_lin 2 0 h
      have hx' := mod_lin (5 ^ oneCount u) (2 * offset u) (show (5 * x + 1) % Q = (2 * z) % Q from hx)
      have e1 : 5 ^ oneCount (1 :: u) * x + offset (1 :: u) = 5 ^ oneCount u * (5 * x + 1) + 2 * offset u := by
        simp only [oneCount, offset]; grind
      have e3 : 5 ^ oneCount u * (2 * z) + 2 * offset u = 2 * (5 ^ oneCount u * z + offset u) + 0 := by grind
      have e2 : 2 ^ ((1 :: u).length + k) * w = 2 * (2 ^ (u.length + k) * w) + 0 := by
        rw [List.length_cons, show u.length + 1 + k = (u.length + k) + 1 by omega, Nat.pow_succ]; grind
      rw [e1, e2]
      exact hx'.trans (by rw [e3]; exact hh)
  | @cong z x hz hx ih =>
    obtain ⟨u, k, hu, h⟩ := ih
    exact ⟨u, k, hu, (mod_lin (5 ^ oneCount u) (offset u) (show x % Q = z % Q from hx)).trans h⟩

theorem split_five (D : Nat) (hD : 0 < D) : ∃ ν d, D = 5 ^ ν * d ∧ d % 5 ≠ 0 := by
  induction D using Nat.strongRecOn with
  | _ D ih =>
    by_cases h : D % 5 = 0
    · obtain ⟨ν, d, hd, h3⟩ := ih (D / 5) (by omega) (by omega)
      refine ⟨ν + 1, d, ?_, h3⟩
      have : D = 5 * (D / 5) := by omega
      rw [this, hd, Nat.pow_succ]; grind
    · exact ⟨0, D, by simp, h⟩

theorem exists_pow2_period (M : Nat) (hM : 0 < M) (hc : Nat.Coprime M 2) :
    ∃ D, 0 < D ∧ D ≤ M ∧ 2 ^ D % M = 1 % M := by
  apply Classical.byContradiction
  intro hno
  have hinj : ∀ a b, a < b → b ≤ M → 2 ^ a % M ≠ 2 ^ b % M := by
    intro a b hab hb heq
    apply hno
    refine ⟨b - a, by omega, by omega, ?_⟩
    have hcop : Nat.Coprime M (2 ^ a) := Nat.Coprime.pow_right _ hc
    exact mod_cancel_mul_right (x := 2 ^ (b - a)) (y := 1) hcop
      (by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega), Nat.one_mul]; exact heq.symm)
  have hnd : ((List.range (M + 1)).map (fun i => 2 ^ i % M)).Nodup := by
    apply List.pairwise_map.2
    apply List.Pairwise.imp_of_mem _ List.nodup_range
    intro a b ha hb hab
    rw [List.mem_range] at ha hb
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · exact hinj a b h (by omega)
    · exact fun h' => hinj b a h (by omega) h'.symm
  have hsub : ((List.range (M + 1)).map (fun i => 2 ^ i % M)) ⊆ List.range M := by
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨i, _, rfl⟩ := hv
    rw [List.mem_range]; exact Nat.mod_lt _ hM
  have := hnd.length_le_of_subset hsub
  simp at this
  omega

theorem reaches_pow2 (w : Nat) : ∀ n, Reaches w (2 ^ n * w)
  | 0 => ⟨0, by simp [iter]⟩
  | n + 1 => by
    obtain ⟨k, hk⟩ := reaches_pow2 w n
    refine ⟨k + 1, ?_⟩
    rw [iter_add]
    show iter collatz k (collatz (2 ^ (n + 1) * w)) = w
    rw [show 2 ^ (n + 1) * w = 2 * (2 ^ n * w) by rw [Nat.pow_succ]; grind, collatz_double]; exact hk

theorem integrality_reaches (u : List Nat) (hu : ∀ e ∈ u, e ≤ 1) (x : Nat)
    (h : 2 ^ u.length ∣ 5 ^ oneCount u * x + offset u) :
    Reaches ((5 ^ oneCount u * x + offset u) / 2 ^ u.length) x := integrality u hu x h

theorem coprime10_of_not_dvd (N : Nat) (h2 : N % 2 ≠ 0) (h5 : N % 5 ≠ 0) : Nat.Coprime N 10 := by
  unfold Nat.Coprime
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd N 10 := ⟨_, rfl⟩
  have h1 : g ∣ N := hg ▸ Nat.gcd_dvd_left N 10
  have h6 : g ∣ 10 := hg ▸ Nat.gcd_dvd_right N 10
  have hle : g ≤ 10 := Nat.le_of_dvd (by decide) h6
  rw [← hg]
  have hpos : 0 < g := Nat.pos_of_dvd_of_pos h6 (by decide)
  have hcases : g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5 ∨ g = 6 ∨ g = 7 ∨ g = 8 ∨ g = 9 ∨ g = 10 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem split_two_five (N : Nat) (hN : 1 ≤ N) :
    ∃ a b M, N = 2 ^ a * 5 ^ b * M ∧ Nat.Coprime M 10 := by
  induction N using Nat.strongRecOn with
  | _ N ih =>
    by_cases h2 : N % 2 = 0
    · obtain ⟨a, b, M, hM, hc⟩ := ih (N / 2) (by omega) (by omega)
      refine ⟨a + 1, b, M, ?_, hc⟩
      have : N = 2 * (N / 2) := by omega
      rw [this, hM, Nat.pow_succ]; grind
    · by_cases h5 : N % 5 = 0
      · obtain ⟨a, b, M, hM, hc⟩ := ih (N / 5) (by omega) (by omega)
        refine ⟨a, b + 1, M, ?_, hc⟩
        have : N = 5 * (N / 5) := by omega
        rw [this, hM, Nat.pow_succ 5 b]; grind
      · exact ⟨0, 0, N, by simp, coprime10_of_not_dvd N h2 h5⟩

theorem parity_word : ∀ (a r : Nat), ∃ p : List Nat, p.length = a ∧ (∀ e ∈ p, e ≤ 1) ∧
    2 ^ a ∣ 5 ^ oneCount p * r + offset p
  | 0, r => ⟨[], rfl, by simp, by simp [oneCount, offset]⟩
  | a + 1, r => by
    obtain ⟨y, hy | hy⟩ : ∃ y, r = 2 * y ∨ r = 2 * y + 1 := ⟨r / 2, by omega⟩
    · obtain ⟨p, hl, hp, hd⟩ := parity_word a y
      refine ⟨0 :: p, by simp [hl], ?_, ?_⟩
      · intro e he
        rcases List.mem_cons.1 he with rfl | he
        · omega
        · exact hp e he
      · have h2 := Nat.mul_dvd_mul_left 2 hd
        rw [hy]
        have e1 : 5 ^ oneCount (0 :: p) * (2 * y) + offset (0 :: p) = 2 * (5 ^ oneCount p * y + offset p) := by
          simp only [oneCount, offset, Nat.add_zero, Nat.mul_zero]; grind
        rw [e1, show 2 ^ (a + 1) = 2 * 2 ^ a by rw [Nat.pow_succ]; grind]
        exact h2
    · obtain ⟨p, hl, hp, hd⟩ := parity_word a (5 * y + 3)
      refine ⟨1 :: p, by simp [hl], ?_, ?_⟩
      · intro e he
        rcases List.mem_cons.1 he with rfl | he
        · omega
        · exact hp e he
      · have h2 := Nat.mul_dvd_mul_left 2 hd
        rw [hy]
        have e1 : 5 ^ oneCount (1 :: p) * (2 * y + 1) + offset (1 :: p)
            = 2 * (5 ^ oneCount p * (5 * y + 3) + offset p) := by
          simp only [oneCount, offset]; grind
        rw [e1, show 2 ^ (a + 1) = 2 * 2 ^ a by rw [Nat.pow_succ]; grind]
        exact h2

section Short
variable (Q w : Nat)

def HasWord (n x : Nat) : Prop :=
  ∃ (u : List Nat) (k : Nat), (∀ e ∈ u, e ≤ 1) ∧ u.length ≤ n ∧
    (5 ^ oneCount u * x + offset u) % Q = (2 ^ (u.length + k) * w) % Q

theorem hasWord_mono {n x : Nat} (h : HasWord Q w n x) : HasWord Q w (n + 1) x := by
  obtain ⟨u, k, hu, hl, he⟩ := h
  exact ⟨u, k, hu, by omega, he⟩

theorem hasWord_le {a b x : Nat} (h : a ≤ b) (hx : HasWord Q w a x) : HasWord Q w b x := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  induction d with
  | zero => exact hx
  | succ d ih => exact hasWord_mono Q w (ih (by omega))

theorem hasWord_mod {n x : Nat} : HasWord Q w n x ↔ HasWord Q w n (x % Q) := by
  constructor
  · rintro ⟨u, k, hu, hl, he⟩
    exact ⟨u, k, hu, hl, (mod_lin (5 ^ oneCount u) (offset u) (Nat.mod_mod x Q)).trans he⟩
  · rintro ⟨u, k, hu, hl, he⟩
    exact ⟨u, k, hu, hl, (mod_lin (5 ^ oneCount u) (offset u) (Nat.mod_mod x Q).symm).trans he⟩

theorem hasWord_base {x k : Nat} (h : x % Q = (2 ^ k * w) % Q) : HasWord Q w 0 x :=
  ⟨[], k, by simp, by simp, by simpa [oneCount, offset] using h⟩

theorem hasWord_step {n x y ε : Nat} (hε : ε ≤ 1) (hy : HasWord Q w n y)
    (h : (2 * y) % Q = (5 ^ ε * x + ε) % Q) : HasWord Q w (n + 1) x := by
  obtain ⟨u, k, hu, hl, he⟩ := hy
  refine ⟨ε :: u, k, ?_, by simp; omega, ?_⟩
  · intro e he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact hε
    · exact hu e he'
  · have hx' := mod_lin (5 ^ oneCount u) (2 * offset u) (show (5 ^ ε * x + ε) % Q = (2 * y) % Q from h.symm)
    have hh := mod_lin 2 0 he
    have e1 : 5 ^ oneCount (ε :: u) * x + offset (ε :: u) = 5 ^ oneCount u * (5 ^ ε * x + ε) + 2 * offset u := by
      simp only [oneCount, offset, Nat.pow_add]; grind
    have e3 : 5 ^ oneCount u * (2 * y) + 2 * offset u = 2 * (5 ^ oneCount u * y + offset u) + 0 := by grind
    have e2 : 2 ^ ((ε :: u).length + k) * w = 2 * (2 ^ (u.length + k) * w) + 0 := by
      rw [List.length_cons, show u.length + 1 + k = (u.length + k) + 1 by omega, Nat.pow_succ]; grind
    rw [e1, e2]
    exact hx'.trans (by rw [e3]; exact hh)

theorem hasWord_inv (hQ2 : Q % 2 = 1) {n x : Nat} (h : HasWord Q w (n + 1) x) :
    HasWord Q w 0 x ∨ ∃ ε, ε ≤ 1 ∧ ∃ y, HasWord Q w n y ∧ (2 * y) % Q = (5 ^ ε * x + ε) % Q := by
  have hcop : Nat.Coprime Q 2 := by
    unfold Nat.Coprime; rw [Nat.gcd_comm, Nat.gcd_rec, hQ2]; simp
  obtain ⟨u, k, hu, hl, he⟩ := h
  cases u with
  | nil => left; exact hasWord_base Q w (k := k) (by simpa [oneCount, offset] using he)
  | cons ε u' =>
    right
    refine ⟨ε, hu ε (by simp), ((Q + 1) / 2) * (5 ^ ε * x + ε), ?_, ?_⟩
    · have h2y : (2 * (((Q + 1) / 2) * (5 ^ ε * x + ε))) % Q = (5 ^ ε * x + ε) % Q := by
        have : 2 * (((Q + 1) / 2) * (5 ^ ε * x + ε)) = (5 ^ ε * x + ε) + Q * (5 ^ ε * x + ε) := by
          have h2 : 2 * ((Q + 1) / 2) = Q + 1 := by omega
          rw [← Nat.mul_assoc, h2]; grind
        rw [this, Nat.add_mul_mod_self_left]
      refine ⟨u', k, fun e he' => hu e (by simp [he']), by simp at hl; omega, ?_⟩
      have e1 : 5 ^ oneCount (ε :: u') * x + offset (ε :: u') = 5 ^ oneCount u' * (5 ^ ε * x + ε) + 2 * offset u' := by
        simp only [oneCount, offset, Nat.pow_add]; grind
      have e2 : 2 ^ ((ε :: u').length + k) * w = 2 * (2 ^ (u'.length + k) * w) := by
        rw [List.length_cons, show u'.length + 1 + k = (u'.length + k) + 1 by omega, Nat.pow_succ]; grind
      rw [e1, e2] at he
      have hz := mod_lin (5 ^ oneCount u') (2 * offset u')
        (show (5 ^ ε * x + ε) % Q = (2 * (((Q + 1) / 2) * (5 ^ ε * x + ε))) % Q from h2y.symm)
      have hA : ((5 ^ oneCount u' * (((Q + 1) / 2) * (5 ^ ε * x + ε)) + offset u') * 2) % Q
          = ((2 ^ (u'.length + k) * w) * 2) % Q := by
        have e3 : (5 ^ oneCount u' * (((Q + 1) / 2) * (5 ^ ε * x + ε)) + offset u') * 2
            = 5 ^ oneCount u' * (2 * (((Q + 1) / 2) * (5 ^ ε * x + ε))) + 2 * offset u' := by grind
        have e4 : (2 ^ (u'.length + k) * w) * 2 = 2 * (2 ^ (u'.length + k) * w) := by grind
        rw [e3, e4]; exact hz.symm.trans he
      exact mod_cancel_mul_right hcop hA
    · have h2 : 2 * (((Q + 1) / 2) * (5 ^ ε * x + ε)) = (5 ^ ε * x + ε) + Q * (5 ^ ε * x + ε) := by
        have h2' : 2 * ((Q + 1) / 2) = Q + 1 := by omega
        rw [← Nat.mul_assoc, h2']; grind
      rw [h2, Nat.add_mul_mod_self_left]

theorem cardinality_le_modulus {Q : Nat} (S : Fin Q → Prop) : cardinality S ≤ Q := by
  classical
  unfold cardinality
  calc ((List.finRange Q).filter (fun t => decide (S t))).length ≤ (List.finRange Q).length :=
        List.length_filter_le _ _
    _ = Q := List.length_finRange

theorem hasWord_stable [NeZero Q] :
    ∃ n, n ≤ Q ∧ ∀ t : Fin Q, HasWord Q w (n + 1) t.val → HasWord Q w n t.val := by
  apply Classical.byContradiction
  intro hno
  have hno' : ∀ n, n ≤ Q → ∃ t : Fin Q, HasWord Q w (n + 1) t.val ∧ ¬ HasWord Q w n t.val := by
    intro n hn
    apply Classical.byContradiction
    intro hc
    exact hno ⟨n, hn, fun t ht => Classical.byContradiction fun h => hc ⟨t, ht, h⟩⟩
  have hc : ∀ n, n ≤ Q + 1 → n + 1 ≤ cardinality (fun t : Fin Q => HasWord Q w n t.val) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact cardinality_pos (t0 := ⟨w % Q, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne Q))⟩)
        (hasWord_base Q w (k := 0) (by simp))
    | succ n ih =>
      intro hn
      obtain ⟨t, h1, h2⟩ := hno' n (by omega)
      have hlt : cardinality (fun t : Fin Q => HasWord Q w n t.val) < cardinality (fun t : Fin Q => HasWord Q w (n + 1) t.val) := by
        apply Classical.byContradiction
        intro hge
        exact h2 (cardinality_eq_of_sub (S := fun t : Fin Q => HasWord Q w n t.val)
          (T := fun t : Fin Q => HasWord Q w (n + 1) t.val) (fun t h => hasWord_mono Q w h)
          (Nat.le_of_not_lt hge) t h1)
      have := ih (by omega)
      omega
  have h1 := hc (Q + 1) (Nat.le_refl _)
  have h2 := cardinality_le_modulus (Q := Q) (fun t : Fin Q => HasWord Q w (Q + 1) t.val)
  omega

theorem hasWord_all_short [NeZero Q] (hQ2 : Q % 2 = 1) (hall : ∀ x, ∃ n, HasWord Q w n x) :
    ∀ x, HasWord Q w Q x := by
  obtain ⟨n, hnQ, hst⟩ := hasWord_stable Q w
  have hQpos : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  have hst' : ∀ x, HasWord Q w (n + 1) x → HasWord Q w n x := by
    intro x hx
    have := hst ⟨x % Q, Nat.mod_lt _ hQpos⟩ ((hasWord_mod Q w).1 hx)
    exact (hasWord_mod Q w).2 this
  have hstab : ∀ d x, HasWord Q w (n + d) x → HasWord Q w n x := by
    intro d
    induction d with
    | zero => exact fun x h => h
    | succ d ih =>
      intro x hx
      rcases hasWord_inv Q w hQ2 (show HasWord Q w (n + d + 1) x from hx) with h0 | ⟨ε, hε, y, hy, h⟩
      · exact hasWord_le Q w (Nat.zero_le n) h0
      · exact hst' x (hasWord_step Q w hε (ih y hy) h)
  intro x
  obtain ⟨m, hm⟩ := hall x
  by_cases hnm : n ≤ m
  · obtain ⟨d, rfl⟩ : ∃ d, m = n + d := ⟨m - n, by omega⟩
    exact hasWord_le Q w hnQ (hstab d x hm)
  · exact hasWord_le Q w (by omega) hm

end Short

theorem closure_word_short (M K w : Nat) [NeZero M] (hM : Nat.Coprime M 10) (hw : w % 5 ≠ 0) (x : Nat) :
    ∃ (u : List Nat) (k : Nat), (∀ e ∈ u, e ≤ 1) ∧ u.length ≤ 5 ^ (K + 1) * M ∧
      (5 ^ oneCount u * x + offset u) % (5 ^ (K + 1) * M) = (2 ^ (u.length + k) * w) % (5 ^ (K + 1) * M) := by
  haveI : NeZero (5 ^ (K + 1) * M) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pos_of_ne_zero (NeZero.ne M)))⟩
  have hM2 : M % 2 = 1 := by
    apply Classical.byContradiction
    intro h
    have h2 : 2 ∣ M := Nat.dvd_of_mod_eq_zero (by omega)
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm (Nat.Coprime.coprime_dvd_right (by decide) hM)) h2
    omega
  have hQ2 : (5 ^ (K + 1) * M) % 2 = 1 := by
    rw [Nat.mul_mod, five_pow_odd, hM2]
  have hall : ∀ x, ∃ n, HasWord (5 ^ (K + 1) * M) w n x := by
    intro x
    obtain ⟨u, k, hu, h⟩ := closure_word _ w (closure_all M K w hM hw x)
    exact ⟨u.length, u, k, hu, Nat.le_refl _, h⟩
  exact hasWord_all_short _ w hQ2 hall x

theorem oneCount_le : ∀ u : List Nat, (∀ e ∈ u, e ≤ 1) → oneCount u ≤ u.length
  | [], _ => by simp [oneCount]
  | e :: u, hu => by
    have h1 := oneCount_le u (fun d hd => hu d (by simp [hd]))
    have h2 := hu e (by simp)
    simp only [oneCount, List.length_cons]; omega

theorem offset_le : ∀ u : List Nat, (∀ e ∈ u, e ≤ 1) → offset u ≤ 10 ^ u.length
  | [], _ => by simp [offset]
  | e :: u, hu => by
    have hu' : ∀ d ∈ u, d ≤ 1 := fun d hd => hu d (by simp [hd])
    have ih := offset_le u hu'
    have hj := oneCount_le u hu'
    have h3 : 5 ^ oneCount u ≤ 5 ^ u.length := Nat.pow_le_pow_right (by omega) hj
    have h36 : 5 ^ u.length ≤ 10 ^ u.length := Nat.pow_le_pow_left (by omega) _
    have he := hu e (by simp)
    have h6 : 10 ^ (u.length + 1) = 10 ^ u.length * 10 := Nat.pow_succ ..
    have h7 : 5 ^ oneCount u * e ≤ 5 ^ oneCount u := by
      rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl <;> simp
    simp only [offset, List.length_cons]
    rw [h6]
    omega

theorem mod_mul_right_cong {Q a b : Nat} (c : Nat) (h : a % Q = b % Q) : (a * c) % Q = (b * c) % Q := by
  rw [Nat.mul_mod, h, ← Nat.mul_mod]

theorem pow2_period_lift (M K D' : Nat) (hM : Nat.Coprime M 10)
    (hD : 2 ^ (5 ^ K * D') % M = 1 % M) :
    2 ^ (4 * 5 ^ K * D') % (5 ^ (K + 1) * M) = 1 % (5 ^ (K + 1) * M) := by
  have hM3 : Nat.Coprime 5 M := Nat.Coprime.symm (Nat.Coprime.coprime_dvd_right (by decide) hM)
  have hcop : Nat.Coprime (5 ^ (K + 1)) M := Nat.Coprime.pow_left _ hM3
  have h1 : 2 ^ (4 * 5 ^ K) % 5 ^ (K + 1) = 1 := two_pow_mod_eq_one_iff.2 (Nat.dvd_refl _)
  have hA : 2 ^ (4 * 5 ^ K * D') % 5 ^ (K + 1) = 1 % 5 ^ (K + 1) := by
    calc 2 ^ (4 * 5 ^ K * D') % 5 ^ (K + 1) = (2 ^ (4 * 5 ^ K)) ^ D' % 5 ^ (K + 1) := by rw [Nat.pow_mul]
      _ = ((2 ^ (4 * 5 ^ K)) % 5 ^ (K + 1)) ^ D' % 5 ^ (K + 1) := Nat.pow_mod _ _ _
      _ = 1 % 5 ^ (K + 1) := by rw [h1, Nat.one_pow]
  have hB : 2 ^ (4 * 5 ^ K * D') % M = 1 % M := by
    rw [show 4 * 5 ^ K * D' = (5 ^ K * D') * 4 by grind, Nat.pow_mul, Nat.pow_mod, hD,
      ← Nat.pow_mod, Nat.one_pow]
  exact mod_combine hcop hA hB

theorem five_pow_le (n : Nat) : 5 ^ n ≤ 2 ^ (3 * n) := by
  calc 5 ^ n ≤ 8 ^ n := Nat.pow_le_pow_left (by omega) n
    _ = 2 ^ (3 * n) := by rw [Nat.pow_mul]

theorem ten_pow_le (n : Nat) : 10 ^ n ≤ 2 ^ (4 * n) := by
  calc 10 ^ n ≤ 16 ^ n := Nat.pow_le_pow_left (by omega) n
    _ = 2 ^ (4 * n) := by rw [Nat.pow_mul]

theorem pow2bound_mul {x y p q : Nat} (hx : x ≤ 2 ^ p) (hy : y ≤ 2 ^ q) : x * y ≤ 2 ^ (p + q) := by
  rw [Nat.pow_add]; exact Nat.mul_le_mul hx hy

theorem pow2bound_le {x p p' : Nat} (hx : x ≤ 2 ^ p) (h : p ≤ p') : x ≤ 2 ^ p' :=
  Nat.le_trans hx (Nat.pow_le_pow_right (by omega) h)

theorem le_two_pow_self (x : Nat) : x ≤ 2 ^ x := Nat.le_of_lt Nat.lt_two_pow_self

theorem bound_arith (X K jv len d' κ C B : Nat) (hX3 : 3 ≤ X) (hK : 5 ^ K ≤ X) (hjv : jv ≤ X)
    (hlen : len ≤ X) (hd' : d' ≤ X) (hκ : κ ≤ 2 * X) (hC : C ≤ 10 ^ X) (hB : B ≤ X) :
    4 * 5 ^ (K + jv) * (κ + 1) + 4 * 5 ^ (K + jv) * (d' * d' * (4 * 5 ^ (K + jv) * (κ + 1))
      + 5 ^ K * d' * (C + len + 5 ^ jv * (B + 1))) ≤ 2 ^ (20 * X) := by
  have hX : X ≤ 2 ^ X := le_two_pow_self X
  have hK' : 5 ^ K ≤ 2 ^ X := Nat.le_trans hK hX
  have hd'' : d' ≤ 2 ^ X := Nat.le_trans hd' hX
  have hlen' : len ≤ 2 ^ X := Nat.le_trans hlen hX
  have hj3 : 5 ^ jv ≤ 2 ^ (3 * X) :=
    Nat.le_trans (Nat.pow_le_pow_right (by omega) hjv) (five_pow_le X)
  have eKj : 5 ^ (K + jv) = 5 ^ K * 5 ^ jv := by rw [Nat.pow_add]
  have e4 : (4 : Nat) * 2 ^ (4 * X) = 2 ^ (4 * X + 2) := by
    rw [show 4 * X + 2 = (4 * X + 1) + 1 by omega, Nat.pow_succ, Nat.pow_succ]; grind
  have hT : 4 * 5 ^ (K + jv) ≤ 2 ^ (4 * X + 2) := by
    calc 4 * 5 ^ (K + jv) = 4 * (5 ^ K * 5 ^ jv) := by rw [eKj]
      _ ≤ 4 * 2 ^ (X + 3 * X) := Nat.mul_le_mul_left 4 (pow2bound_mul hK' hj3)
      _ = 2 ^ (4 * X + 2) := by rw [show X + 3 * X = 4 * X by omega]; exact e4
  have hκ1 : κ + 1 ≤ 2 ^ (2 * X + 1) :=
    Nat.le_trans (by omega : κ + 1 ≤ 2 * X + 1) (le_two_pow_self _)
  have hTk : 4 * 5 ^ (K + jv) * (κ + 1) ≤ 2 ^ (6 * X + 3) :=
    pow2bound_le (pow2bound_mul hT hκ1) (by omega)
  have hdd : d' * d' ≤ 2 ^ (2 * X) := pow2bound_le (pow2bound_mul hd'' hd'') (by omega)
  have hA : d' * d' * (4 * 5 ^ (K + jv) * (κ + 1)) ≤ 2 ^ (8 * X + 5) :=
    pow2bound_le (pow2bound_mul hdd hTk) (by omega)
  have hC' : C ≤ 2 ^ (4 * X) := Nat.le_trans hC (ten_pow_le X)
  have hB1 : B + 1 ≤ 2 ^ (X + 1) := Nat.le_trans (by omega : B + 1 ≤ X + 1) (le_two_pow_self _)
  have hm : 5 ^ jv * (B + 1) ≤ 2 ^ (4 * X + 1) :=
    pow2bound_le (pow2bound_mul hj3 hB1) (by omega)
  have h1 : len ≤ 2 ^ (4 * X) := pow2bound_le hlen' (by omega)
  have e41 : 2 ^ (4 * X + 1) = 2 * 2 ^ (4 * X) := by
    rw [show 4 * X + 1 = (4 * X) + 1 by omega, Nat.pow_succ]; grind
  have e42 : 2 ^ (4 * X + 2) = 4 * 2 ^ (4 * X) := e4.symm
  have hBp : C + len + 5 ^ jv * (B + 1) ≤ 2 ^ (4 * X + 2) := by omega
  have hP : 5 ^ K * d' * (C + len + 5 ^ jv * (B + 1)) ≤ 2 ^ (6 * X + 2) :=
    pow2bound_le (pow2bound_mul (pow2bound_mul hK' hd'') hBp) (by omega)
  have hI : d' * d' * (4 * 5 ^ (K + jv) * (κ + 1)) + 5 ^ K * d' * (C + len + 5 ^ jv * (B + 1))
      ≤ 2 ^ (8 * X + 6) := by
    have eI : 2 ^ (8 * X + 6) = 2 * 2 ^ (8 * X + 5) := by
      rw [show 8 * X + 6 = (8 * X + 5) + 1 by omega, Nat.pow_succ]; grind
    have hleP : 2 ^ (6 * X + 2) ≤ 2 ^ (8 * X + 5) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hTI := pow2bound_le (pow2bound_mul hT hI) (show 4 * X + 2 + (8 * X + 6) ≤ 12 * X + 8 by omega)
  have hmain : 4 * 5 ^ (K + jv) * (κ + 1) + 4 * 5 ^ (K + jv) * (d' * d' * (4 * 5 ^ (K + jv) * (κ + 1))
      + 5 ^ K * d' * (C + len + 5 ^ jv * (B + 1))) ≤ 2 ^ (12 * X + 9) := by
    refine Nat.le_trans (Nat.add_le_add hTk hTI) ?_
    have emain : 2 ^ (12 * X + 9) = 2 * 2 ^ (12 * X + 8) := by
      rw [show 12 * X + 9 = (12 * X + 8) + 1 by omega, Nat.pow_succ]; grind
    have hleTk : 2 ^ (6 * X + 3) ≤ 2 ^ (12 * X + 8) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  exact pow2bound_le hmain (by omega)

theorem hit_residue (M b' e B w X : Nat) (hM : Nat.Coprime M 10) (hw : w % 5 ≠ 0)
    (hX : 5 * (5 ^ b' * M * M) ≤ X) (hBX : B ≤ X) :
    ∃ m, B < m ∧ m % (5 ^ b' * M) = e % (5 ^ b' * M) ∧ Reaches w m ∧ m ≤ w * 2 ^ (2 ^ (20 * X)) := by
  have hM0 : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; exact absurd hM (by decide)
    · exact h
  haveI : NeZero M := ⟨by omega⟩
  have hM2 : Nat.Coprime M 2 := Nat.Coprime.coprime_dvd_right (by decide) hM
  obtain ⟨D, hD0, hDM, hD⟩ := exists_pow2_period M hM0 hM2
  obtain ⟨ν, d', hDd, hd3⟩ := split_five D hD0
  obtain ⟨K, hKd⟩ : ∃ K, K = ν + b' := ⟨_, rfl⟩
  have hKν : ν ≤ K := by omega
  have hKb : b' ≤ K + 1 := by omega
  have hd'pos : 1 ≤ d' := by omega
  have h3ν : 0 < 5 ^ ν := Nat.pow_pos (by omega)
  have hper : 2 ^ (5 ^ K * d') % M = 1 % M := by
    have e1 : 5 ^ K = 5 ^ ν * 5 ^ (K - ν) := by rw [← Nat.pow_add, Nat.add_sub_cancel' hKν]
    have e2 : 5 ^ K * d' = D * 5 ^ (K - ν) := by rw [hDd, e1]; grind
    rw [e2, Nat.pow_mul, Nat.pow_mod, hD, ← Nat.pow_mod, Nat.one_pow]
  have hν3 : 5 ^ ν ≤ M := by
    have := Nat.le_mul_of_pos_right (5 ^ ν) hd'pos
    rw [← hDd] at this; omega
  have hd'M : d' ≤ M := by
    have := Nat.le_mul_of_pos_left d' h3ν
    rw [← hDd] at this; omega
  have hK3 : 5 ^ K ≤ 5 ^ b' * M := by
    rw [hKd, Nat.pow_add]
    calc 5 ^ ν * 5 ^ b' ≤ M * 5 ^ b' := Nat.mul_le_mul_right _ hν3
      _ = 5 ^ b' * M := Nat.mul_comm _ _
  have hS : 0 < 5 ^ b' * M := Nat.mul_pos (Nat.pow_pos (by omega)) hM0
  rw [← Nat.mul_assoc] at hX
  have hSX : 5 ^ b' * M ≤ X := by
    have := Nat.le_mul_of_pos_right (5 * (5 ^ b' * M)) hM0
    omega
  have hMX : M ≤ X := by
    have := Nat.le_mul_of_pos_left M (show 0 < 5 * (5 ^ b' * M) by omega)
    omega
  have hX3 : 3 ≤ X := by
    have e : 5 * (5 ^ b' * M) * M = 5 * (5 ^ b' * M * M) := by grind
    have := Nat.mul_pos hS hM0
    omega
  have hQ : 5 ^ (K + 1) * M = 5 * 5 ^ K * M := by rw [Nat.pow_succ]; grind
  have hQX : 5 ^ (K + 1) * M ≤ X := by
    rw [hQ]
    exact Nat.le_trans (Nat.mul_le_mul_right M (Nat.mul_le_mul_left 5 hK3)) hX
  have hK3X : 5 ^ K ≤ X := Nat.le_trans hK3 hSX
  have hd'X : d' ≤ X := Nat.le_trans hd'M hMX
  have hπX : 4 * 5 ^ K * d' ≤ X := by
    have h1 := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hK3) hd'M
    have h2 : 4 * (5 ^ b' * M) * M ≤ 5 * (5 ^ b' * M) * M :=
      Nat.mul_le_mul_right M (Nat.mul_le_mul_right _ (by omega))
    exact Nat.le_trans h1 (Nat.le_trans h2 hX)
  have hπpos : 0 < 4 * 5 ^ K * d' :=
    Nat.mul_pos (Nat.mul_pos (by omega) (Nat.pow_pos (by omega))) hd'pos
  obtain ⟨u, kk, hu, hlen, hk'⟩ := closure_word_short M K w hM hw e
  have hlenX : u.length ≤ X := Nat.le_trans hlen hQX
  have hπ := pow2_period_lift M K d' hM hper
  have hkr : (5 ^ oneCount u * e + offset u) % (5 ^ (K + 1) * M)
      = (2 ^ (u.length + kk % (4 * 5 ^ K * d')) * w) % (5 ^ (K + 1) * M) := by
    have h1 : 2 ^ (u.length + kk) % (5 ^ (K + 1) * M)
        = 2 ^ (u.length + kk % (4 * 5 ^ K * d')) % (5 ^ (K + 1) * M) := by
      have e' : u.length + kk = (u.length + kk % (4 * 5 ^ K * d')) + (4 * 5 ^ K * d') * (kk / (4 * 5 ^ K * d')) := by
        have := Nat.mod_add_div kk (4 * 5 ^ K * d'); omega
      rw [e']; exact pow_mod_period hπ _ _
    exact hk'.trans (mod_mul_right_cong w h1)
  have hκ : u.length + kk % (4 * 5 ^ K * d') ≤ 2 * X := by
    have := Nat.mod_lt kk hπpos; omega
  have hw1 : 1 ≤ w := by omega
  obtain ⟨k, hk, hkU, hkZ⟩ := exponent_class M K (oneCount u) w (5 ^ oneCount u * e + offset u)
    (u.length + kk % (4 * 5 ^ K * d')) d' (offset u + u.length + 5 ^ oneCount u * (B + 1)) hM hw hd3 hper hkr
  have hU := bound_arith X K (oneCount u) u.length d' (u.length + kk % (4 * 5 ^ K * d')) (offset u) B hX3 hK3X
    (Nat.le_trans (oneCount_le u hu) hlenX) hlenX hd'X hκ
    (Nat.le_trans (offset_le u hu) (Nat.pow_le_pow_right (by omega) hlenX)) hBX
  have hkX : k ≤ 2 ^ (20 * X) := Nat.le_trans hkU hU
  have hbig : offset u + u.length + 5 ^ oneCount u * (B + 1) < 2 ^ k * w :=
    Nat.lt_of_le_of_lt hk (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.le_mul_of_pos_right _ hw1))
  have hj0 : 0 < 5 ^ oneCount u := Nat.pow_pos (by omega)
  have hdv : 5 ^ oneCount u ∣ 5 ^ (K + oneCount u + 1) * M :=
    Nat.dvd_trans (Nat.pow_dvd_pow 5 (by omega)) (Nat.dvd_mul_right _ _)
  have hd : (2 ^ k * w - offset u) % 5 ^ oneCount u = 0 := by
    apply Nat.sub_mod_eq_zero_of_mod_eq
    rw [mod_of_dvd_mod hdv hkZ.symm, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
  have hm3 := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hd)
  obtain ⟨m, hm⟩ : ∃ m, m = (2 ^ k * w - offset u) / 5 ^ oneCount u := ⟨_, rfl⟩
  rw [← hm] at hm3
  rw [Nat.mul_add, Nat.mul_one] at hbig
  have heq : 5 ^ oneCount u * m + offset u = 2 ^ k * w := by omega
  have hmB : B < m := by
    apply Classical.byContradiction
    intro hc
    have := Nat.mul_le_mul_left (5 ^ oneCount u) (Nat.le_of_not_lt hc)
    omega
  refine ⟨m, hmB, ?_, ?_, ?_⟩
  · have h1 : (offset u + 5 ^ oneCount u * m) % (5 ^ (K + oneCount u + 1) * M) = (offset u + 5 ^ oneCount u * e) % (5 ^ (K + oneCount u + 1) * M) := by
      rw [Nat.add_comm (offset u) (5 ^ oneCount u * m), Nat.add_comm (offset u) (5 ^ oneCount u * e), heq]
      exact hkZ.symm
    have h2 := mod_add_left_cancel h1
    have hBig : 5 ^ (K + oneCount u + 1) * M = 5 ^ oneCount u * (5 ^ (K + 1) * M) := by
      rw [show K + oneCount u + 1 = oneCount u + (K + 1) by omega, Nat.pow_add, Nat.mul_assoc]
    rw [hBig, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at h2
    have h3 := Nat.eq_of_mul_eq_mul_left hj0 h2
    exact mod_of_dvd_mod (Nat.mul_dvd_mul_right (Nat.pow_dvd_pow 5 hKb) M) h3
  · have hak : u.length ≤ k := by omega
    have hdiv : 2 ^ u.length ∣ 5 ^ oneCount u * m + offset u :=
      ⟨2 ^ (k - u.length) * w, by rw [heq, ← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' hak]⟩
    have hq : (5 ^ oneCount u * m + offset u) / 2 ^ u.length = 2 ^ (k - u.length) * w := by
      rw [heq, show 2 ^ k * w = 2 ^ u.length * (2 ^ (k - u.length) * w) by
        rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' hak]]
      exact Nat.mul_div_cancel_left _ (Nat.pow_pos (by omega))
    have hr := integrality_reaches u hu m hdiv
    rw [hq] at hr
    exact reaches_trans hr (reaches_pow2 w _)
  · have h1 : m ≤ 5 ^ oneCount u * m := Nat.le_mul_of_pos_left m hj0
    have h2 : m ≤ 2 ^ k * w := by omega
    have h3 : 2 ^ k ≤ 2 ^ (2 ^ (20 * X)) := Nat.pow_le_pow_right (by omega) hkX
    calc m ≤ 2 ^ k * w := h2
      _ ≤ 2 ^ (2 ^ (20 * X)) * w := Nat.mul_le_mul_right w h3
      _ = w * 2 ^ (2 ^ (20 * X)) := Nat.mul_comm _ _

theorem remainder_bounded (N : Nat) (hN : 1 ≤ N) (w : Nat) (hw5 : w % 5 ≠ 0)
    (r B : Nat) :
    ∃ n : Nat, B < n ∧ Reaches w n ∧ n % N = r % N ∧
      n ≤ w * 2 ^ (2 ^ (21 * (5 * N ^ 5 * (B + 1)))) := by
  obtain ⟨α, b, M, hNd, h6⟩ := split_two_five N hN
  have hM0 : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; exact absurd h6 (by decide)
    · exact h
  obtain ⟨p, hpl, hpe, e, he0⟩ := parity_word α (r % N)
  have hr0 : r % N < N := Nat.mod_lt _ (by omega)
  have h2pos : 0 < 2 ^ α := Nat.pow_pos (by omega)
  have h3bM : 0 < 5 ^ b * M := Nat.mul_pos (Nat.pow_pos (by omega)) hM0
  have hNe : N = 2 ^ α * (5 ^ b * M) := by rw [hNd]; grind
  have hM2 : M % 2 ≠ 0 := by
    intro h0
    have hd2 : 2 ∣ M := Nat.dvd_of_mod_eq_zero h0
    have hc2 : Nat.Coprime 2 10 := Nat.Coprime.coprime_dvd_left hd2 h6
    have := Nat.Coprime.eq_one_of_dvd hc2 (by decide : 2 ∣ 10)
    omega
  have hM5 : M % 5 ≠ 0 := by
    intro h0
    have hd5 : 5 ∣ M := Nat.dvd_of_mod_eq_zero h0
    have hc5 : Nat.Coprime 5 10 := Nat.Coprime.coprime_dvd_left hd5 h6
    have := Nat.Coprime.eq_one_of_dvd hc5 (by decide : 5 ∣ 10)
    omega
  have hM10' : Nat.Coprime M 10 := coprime10_of_not_dvd M hM2 hM5
  have h2aN : 2 ^ α ≤ N := by
    rw [hNe]; exact Nat.le_mul_of_pos_right _ h3bM
  have h3bMN : 5 ^ b * M ≤ N := by
    rw [hNe]; exact Nat.le_mul_of_pos_left _ h2pos
  have hMN : M ≤ N := Nat.le_trans (Nat.le_mul_of_pos_left M (Nat.pow_pos (by omega))) h3bMN
  have h3αN : 5 ^ α ≤ N ^ 3 := by
    have h1 := five_pow_le α
    have h2 : 2 ^ (3 * α) = (2 ^ α) ^ 3 := by rw [Nat.mul_comm, Nat.pow_mul]
    exact Nat.le_trans h1 (by rw [h2]; exact Nat.pow_le_pow_left h2aN 3)
  have hjp : oneCount p ≤ α := by have := oneCount_le p hpe; rw [hpl] at this; exact this
  have h3jp : 5 ^ oneCount p ≤ N ^ 3 := Nat.le_trans (Nat.pow_le_pow_right (by omega) hjp) h3αN
  have hN3p : N ^ 3 = N ^ 2 * N := Nat.pow_succ N 2
  have hN4 : N ^ 4 = N ^ 3 * N := Nat.pow_succ N 3
  have hN5 : N ^ 5 = N ^ 4 * N := Nat.pow_succ N 4
  have h13 : N ^ 3 ≤ N ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h14 : N ^ 4 ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hS3 : 5 ^ (oneCount p + b) * M ≤ N ^ 4 := by
    rw [Nat.pow_add, Nat.mul_assoc, hN4]; exact Nat.mul_le_mul h3jp h3bMN
  have hSM : 5 ^ (oneCount p + b) * M * M ≤ N ^ 5 := by
    rw [hN5]; exact Nat.mul_le_mul hS3 hMN
  have hN5B : N ^ 5 ≤ 5 * N ^ 5 * (B + 1) := by
    have := Nat.le_mul_of_pos_right (5 * N ^ 5) (show 0 < B + 1 by omega); omega
  have hX : 5 * (5 ^ (oneCount p + b) * M * M) ≤ 5 * N ^ 5 * (B + 1) := by
    have := Nat.mul_le_mul_left 5 hSM
    have h2 := Nat.le_mul_of_pos_right (5 * N ^ 5) (show 0 < B + 1 by omega)
    omega
  have hcc : offset p ≤ 2 ^ α * N ^ 3 := by
    have h1 := offset_le p hpe
    rw [hpl, show (10 : Nat) = 2 * 5 from rfl, Nat.mul_pow] at h1
    exact Nat.le_trans h1 (Nat.mul_le_mul (Nat.le_refl _) h3αN)
  have h3r : 5 ^ oneCount p * (r % N) ≤ N ^ 4 := by
    rw [hN4]; exact Nat.mul_le_mul h3jp (Nat.le_of_lt hr0)
  have h2N3 : 2 ^ α * N ^ 3 ≤ N ^ 4 := by
    calc 2 ^ α * N ^ 3 ≤ N * N ^ 3 := Nat.mul_le_mul_right _ h2aN
      _ = N ^ 4 := by rw [hN4]; grind
  have he1 : e ≤ 2 * N ^ 4 := by
    have h1 : e ≤ 2 ^ α * e := Nat.le_mul_of_pos_left e h2pos
    omega
  have hBX : e + 5 ^ oneCount p * B ≤ 5 * N ^ 5 * (B + 1) := by
    have h2 : 5 ^ oneCount p * B ≤ N ^ 5 * B := Nat.le_trans (Nat.mul_le_mul_right B h3jp)
      (Nat.mul_le_mul_right B (Nat.pow_le_pow_right (by omega) (by omega)))
    have h3 : 5 * N ^ 5 * (B + 1) = 5 * (N ^ 5 * B) + 5 * N ^ 5 := by grind
    omega
  obtain ⟨m, hmB, hmc, hmw, hmbd⟩ :=
    hit_residue M (oneCount p + b) e (e + 5 ^ oneCount p * B) w (5 * N ^ 5 * (B + 1)) hM10' hw5 hX hBX
  have hj0 : 0 < 5 ^ oneCount p := Nat.pow_pos (by omega)
  have h0 := Nat.sub_mod_eq_zero_of_mod_eq hmc
  obtain ⟨s, hs⟩ := Nat.dvd_of_mod_eq_zero h0
  have hm' : m = e + 5 ^ oneCount p * (5 ^ b * M * s) := by
    have : m - e = 5 ^ oneCount p * (5 ^ b * M * s) := by rw [hs, Nat.pow_add]; grind
    omega
  have htB : B < 5 ^ b * M * s := by
    apply Classical.byContradiction
    intro hc
    have := Nat.mul_le_mul_left (5 ^ oneCount p) (Nat.le_of_not_lt hc)
    omega
  have htm : 5 ^ b * M * s ≤ m := by
    have := Nat.le_mul_of_pos_left (5 ^ b * M * s) hj0
    omega
  have hn : 5 ^ oneCount p * (r % N + 2 ^ α * (5 ^ b * M * s)) + offset p
      = 2 ^ α * (e + 5 ^ oneCount p * (5 ^ b * M * s)) := by
    have : 5 ^ oneCount p * (r % N + 2 ^ α * (5 ^ b * M * s)) + offset p
        = (5 ^ oneCount p * (r % N) + offset p) + 2 ^ α * (5 ^ oneCount p * (5 ^ b * M * s)) := by grind
    rw [this, he0]; grind
  have hm1 : 1 ≤ m := by omega
  refine ⟨r % N + 2 ^ α * (5 ^ b * M * s), ?_, ?_, ?_, ?_⟩
  · have := Nat.le_mul_of_pos_left (5 ^ b * M * s) h2pos
    omega
  · have hdiv : 2 ^ p.length ∣ 5 ^ oneCount p * (r % N + 2 ^ α * (5 ^ b * M * s)) + offset p := by
      rw [hpl, hn]; exact Nat.dvd_mul_right _ _
    have hr := integrality_reaches p hpe _ hdiv
    rw [hpl, hn, Nat.mul_div_cancel_left _ h2pos, ← hm'] at hr
    exact reaches_trans hr hmw
  · rw [show 2 ^ α * (5 ^ b * M * s) = N * s by rw [hNe]; grind, Nat.add_mul_mod_self_left, Nat.mod_mod]
  ·
    have hn1 : r % N + 2 ^ α * (5 ^ b * M * s) ≤ 2 * (N * m) := by
      have h1 : 2 ^ α * (5 ^ b * M * s) ≤ N * m := Nat.mul_le_mul h2aN htm
      have h2 : N ≤ N * m := Nat.le_mul_of_pos_right N hm1
      omega
    have hX1 : N ≤ 5 * N ^ 5 * (B + 1) := by
      have := Nat.le_self_pow (show 5 ≠ 0 by omega) N
      omega
    have hN2 : 2 * N ≤ 2 ^ (N + 1) := by
      have := Nat.lt_two_pow_self (n := N)
      rw [Nat.pow_succ]; omega
    have hN1 : N + 1 ≤ 2 ^ (20 * (5 * N ^ 5 * (B + 1))) :=
      Nat.le_trans Nat.lt_two_pow_self (Nat.pow_le_pow_right (by omega) (by omega))
    have hexp : N + 1 + 2 ^ (20 * (5 * N ^ 5 * (B + 1))) ≤ 2 ^ (21 * (5 * N ^ 5 * (B + 1))) := by
      have hX1' : 1 ≤ 5 * N ^ 5 * (B + 1) := by omega
      have h1 : 2 ^ (20 * (5 * N ^ 5 * (B + 1)) + 1) ≤ 2 ^ (21 * (5 * N ^ 5 * (B + 1))) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : 2 ^ (20 * (5 * N ^ 5 * (B + 1)) + 1) = 2 ^ (20 * (5 * N ^ 5 * (B + 1))) * 2 := Nat.pow_succ 2 _
      omega
    calc r % N + 2 ^ α * (5 ^ b * M * s) ≤ 2 * (N * m) := hn1
      _ ≤ 2 * (N * (w * 2 ^ (2 ^ (20 * (5 * N ^ 5 * (B + 1)))))) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left N hmbd)
      _ = (2 * N) * w * 2 ^ (2 ^ (20 * (5 * N ^ 5 * (B + 1)))) := by grind
      _ ≤ 2 ^ (N + 1) * w * 2 ^ (2 ^ (20 * (5 * N ^ 5 * (B + 1)))) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right w hN2)
      _ = w * 2 ^ (N + 1 + 2 ^ (20 * (5 * N ^ 5 * (B + 1)))) := by
          rw [Nat.pow_add]; grind
      _ ≤ w * 2 ^ (2 ^ (21 * (5 * N ^ 5 * (B + 1)))) :=
          Nat.mul_le_mul_left w (Nat.pow_le_pow_right (by omega) hexp)

theorem effective_remainder_everywhere (N : Nat) (hN : 1 ≤ N) (w : Nat)
    (hw5 : w % 5 ≠ 0) (r : Nat) :
    ∃ n : Nat, Reaches w n ∧ n % N = r % N ∧ n ≤ w * 2 ^ (2 ^ (105 * N ^ 5)) := by
  obtain ⟨n, -, h1, h2, h3⟩ := remainder_bounded N hN w hw5 r 0
  have e : 21 * (5 * N ^ 5 * (0 + 1)) = 105 * N ^ 5 := by
    rw [Nat.add_zero, Nat.mul_one, ← Nat.mul_assoc]
  rw [e] at h3
  exact ⟨n, h1, h2, h3⟩

theorem remainder_infinitely_often (N : Nat) (hN : 1 ≤ N) (w : Nat) (hw5 : w % 5 ≠ 0)
    (r L : Nat) : ∃ n : Nat, L < n ∧ Reaches w n ∧ n % N = r % N := by
  obtain ⟨n, h0, h1, h2, -⟩ := remainder_bounded N hN w hw5 r L
  exact ⟨n, h0, h1, h2⟩

end ERE5
#print axioms ERE5.effective_remainder_everywhere
#print axioms ERE5.remainder_infinitely_often
