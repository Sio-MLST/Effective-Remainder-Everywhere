import Collatz.BackstepCover

namespace Collatz

theorem ipow_dvd (p : Int) {a b : Nat} (h : a ≤ b) : p ^ a ∣ p ^ b :=
  ⟨p ^ (b - a), by rw [← Int.pow_add]; congr 1; omega⟩

theorem fp_step (p : Int) (K j : Nat) (hj1 : 1 ≤ j) (hjK : j ≤ K + 1) (c y : Int)
    (hc : p ^ (K + 1) ∣ (2 - p) * c - 1) (hy : p ^ j ∣ y - c) :
    ∃ z, 2 * y - 1 = p * z ∧ p ^ (j - 1) ∣ z - c := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, K = i + k := ⟨K - i, by omega⟩
  obtain ⟨h1, hh1⟩ := hc
  obtain ⟨h2, hh2⟩ := hy
  have e1 : p ^ (i + k + 1) = p ^ (i + k) * p := Int.pow_succ _ _
  have e2 : p ^ (i + 1) = p ^ i * p := Int.pow_succ _ _
  rw [e1] at hh1
  rw [e2] at hh2
  refine ⟨c + p ^ (i + k) * h1 + 2 * p ^ i * h2, ?_, ?_⟩
  · have key : 2 * y - 1 = ((2 - p) * c - 1) + p * c + 2 * (y - c) := by int_ring
    rw [key, hh1, hh2]
    int_ring
  · show p ^ i ∣ c + p ^ (i + k) * h1 + 2 * p ^ i * h2 - c
    exact ⟨p ^ k * h1 + 2 * h2, by rw [Int.pow_add]; int_ring⟩

theorem locality (p : Int) (hp : p ≠ 0) (K P : Nat) (E : Nat → Int)
    (hE : ∀ j : Nat, (2 : Int) ^ (j * P) = 1 + p ^ (K + 1) * E j)
    (b J J' : Nat → Nat) (y y' : Nat → Int) (n : Nat) (hy0 : y' 0 = y 0)
    (hrel : ∀ i, i < n → p * y (i + 1) + 1 = 2 ^ (b (i + 1)) * 2 ^ (J (i + 1) * P) * y i)
    (hrel' : ∀ i, i < n → p * y' (i + 1) + 1 = 2 ^ (b (i + 1)) * 2 ^ (J' (i + 1) * P) * y' i) :
    ∀ i, i ≤ n → ∀ v, (∀ l, 1 ≤ l → l + K + 1 ≤ i + v → J l = J' l) → p ^ v ∣ y' i - y i := by
  intro i
  induction i with
  | zero =>
    intro _ v _
    rw [hy0, Int.sub_self]
    exact Int.dvd_zero _
  | succ i ih =>
    intro hin v H
    have IH := ih (by omega) (v + 1) (fun l hl hl2 => H l hl (by omega))
    have r0 := hrel i (by omega)
    have r1 := hrel' i (by omega)
    rw [hE (J (i + 1))] at r0
    rw [hE (J' (i + 1))] at r1
    have key : p * (y' (i + 1) - y (i + 1)) = 2 ^ (b (i + 1)) * (y' i - y i)
        + 2 ^ (b (i + 1)) * p ^ (K + 1) * (E (J' (i + 1)) * y' i - E (J (i + 1)) * y i) := by
      have hd : p * (y' (i + 1) - y (i + 1))
          = (p * y' (i + 1) + 1) - (p * y (i + 1) + 1) := by int_ring
      rw [hd, r0, r1]
      simp only [Int.mul_add, Int.mul_one]
      int_ring
    have hmain : p ^ (v + 1) ∣ p * (y' (i + 1) - y (i + 1)) := by
      rw [key]
      apply Int.dvd_add
      · obtain ⟨g, hg⟩ := IH
        exact ⟨2 ^ (b (i + 1)) * g, by rw [hg]; int_ring⟩
      · rcases Nat.lt_or_ge v (K + 1) with hv | hv
        · obtain ⟨g, hg⟩ := ipow_dvd p (show v + 1 ≤ K + 1 by omega)
          exact ⟨2 ^ (b (i + 1)) * g * (E (J' (i + 1)) * y' i - E (J (i + 1)) * y i), by
            rw [hg]; int_ring⟩
        · have hJ : J (i + 1) = J' (i + 1) := H (i + 1) (by omega)
            (by omega)
          rw [← hJ]
          obtain ⟨g, hg⟩ := IH
          have hy' : y' i = y i + p ^ (v + 1) * g := by omega
          exact ⟨2 ^ (b (i + 1)) * p ^ (K + 1) * E (J (i + 1)) * g, by
            rw [hy']; int_ring⟩
    have hpv : p ^ (v + 1) = p * p ^ v := by rw [Int.pow_succ, Int.mul_comm]
    rw [hpv] at hmain
    exact Int.dvd_of_mul_dvd_mul_left hp hmain

def bsum (b : Nat → Nat) (k : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => bsum b k i + b (k + i + 1)

theorem chain_diff_exact (p : Int) (hp : p ≠ 0) (K P : Nat) (E : Int)
    (b J J' : Nat → Nat) (y y' : Nat → Int) (k0 n : Nat)
    (hE : (2 : Int) ^ (J' (k0 + 1) * P) = 1 + p ^ (K + 1) * E)
    (hrel : ∀ i, i < n → p * y (i + 1) + 1 = 2 ^ (b (i + 1)) * 2 ^ (J (i + 1) * P) * y i)
    (hrel' : ∀ i, i < n → p * y' (i + 1) + 1 = 2 ^ (b (i + 1)) * 2 ^ (J' (i + 1) * P) * y' i)
    (hy : y' k0 = y k0) (hJ : J (k0 + 1) = 0) (hag : ∀ l, k0 + 1 < l → J' l = J l) :
    ∀ i, k0 + 1 + i ≤ n → p ^ i * (y' (k0 + 1 + i) - y (k0 + 1 + i))
      = 2 ^ (bsum (fun l => b l + J l * P) (k0 + 1) i)
        * (p ^ K * (2 ^ (b (k0 + 1)) * y k0) * E) := by
  intro i
  induction i with
  | zero =>
    intro hin
    have r0 := hrel k0 (by omega)
    have r1 := hrel' k0 (by omega)
    rw [hJ, Nat.zero_mul, Int.pow_zero, hE, hy] at *
    have h1 : p * (y' (k0 + 1) - y (k0 + 1)) = p * (p ^ K * (2 ^ (b (k0 + 1)) * y k0) * E) := by
      have hd : p * (y' (k0 + 1) - y (k0 + 1)) = (p * y' (k0 + 1) + 1) - (p * y (k0 + 1) + 1) := by int_ring
      rw [hd, r0, r1]
      have e : p ^ (K + 1) = p ^ K * p := Int.pow_succ _ _
      rw [e]
      simp only [Int.mul_add, Int.mul_one]
      int_ring
    have h2 := Int.eq_of_mul_eq_mul_left hp h1
    simp only [bsum, Nat.add_zero, Int.pow_zero, Int.one_mul]
    exact h2
  | succ i ih =>
    intro hin
    have ih := ih (by omega)
    have r0 := hrel (k0 + 1 + i) (by omega)
    have r1 := hrel' (k0 + 1 + i) (by omega)
    have hJi : J' (k0 + 1 + i + 1) = J (k0 + 1 + i + 1) := hag _ (by omega)
    rw [hJi] at r1
    have hd : p * (y' (k0 + 1 + i + 1) - y (k0 + 1 + i + 1))
        = 2 ^ (b (k0 + 1 + i + 1) + J (k0 + 1 + i + 1) * P) * (y' (k0 + 1 + i) - y (k0 + 1 + i)) := by
      have e : (2 : Int) ^ (b (k0 + 1 + i + 1) + J (k0 + 1 + i + 1) * P)
          = 2 ^ (b (k0 + 1 + i + 1)) * 2 ^ (J (k0 + 1 + i + 1) * P) := Int.pow_add _ _ _
      rw [e]
      have hd0 : p * (y' (k0 + 1 + i + 1) - y (k0 + 1 + i + 1))
          = (p * y' (k0 + 1 + i + 1) + 1) - (p * y (k0 + 1 + i + 1) + 1) := by int_ring
      rw [hd0, r0, r1]
      int_ring
    have hp1 : p ^ (i + 1) = p ^ i * p := Int.pow_succ _ _
    have hb : bsum (fun l => b l + J l * P) (k0 + 1) (i + 1)
        = bsum (fun l => b l + J l * P) (k0 + 1) i + (b (k0 + 1 + i + 1) + J (k0 + 1 + i + 1) * P) := rfl
    have hI : k0 + 1 + (i + 1) = k0 + 1 + i + 1 := rfl
    rw [hI, hp1, hb, Int.pow_add]
    have step : p ^ i * p * (y' (k0 + 1 + i + 1) - y (k0 + 1 + i + 1))
        = 2 ^ (b (k0 + 1 + i + 1) + J (k0 + 1 + i + 1) * P) * (p ^ i * (y' (k0 + 1 + i) - y (k0 + 1 + i))) := by
      rw [Int.mul_assoc, hd]; int_ring
    rw [step, ih]
    int_ring

theorem pow_mod_one_int (m : Int) (P j : Nat) (hP : m ∣ (2 : Int) ^ P - 1) :
    m ∣ (2 : Int) ^ (j * P) - 1 := by
  induction j with
  | zero => rw [Nat.zero_mul, Int.pow_zero]; exact ⟨0, by omega⟩
  | succ j ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨h, hh⟩ := hP
    have e : (2 : Int) ^ ((j + 1) * P) = (2 : Int) ^ (j * P) * (2 : Int) ^ P := by
      rw [Nat.succ_mul, Int.pow_add]
    rw [e]
    refine ⟨g * (2 : Int) ^ P + h, ?_⟩
    have hA : (2 : Int) ^ P = 1 + m * h := by omega
    have hB : (2 : Int) ^ (j * P) = 1 + m * g := by omega
    rw [hA, hB]; int_ring

theorem int_binom_quad (a : Int) : ∀ n : Nat, ∃ z, (1 + a) ^ n = 1 + (n : Int) * a + a ^ 2 * z
  | 0 => ⟨0, by simp⟩
  | n + 1 => by
    obtain ⟨z, hz⟩ := int_binom_quad a n
    refine ⟨(n : Int) + z + a * z, ?_⟩
    rw [Int.pow_succ, hz]
    have e : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by omega
    rw [e]
    have e2 : a ^ 2 = a * a := by rw [Int.pow_succ, Int.pow_one]
    rw [e2]
    int_ring

def Efun (p : Int) (K P : Nat) (j : Nat) : Int := ((2 : Int) ^ (j * P) - 1) / p ^ (K + 1)

theorem Efun_spec (p : Int) (hp : p ≠ 0) (K P : Nat) (uP : Int)
    (h : (2 : Int) ^ P = 1 + p ^ (K + 1) * uP) (j : Nat) :
    (2 : Int) ^ (j * P) = 1 + p ^ (K + 1) * Efun p K P j ∧ p ∣ Efun p K P j - (j : Int) * uP := by
  obtain ⟨z, hz⟩ := int_binom_quad (p ^ (K + 1) * uP) j
  have e1 : (2 : Int) ^ (j * P) = ((2 : Int) ^ P) ^ j := by rw [Nat.mul_comm, Int.pow_mul]
  have hz2 : (2 : Int) ^ (j * P)
      = 1 + (j : Int) * (p ^ (K + 1) * uP) + (p ^ (K + 1) * uP) ^ 2 * z := by
    rw [e1, h]; exact hz
  have hne : p ^ (K + 1) ≠ 0 := Int.pow_ne_zero hp
  have hid : 1 + (j : Int) * (p ^ (K + 1) * uP) + (p ^ (K + 1) * uP) ^ 2 * z
      = 1 + p ^ (K + 1) * ((j : Int) * uP + p ^ (K + 1) * (uP ^ 2 * z)) := by
    have e2 : ∀ x : Int, x ^ 2 = x * x := fun x => by rw [Int.pow_succ, Int.pow_one]
    rw [Int.mul_pow, e2 (p ^ (K + 1)), e2 uP]; int_ring
  have hpre : (2 : Int) ^ (j * P) - 1
      = p ^ (K + 1) * ((j : Int) * uP + p ^ (K + 1) * (uP ^ 2 * z)) := by
    rw [hz2, hid]; omega
  have hEf : Efun p K P j = (j : Int) * uP + p ^ (K + 1) * (uP ^ 2 * z) := by
    unfold Efun
    rw [hpre]
    exact Int.mul_ediv_cancel_left _ hne
  rw [hEf]
  refine ⟨?_, ?_⟩
  · rw [hz2, hid]
  · refine ⟨p ^ K * (uP ^ 2 * z), ?_⟩
    have e : p ^ (K + 1) = p ^ K * p := Int.pow_succ _ _
    rw [e]; int_ring

theorem dvd_triple_prod_sub (p a M X E c : Int) (hM : p ∣ M - a) (hX : p ∣ X - 1) (hE : p ∣ E - c) :
    p ∣ M * X * E - a * c := by
  obtain ⟨m, hm⟩ := hM
  obtain ⟨g, hg⟩ := hX
  obtain ⟨e, he⟩ := hE
  have hM' : M = a + p * m := by omega
  have hX' : X = 1 + p * g := by omega
  have hE' : E = c + p * e := by omega
  rw [hM', hX', hE']
  exact ⟨a * e + (a * g + m + p * m * g) * c + p * (a * g + m + p * m * g) * e, by int_ring⟩

theorem bsum_cong (p : Int) (P : Nat) (hG : ∀ j : Nat, p ∣ (2 : Int) ^ (j * P) - 1)
    (b J : Nat → Nat) (k : Nat) :
    ∀ i, p ∣ (2 : Int) ^ (bsum (fun l => b l + J l * P) k i) - 2 ^ (bsum b k i)
  | 0 => by simp [bsum]
  | i + 1 => by
    obtain ⟨g, hg⟩ := bsum_cong p P hG b J k i
    obtain ⟨w, hw⟩ := hG (J (k + i + 1))
    have e1 : (2 : Int) ^ (bsum (fun l => b l + J l * P) k (i + 1))
        = 2 ^ (bsum (fun l => b l + J l * P) k i) * (2 ^ (b (k + i + 1)) * 2 ^ (J (k + i + 1) * P)) := by
      show (2 : Int) ^ (bsum (fun l => b l + J l * P) k i + (b (k + i + 1) + J (k + i + 1) * P)) = _
      rw [Int.pow_add, Int.pow_add]
    have e2 : (2 : Int) ^ (bsum b k (i + 1)) = 2 ^ (bsum b k i) * 2 ^ (b (k + i + 1)) := by
      show (2 : Int) ^ (bsum b k i + b (k + i + 1)) = _
      rw [Int.pow_add]
    rw [e1, e2]
    generalize (2 : Int) ^ (bsum (fun l => b l + J l * P) k i) = X at *
    generalize (2 : Int) ^ (bsum b k i) = Y at *
    generalize (2 : Int) ^ (b (k + i + 1)) = Z at *
    generalize (2 : Int) ^ (J (k + i + 1) * P) = U at *
    have hU : U = 1 + p * w := by omega
    have hX : X = Y + p * g := by omega
    rw [hU, hX]
    exact ⟨Z * ((Y + p * g) * w + g), by int_ring⟩

theorem chain_diff_congr (p : Int) (hp : p ≠ 0) (K P : Nat) (uP : Int)
    (h2P : (2 : Int) ^ P = 1 + p ^ (K + 1) * uP)
    (b J J' : Nat → Nat) (y y' : Nat → Int) (k0 n : Nat)
    (hrel : ∀ i, i < n → p * y (i + 1) + 1 = 2 ^ (b (i + 1)) * 2 ^ (J (i + 1) * P) * y i)
    (hrel' : ∀ i, i < n → p * y' (i + 1) + 1 = 2 ^ (b (i + 1)) * 2 ^ (J' (i + 1) * P) * y' i)
    (hy : y' k0 = y k0) (hJ : J (k0 + 1) = 0) (hag : ∀ l, k0 + 1 < l → J' l = J l)
    (hx : p ∣ 2 ^ (b (k0 + 1)) * y k0 - 1) :
    ∀ i, i ≤ K → k0 + 1 + i ≤ n →
      p ^ (K - i + 1) ∣ (y' (k0 + 1 + i) - y (k0 + 1 + i))
        - p ^ (K - i) * (2 ^ (bsum b (k0 + 1) i) * ((J' (k0 + 1) : Nat) : Int) * uP) := by
  intro i hi hin
  obtain ⟨hE, hEc⟩ := Efun_spec p hp K P uP h2P (J' (k0 + 1))
  have hG : ∀ j : Nat, p ∣ (2 : Int) ^ (j * P) - 1 := fun j =>
    pow_mod_one_int p P j ⟨p ^ K * uP, by rw [h2P, Int.pow_succ]; int_ring⟩
  have ex := chain_diff_exact p hp K P (Efun p K P (J' (k0 + 1))) b J J' y y' k0 n hE hrel hrel' hy hJ hag i hin
  have pK : p ^ K = p ^ i * p ^ (K - i) := by
    rw [← Int.pow_add]; congr 1; omega
  have hδ : y' (k0 + 1 + i) - y (k0 + 1 + i)
      = p ^ (K - i) * (2 ^ (bsum (fun l => b l + J l * P) (k0 + 1) i)
          * (2 ^ (b (k0 + 1)) * y k0) * Efun p K P (J' (k0 + 1))) := by
    apply Int.eq_of_mul_eq_mul_left (Int.pow_ne_zero hp : p ^ i ≠ 0)
    rw [ex, pK]; int_ring
  obtain ⟨c, hc⟩ := dvd_triple_prod_sub p (2 ^ (bsum b (k0 + 1) i))
    (2 ^ (bsum (fun l => b l + J l * P) (k0 + 1) i)) (2 ^ (b (k0 + 1)) * y k0)
    (Efun p K P (J' (k0 + 1))) (((J' (k0 + 1) : Nat) : Int) * uP)
    (bsum_cong p P hG b J (k0 + 1) i) hx hEc
  refine ⟨c, ?_⟩
  have e3 : 2 ^ (bsum (fun l => b l + J l * P) (k0 + 1) i) * (2 ^ (b (k0 + 1)) * y k0)
      * Efun p K P (J' (k0 + 1))
      = 2 ^ (bsum b (k0 + 1) i) * (((J' (k0 + 1) : Nat) : Int) * uP) + p * c := by omega
  rw [hδ, e3, Int.pow_succ]
  int_ring

structure Setup (p : Int) (K P : Nat) (uP : Int) (b : Nat → Nat) (y0 c : Int) : Prop where
  hp : p ≠ 0
  h2P : (2 : Int) ^ P = 1 + p ^ (K + 1) * uP
  inv2 : ∃ t : Int, p ∣ 2 * t - 1
  invu : ∃ w : Int, p ∣ uP * w - 1
  hc : p ^ (K + 1) ∣ (2 - p) * c - 1
  hy0 : p ^ (K + 1) ∣ y0 - c
  hb1 : ∀ i, 1 ≤ i → i ≤ K + 1 → b i = 1

def chain (p : Int) (P : Nat) (y0 : Int) (b J : Nat → Nat) : Nat → Int
  | 0 => y0
  | i + 1 => ((2 : Int) ^ (b (i + 1)) * 2 ^ (J (i + 1) * P) * chain p P y0 b J i - 1) / p

def Integral (p : Int) (P : Nat) (y0 : Int) (b J : Nat → Nat) (n : Nat) : Prop :=
  ∀ i, i < n → p ∣ (2 : Int) ^ (b (i + 1)) * 2 ^ (J (i + 1) * P) * chain p P y0 b J i - 1

theorem chain_rel {p : Int} {P : Nat} {y0 : Int} {b J : Nat → Nat} {n : Nat}
    (h : Integral p P y0 b J n) : ∀ i, i < n →
    p * chain p P y0 b J (i + 1) + 1
      = 2 ^ (b (i + 1)) * 2 ^ (J (i + 1) * P) * chain p P y0 b J i := by
  intro i hi
  have e := Int.mul_ediv_cancel' (h i hi)
  show p * (((2 : Int) ^ (b (i + 1)) * 2 ^ (J (i + 1) * P) * chain p P y0 b J i - 1) / p) + 1 = _
  rw [e]; omega

theorem chain_congr (p : Int) (P : Nat) (y0 : Int) (b J J' : Nat → Nat) :
    ∀ i, (∀ l, 1 ≤ l → l ≤ i → J l = J' l) → chain p P y0 b J i = chain p P y0 b J' i
  | 0, _ => rfl
  | i + 1, H => by
    have ih := chain_congr p P y0 b J J' i (fun l h1 h2 => H l h1 (by omega))
    show ((2 : Int) ^ (b (i + 1)) * 2 ^ (J (i + 1) * P) * chain p P y0 b J i - 1) / p
      = ((2 : Int) ^ (b (i + 1)) * 2 ^ (J' (i + 1) * P) * chain p P y0 b J' i - 1) / p
    rw [ih, H (i + 1) (by omega) (by omega)]

theorem step_int_iff (p : Int) (P : Nat) (bb y : Int) (j : Nat)
    (hG : p ∣ (2 : Int) ^ (j * P) - 1) :
    p ∣ bb * 2 ^ (j * P) * y - 1 ↔ p ∣ bb * y - 1 := by
  obtain ⟨w, hw⟩ := hG
  have hU : (2 : Int) ^ (j * P) = 1 + p * w := by omega
  rw [hU]
  have e : bb * (1 + p * w) * y = bb * y + p * (bb * y * w) := by int_ring
  rw [e]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g - bb * y * w, by rw [Int.mul_sub]; omega⟩
  · rintro ⟨g, hg⟩
    exact ⟨g + bb * y * w, by rw [Int.mul_add]; omega⟩

theorem Gdiv {p : Int} {K P : Nat} {uP : Int} {b : Nat → Nat} {y0 c : Int}
    (S : Setup p K P uP b y0 c) (j : Nat) : p ∣ (2 : Int) ^ (j * P) - 1 :=
  pow_mod_one_int p P j ⟨p ^ K * uP, by rw [S.h2P, Int.pow_succ]; int_ring⟩

theorem integral_transfer {p : Int} {K P : Nat} {uP : Int} {b : Nat → Nat} {y0 c : Int}
    (S : Setup p K P uP b y0 c) (J J' : Nat → Nat) (m : Nat)
    (hag : ∀ l, 1 ≤ l → l ≤ m → J l = J' l) :
    ∀ n, n ≤ m + K + 1 → Integral p P y0 b J n → Integral p P y0 b J' n := by
  intro n
  induction n with
  | zero => intro _ _ i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    intro hn hI
    have hI0 : Integral p P y0 b J n := fun i hi => hI i (by omega)
    have hI0' := ih (by omega) hI0
    intro i hi
    rcases Nat.lt_or_ge i n with h | h
    · exact hI0' i h
    · have hin : i = n := by omega
      subst hin
      have hs := (step_int_iff p P _ _ _ (Gdiv S (J (i + 1)))).1 (hI i (by omega))
      have hloc := locality p S.hp K P (Efun p K P)
        (fun j => (Efun_spec p S.hp K P uP S.h2P j).1) b J J'
        (chain p P y0 b J) (chain p P y0 b J') i rfl
        (chain_rel hI0) (chain_rel hI0') i (Nat.le_refl i) 1
        (fun l hl hl2 => hag l hl (by omega))
      rw [Int.pow_one] at hloc
      refine (step_int_iff p P _ _ _ (Gdiv S (J' (i + 1)))).2 ?_
      obtain ⟨g1, hg1⟩ := hs
      obtain ⟨g2, hg2⟩ := hloc
      refine ⟨g1 + 2 ^ (b (i + 1)) * g2, ?_⟩
      have h3 : chain p P y0 b J' i = chain p P y0 b J i + p * g2 := by omega
      rw [h3]
      generalize chain p P y0 b J i = Y at *
      have e : (2 : Int) ^ (b (i + 1)) * (Y + p * g2) - 1
          = ((2 : Int) ^ (b (i + 1)) * Y - 1) + p * ((2 : Int) ^ (b (i + 1)) * g2) := by int_ring
      rw [e, hg1]; int_ring

theorem inv_mul (p X Xi Y Yi : Int) (hX : p ∣ X * Xi - 1) (hY : p ∣ Y * Yi - 1) :
    p ∣ (X * Y) * (Xi * Yi) - 1 := by
  obtain ⟨g1, h1⟩ := hX
  obtain ⟨g2, h2⟩ := hY
  have e : (X * Y) * (Xi * Yi) = (X * Xi) * (Y * Yi) := by int_ring
  have h1' : X * Xi = 1 + p * g1 := by omega
  have h2' : Y * Yi = 1 + p * g2 := by omega
  rw [e, h1', h2']
  exact ⟨g1 * (1 + p * g2) + g2, by int_ring⟩

theorem inv_pow2 {p : Int} {K P : Nat} {uP : Int} {b : Nat → Nat} {y0 c : Int}
    (S : Setup p K P uP b y0 c) : ∀ e : Nat, ∃ ti : Int, p ∣ (2 : Int) ^ e * ti - 1
  | 0 => ⟨1, by rw [Int.pow_zero]; simp⟩
  | e + 1 => by
    obtain ⟨ti, h1⟩ := inv_pow2 S e
    obtain ⟨t, ht⟩ := S.inv2
    refine ⟨t * ti, ?_⟩
    have e1 : (2 : Int) ^ (e + 1) * (t * ti) = (2 * 2 ^ e) * (t * ti) := by
      rw [Int.pow_succ, Int.mul_comm ((2 : Int) ^ e) 2]
    rw [e1]
    exact inv_mul p 2 t (2 ^ e) ti ht h1

theorem inv_a1 {p : Int} {K P : Nat} {uP : Int} {b : Nat → Nat} {y0 c : Int}
    (S : Setup p K P uP b y0 c) (e : Nat) : ∃ ai : Int, p ∣ ((2 : Int) ^ e * uP) * ai - 1 := by
  obtain ⟨ti, h1⟩ := inv_pow2 S e
  obtain ⟨w, hw⟩ := S.invu
  exact ⟨ti * w, inv_mul p _ ti uP w h1 hw⟩

theorem lin_solve (q : Nat) (hq : 0 < q) (a w c : Int) (hw : (q : Int) ∣ a * w - 1) :
    ∃ j : Nat, j < q ∧ (q : Int) ∣ a * (j : Int) - c := by
  have hq' : (0 : Int) < (q : Int) := by omega
  have h1 : 0 ≤ (w * c) % (q : Int) := Int.emod_nonneg _ (by omega)
  have h2 : (w * c) % (q : Int) < (q : Int) := Int.emod_lt_of_pos _ hq'
  refine ⟨((w * c) % (q : Int)).toNat, by omega, ?_⟩
  have e : ((((w * c) % (q : Int)).toNat : Nat) : Int) = (w * c) % (q : Int) := Int.toNat_of_nonneg h1
  rw [e, Int.emod_def]
  obtain ⟨g, hg⟩ := hw
  generalize w * c / (q : Int) = t
  have e1 : a * (w * c - (q : Int) * t) - c = (a * w - 1) * c - (q : Int) * (a * t) := by int_ring
  rw [e1, hg]
  exact ⟨c * g - a * t, by int_ring⟩

theorem primer_step {p : Int} {K P : Nat} {uP : Int} {b : Nat → Nat} {y0 c : Int}
    (S : Setup p K P uP b y0 c) (J : Nat → Nat) (i : Nat) (hi : i ≤ K)
    (hd : p ^ (K + 1 - i) ∣ chain p P y0 b J i - c) :
    p ∣ (2 : Int) ^ (b (i + 1)) * 2 ^ (J (i + 1) * P) * chain p P y0 b J i - 1 ∧
    p ^ (K - i) ∣ chain p P y0 b J (i + 1) - c := by
  have hb : b (i + 1) = 1 := S.hb1 (i + 1) (by omega) (by omega)
  obtain ⟨g, hg⟩ := hd
  have hGK : p ^ (K + 1) ∣ (2 : Int) ^ (J (i + 1) * P) - 1 :=
    pow_mod_one_int (p ^ (K + 1)) P (J (i + 1)) ⟨uP, by rw [S.h2P]; omega⟩
  obtain ⟨w, hw⟩ := Int.dvd_trans (ipow_dvd p (by omega : K + 1 - i ≤ K + 1)) hGK
  have hYc : p ^ (K + 1 - i) ∣ (2 : Int) ^ (J (i + 1) * P) * chain p P y0 b J i - c := by
    have hid : (2 : Int) ^ (J (i + 1) * P) * chain p P y0 b J i - c
        = (2 : Int) ^ (J (i + 1) * P) * (chain p P y0 b J i - c)
          + ((2 : Int) ^ (J (i + 1) * P) - 1) * c := by int_ring
    rw [hid]
    exact ⟨(2 : Int) ^ (J (i + 1) * P) * g + w * c, by rw [hg, hw]; int_ring⟩
  obtain ⟨z, hz1, hz2⟩ := fp_step p K (K + 1 - i) (by omega)
    (by omega) c _ S.hc hYc
  have hnum : (2 : Int) ^ (b (i + 1)) * 2 ^ (J (i + 1) * P) * chain p P y0 b J i - 1 = p * z := by
    rw [hb, Int.pow_one]; rw [← hz1]; int_ring
  refine ⟨⟨z, hnum⟩, ?_⟩
  have hch : chain p P y0 b J (i + 1) = z := by
    show ((2 : Int) ^ (b (i + 1)) * 2 ^ (J (i + 1) * P) * chain p P y0 b J i - 1) / p = z
    rw [hnum]; exact Int.mul_ediv_cancel_left _ S.hp
  rw [hch]
  have hj2 : K + 1 - i - 1 = K - i := by omega
  rw [hj2] at hz2
  exact hz2

theorem primer_chain {p : Int} {K P : Nat} {uP : Int} {b : Nat → Nat} {y0 c : Int}
    (S : Setup p K P uP b y0 c) (J : Nat → Nat) :
    (∀ i, i ≤ K → p ^ (K + 1 - i) ∣ chain p P y0 b J i - c) ∧ Integral p P y0 b J (K + 1) := by
  have h1 : ∀ i, i ≤ K → p ^ (K + 1 - i) ∣ chain p P y0 b J i - c := by
    intro i
    induction i with
    | zero => intro _; exact S.hy0
    | succ i ih =>
      intro hi
      have hs := (primer_step S J i (by omega) (ih (by omega))).2
      have hj : K + 1 - (i + 1) = K - i := by omega
      rw [hj]; exact hs
  exact ⟨h1, fun i hi => (primer_step S J i (by omega) (h1 i (by omega))).1⟩

theorem lift_digit_identity (Z p A j Y0 Y1 ρ θ g h1 : Int)
    (hg : Y1 - Y0 - Z * (A * j) = Z * p * g) (hθ : Y0 - ρ = Z * θ)
    (hh : A * j + θ = p * h1) : Y1 - ρ = Z * p * (g + h1) := by
  have h2 : Z * (A * j + θ) = Z * (p * h1) := by rw [hh]
  have e1 : Z * (A * j + θ) = Z * (A * j) + Z * θ := by int_ring
  have e2 : Z * p * (g + h1) = Z * p * g + Z * (p * h1) := by int_ring
  rw [e2]; omega

theorem choose_shifts {p : Int} {K P : Nat} {uP : Int} {b : Nat → Nat} {y0 c : Int}
    (q : Nat) (hq : 0 < q) (hpq : p = (q : Int)) (S : Setup p K P uP b y0 c) (τ : Nat) (ρ : Int) :
    ∃ f : Nat → Nat, (∀ l, 1 ≤ l → l ≤ K + τ → f l < q) ∧
      ∀ J : Nat → Nat, (∀ l, 1 ≤ l → l ≤ K + τ → J l = f l) →
        Integral p P y0 b J (K + 1 + τ) ∧ p ^ K ∣ chain p P y0 b J (K + 1 + τ) - ρ := by
  have lin' : ∀ a ai c' : Int, p ∣ a * ai - 1 → ∃ j : Nat, j < q ∧ p ∣ a * (j : Int) - c' := by
    intro a ai c' h
    subst hpq
    exact lin_solve q hq a ai c' h
  have hEf : ∀ j : Nat, (2 : Int) ^ (j * P) = 1 + p ^ (K + 1) * Efun p K P j :=
    fun j => (Efun_spec p S.hp K P uP S.h2P j).1
  have key : ∀ k, k ≤ K + τ → ∃ f : Nat → Nat, (∀ l, 1 ≤ l → l ≤ k → f l < q) ∧
      ∀ J : Nat → Nat, (∀ l, 1 ≤ l → l ≤ k → J l = f l) →
        Integral p P y0 b J (min (k + K + 1) (K + 1 + τ)) ∧
        p ^ (k - τ) ∣ chain p P y0 b J (K + 1 + τ) - ρ := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun _ => 0, fun l _ h2 => absurd h2 (by omega), ?_⟩
      intro J _
      refine ⟨?_, ?_⟩
      · have hi : min (0 + K + 1) (K + 1 + τ) = K + 1 := by omega
        rw [hi]; exact (primer_chain S J).2
      · have h0 : 0 - τ = 0 := by omega
        rw [h0, Int.pow_zero]; exact Int.one_dvd _
    | succ k0 ih =>
      intro hk
      obtain ⟨f, hfb, hf⟩ := ih (by omega)
      obtain ⟨J0, hJ0⟩ : ∃ J0 : Nat → Nat, J0 = fun l => if l ≤ k0 then f l else 0 := ⟨_, rfl⟩
      have hJ0a : ∀ l, l ≤ k0 → J0 l = f l := by intro l h; rw [hJ0]; simp [h]
      have hJ0b : ∀ l, k0 < l → J0 l = 0 := by intro l h; rw [hJ0]; simp [Nat.not_le.2 h]
      obtain ⟨hI0, hC0⟩ := hf J0 (fun l _ h => hJ0a l h)
      have hJ0k : J0 (k0 + 1) = 0 := hJ0b _ (by omega)
      obtain ⟨J1, hJ1⟩ : ∃ J1 : Nat → Nat → Nat,
          J1 = fun j l => if l = k0 + 1 then j else J0 l := ⟨_, rfl⟩
      have hJ1a : ∀ j, J1 j (k0 + 1) = j := by intro j; rw [hJ1]; simp
      have hJ1b : ∀ j l, l ≠ k0 + 1 → J1 j l = J0 l := by intro j l h; rw [hJ1]; simp [h]
      have hJ1c : ∀ j l, l ≤ k0 → J1 j l = f l := by
        intro j l h; rw [hJ1b j l (by omega), hJ0a l h]
      obtain ⟨F, hF⟩ : ∃ F : Nat → Nat → Nat, F = fun j l => if l = k0 + 1 then j else f l := ⟨_, rfl⟩
      have hFa : ∀ j, F j (k0 + 1) = j := by intro j; rw [hF]; simp
      have hFb : ∀ j l, l ≠ k0 + 1 → F j l = f l := by intro j l h; rw [hF]; simp [h]
      have hFq : ∀ j, j < q → ∀ l, 1 ≤ l → l ≤ k0 + 1 → F j l < q := by
        intro j hj l h1 h2
        by_cases hl : l = k0 + 1
        · subst hl; rw [hFa]; exact hj
        · rw [hFb j l hl]; exact hfb l h1 (by omega)
      have hag : ∀ j (J : Nat → Nat), (∀ l, 1 ≤ l → l ≤ k0 + 1 → J l = F j l) →
          ∀ l, 1 ≤ l → l ≤ k0 + 1 → J1 j l = J l := by
        intro j J hJ l h1 h2
        rw [hJ l h1 h2]
        by_cases hl : l = k0 + 1
        · subst hl; rw [hJ1a, hFa]
        · rw [hJ1c j l (by omega), hFb j l hl]
      have hIJ1 : ∀ j, Integral p P y0 b (J1 j) (min (k0 + K + 1) (K + 1 + τ)) := fun j =>
        integral_transfer S J0 (J1 j) k0 (fun l _ h => (hJ1b j l (by omega)).symm) _
          (by omega) hI0
      have hx : p ∣ (2 : Int) ^ (b (k0 + 1)) * chain p P y0 b J0 k0 - 1 := by
        have h := hI0 k0 (by omega)
        rw [hJ0k, Nat.zero_mul, Int.pow_zero, Int.mul_one] at h
        exact h
      have hrel0 := chain_rel hI0
      have hy1 : ∀ j, chain p P y0 b (J1 j) k0 = chain p P y0 b J0 k0 :=
        fun j => chain_congr p P y0 b (J1 j) J0 k0 (fun l _ h => by rw [hJ1b j l (by omega)])
      have shift : ∀ j i, i ≤ K → k0 + 1 + i ≤ min (k0 + K + 1) (K + 1 + τ) →
          p ^ (K - i + 1) ∣ (chain p P y0 b (J1 j) (k0 + 1 + i) - chain p P y0 b J0 (k0 + 1 + i))
            - p ^ (K - i) * (2 ^ (bsum b (k0 + 1) i) * (j : Int) * uP) := by
        intro j i hi hin
        have h := chain_diff_congr p S.hp K P uP S.h2P b J0 (J1 j) (chain p P y0 b J0)
          (chain p P y0 b (J1 j)) k0 (min (k0 + K + 1) (K + 1 + τ)) hrel0
          (chain_rel (hIJ1 j)) (hy1 j) hJ0k (fun l hl => hJ1b j l (by omega)) hx i hi hin
        rw [hJ1a j] at h
        exact h
      rcases Nat.lt_or_ge τ (k0 + 1) with hB | hA
      ·
        have hn : min (k0 + K + 1) (K + 1 + τ) = K + 1 + τ := by omega
        have hIs : Integral p P y0 b J0 (K + 1 + τ) := by rw [hn] at hI0; exact hI0
        have hIJ1s : ∀ j, Integral p P y0 b (J1 j) (K + 1 + τ) := fun j => by
          have := hIJ1 j; rw [hn] at this; exact this
        have hsh : ∀ j, p ^ (k0 - τ + 1) ∣
            (chain p P y0 b (J1 j) (K + 1 + τ) - chain p P y0 b J0 (K + 1 + τ))
              - p ^ (k0 - τ) * (2 ^ (bsum b (k0 + 1) (K + 1 + τ - (k0 + 1))) * (j : Int) * uP) := by
          intro j
          have h := shift j (K + 1 + τ - (k0 + 1)) (by omega) (by omega)
          have e1 : K - (K + 1 + τ - (k0 + 1)) = k0 - τ := by omega
          have e3 : k0 + 1 + (K + 1 + τ - (k0 + 1)) = K + 1 + τ := by omega
          rw [e1, e3] at h
          exact h
        obtain ⟨θ, hθ⟩ := hC0
        obtain ⟨ai, hai⟩ := inv_a1 S (bsum b (k0 + 1) (K + 1 + τ - (k0 + 1)))
        obtain ⟨j, hjq, hj⟩ := lin' _ ai (-θ) hai
        obtain ⟨h1, hh1⟩ := hj
        obtain ⟨g, hg⟩ := hsh j
        have eA : (2 : Int) ^ (bsum b (k0 + 1) (K + 1 + τ - (k0 + 1))) * (j : Int) * uP
            = ((2 : Int) ^ (bsum b (k0 + 1) (K + 1 + τ - (k0 + 1))) * uP) * (j : Int) := by int_ring
        rw [eA, Int.pow_succ] at hg
        have hC := lift_digit_identity (p ^ (k0 - τ)) p
          ((2 : Int) ^ (bsum b (k0 + 1) (K + 1 + τ - (k0 + 1))) * uP) (j : Int)
          (chain p P y0 b J0 (K + 1 + τ)) (chain p P y0 b (J1 j) (K + 1 + τ)) ρ θ g h1
          hg hθ (by omega)
        refine ⟨F j, hFq j hjq, ?_⟩
        intro J hJ
        have hagJ := hag j J hJ
        have hIJ : Integral p P y0 b J (K + 1 + τ) :=
          integral_transfer S (J1 j) J (k0 + 1) hagJ (K + 1 + τ) (by omega) (hIJ1s j)
        have hmin : min (k0 + 1 + K + 1) (K + 1 + τ) = K + 1 + τ := by omega
        refine ⟨by rw [hmin]; exact hIJ, ?_⟩
        have hloc := locality p S.hp K P (Efun p K P) hEf b (J1 j) J
          (chain p P y0 b (J1 j)) (chain p P y0 b J) (K + 1 + τ) rfl
          (chain_rel (hIJ1s j)) (chain_rel hIJ) (K + 1 + τ) (Nat.le_refl _) (k0 - τ + 1)
          (fun l hl hl2 => hagJ l hl (by omega))
        obtain ⟨g', hg'⟩ := hloc
        have e : k0 + 1 - τ = k0 - τ + 1 := by omega
        rw [e]
        have e2 : p ^ (k0 - τ + 1) = p ^ (k0 - τ) * p := Int.pow_succ _ _
        rw [e2] at hg' ⊢
        refine ⟨g' + (g + h1), ?_⟩
        rw [Int.mul_add]
        omega
      ·
        have hn : min (k0 + K + 1) (K + 1 + τ) = k0 + K + 1 := by omega
        obtain ⟨ai, hai⟩ := inv_a1 S (bsum b (k0 + 1) K)
        obtain ⟨at', hat'⟩ := inv_pow2 S (b (k0 + 1 + K + 1))
        have hinv : p ∣ ((2 : Int) ^ (b (k0 + 1 + K + 1))
            * ((2 : Int) ^ (bsum b (k0 + 1) K) * uP)) * (at' * ai) - 1 :=
          inv_mul p _ at' _ ai hat' hai
        obtain ⟨j, hjq, hj⟩ := lin' _ _ (1 - (2 : Int) ^ (b (k0 + 1 + K + 1))
          * chain p P y0 b J0 (k0 + 1 + K)) hinv
        obtain ⟨h1, hh1⟩ := hj
        have hsh := shift j K (Nat.le_refl K) (by omega)
        rw [Nat.sub_self, Nat.zero_add, Int.pow_one, Int.pow_zero, Int.one_mul] at hsh
        obtain ⟨g, hg⟩ := hsh
        have hy1eq : chain p P y0 b (J1 j) (k0 + 1 + K)
            = chain p P y0 b J0 (k0 + 1 + K)
              + (2 : Int) ^ (bsum b (k0 + 1) K) * (j : Int) * uP + p * g := by omega
        have hstep : p ∣ (2 : Int) ^ (b (k0 + 1 + K + 1)) * chain p P y0 b (J1 j) (k0 + 1 + K) - 1 := by
          refine ⟨h1 + (2 : Int) ^ (b (k0 + 1 + K + 1)) * g, ?_⟩
          rw [Int.mul_add, ← hh1, hy1eq]
          int_ring
        have hIn : Integral p P y0 b (J1 j) (k0 + K + 2) := by
          intro i hi
          rcases Nat.lt_or_ge i (k0 + K + 1) with h | h
          · have := hIJ1 j i (by omega); exact this
          · have hi' : i = k0 + 1 + K := by omega
            subst hi'
            exact (step_int_iff p P _ _ _ (Gdiv S (J1 j (k0 + 1 + K + 1)))).2 hstep
        refine ⟨F j, hFq j hjq, ?_⟩
        intro J hJ
        have hagJ := hag j J hJ
        refine ⟨?_, ?_⟩
        · have hmin : min (k0 + 1 + K + 1) (K + 1 + τ) = k0 + K + 2 := by omega
          rw [hmin]
          exact integral_transfer S (J1 j) J (k0 + 1) hagJ (k0 + K + 2) (by omega) hIn
        · have h0 : k0 + 1 - τ = 0 := by omega
          rw [h0, Int.pow_zero]; exact Int.one_dvd _
  obtain ⟨f, hfb, hf⟩ := key (K + τ) (Nat.le_refl _)
  refine ⟨f, hfb, fun J hJ => ?_⟩
  obtain ⟨h1, h2⟩ := hf J hJ
  have e1 : min (K + τ + K + 1) (K + 1 + τ) = K + 1 + τ := by omega
  have e2 : K + τ - τ = K := by omega
  rw [e1] at h1; rw [e2] at h2
  exact ⟨h1, h2⟩


end Collatz
