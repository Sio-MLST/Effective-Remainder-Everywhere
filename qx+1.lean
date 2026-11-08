
namespace Collatz

def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + n

theorem triangle_two (n : Nat) : 2 * triangle n = n * (n - 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show 2 * (triangle n + n) = (n + 1) * n
    rw [Nat.mul_add, ih]; cases n with
    | zero => rfl
    | succ n => simp; grind

theorem binom_cubic (a : Nat) : ∀ n, ∃ z, (1 + a) ^ n = 1 + n * a + triangle n * a ^ 2 + a ^ 3 * z
  | 0 => ⟨0, by simp [triangle]⟩
  | n + 1 => by
    obtain ⟨z, hz⟩ := binom_cubic a n
    refine ⟨triangle n + z + z * a, ?_⟩
    rw [Nat.pow_succ, hz]; show _ = 1 + (n + 1) * a + (triangle n + n) * a ^ 2 + a ^ 3 * (triangle n + z + z * a)
    grind

theorem binom_quadratic (a : Nat) : ∀ n, ∃ z, (1 + a) ^ n = 1 + n * a + a ^ 2 * z := by
  intro n; obtain ⟨z, hz⟩ := binom_cubic a n
  exact ⟨triangle n + a * z, by rw [hz]; grind⟩

theorem lift_step {q j u : Nat} (hp : q % 2 = 1) (hj : 1 ≤ j) (hu : Nat.Coprime q u) :
    ∃ w, Nat.Coprime q w ∧ (1 + q ^ j * u) ^ q = 1 + q ^ (j + 1) * w := by
  obtain ⟨z, hz⟩ := binom_cubic (q ^ j * u) q
  obtain ⟨h, hh⟩ : ∃ h, triangle q = q * h := by
    refine ⟨(q - 1) / 2, ?_⟩
    have := triangle_two q
    have : (q - 1) % 2 = 0 := by omega
    have e : q - 1 = 2 * ((q - 1) / 2) := by omega
    rw [e] at *; grind
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  let w := u + q * (h * q ^ k * u ^ 2 + q ^ (2 * k) * u ^ 3 * z)
  refine ⟨w, ?_, ?_⟩
  · show Nat.Coprime q (u + q * _)
    rw [Nat.Coprime, Nat.gcd_add_mul_left_right]; exact hu
  · rw [hz, hh]
    show _ = 1 + q ^ (k + 1 + 1) * (u + q * (h * q ^ k * u ^ 2 + q ^ (2 * k) * u ^ 3 * z))
    have e1 : q ^ (k + 1 + 1) = q * q * q ^ k := by rw [Nat.pow_succ, Nat.pow_succ]; grind
    have e2 : q ^ (k + 1) = q * q ^ k := by rw [Nat.pow_succ]; grind
    have e3 : q ^ (2 * k) = q ^ k * q ^ k := by rw [Nat.two_mul, Nat.pow_add]
    rw [e1, e2, e3]; generalize q ^ k = A; grind

theorem lift_exponent {q u : Nat} (hp : q % 2 = 1) (hu : Nat.Coprime q u) :
    ∀ n, ∃ w, Nat.Coprime q w ∧ (1 + q * u) ^ (q ^ n) = 1 + q ^ (n + 1) * w
  | 0 => ⟨u, hu, by simp⟩
  | n + 1 => by
    obtain ⟨w, hw, hx⟩ := lift_exponent hp hu n
    obtain ⟨w', hw', hx'⟩ := lift_step (j := n + 1) hp (by omega) hw
    exact ⟨w', hw', by rw [Nat.pow_succ, Nat.pow_mul, hx, hx']⟩

theorem order_iff {q u : Nat} (hp : q % 2 = 1) (hp3 : 3 ≤ q) (hu : Nat.Coprime q u) :
    ∀ K m, (1 + q * u) ^ m % q ^ (K + 1) = 1 ↔ q ^ K ∣ m := by
  have hP : ∀ K, 1 < q ^ (K + 1) := fun K =>
    Nat.lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) q)
  intro K
  induction K with
  | zero =>
    intro m
    obtain ⟨z, hz⟩ := binom_quadratic (q * u) m
    simp only [Nat.pow_zero, Nat.one_dvd, iff_true, Nat.zero_add, Nat.pow_one]
    rw [hz, show 1 + m * (q * u) + (q * u) ^ 2 * z = 1 + q * (m * u + q * u ^ 2 * z) by grind,
      Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)
  | succ K ih =>
    intro m
    constructor
    · intro h
      have h1 : (1 + q * u) ^ m % q ^ (K + 1) = 1 := by
        rw [← Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow q (by omega : K + 1 ≤ K + 1 + 1)), h]
        exact Nat.mod_eq_of_lt (hP K)
      obtain ⟨k, rfl⟩ := (ih m).1 h1
      by_cases hpk : q ∣ k
      · obtain ⟨k', rfl⟩ := hpk; exact ⟨k', by rw [Nat.pow_succ]; grind⟩
      · exfalso
        obtain ⟨w, hw, hx⟩ := lift_exponent hp hu K
        obtain ⟨z, hz⟩ := binom_quadratic (q ^ (K + 1) * w) k
        rw [Nat.pow_mul, hx, hz,
          show 1 + k * (q ^ (K + 1) * w) + (q ^ (K + 1) * w) ^ 2 * z
            = 1 + q ^ (K + 1) * (k * w + q ^ (K + 1) * (w ^ 2 * z)) by grind,
          show q ^ (K + 1 + 1) = q ^ (K + 1) * q by rw [Nat.pow_succ]] at h
        have hd : q ^ (K + 1) * q ∣ q ^ (K + 1) * (k * w + q ^ (K + 1) * (w ^ 2 * z)) := by
          have h2 := Nat.sub_mod_eq_zero_of_mod_eq
            (h.trans (Nat.mod_eq_of_lt (by have := hP (K + 1); rwa [Nat.pow_succ] at this)).symm)
          simpa using Nat.dvd_of_mod_eq_zero h2
        have hd2 := Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos (by omega)) hd
        have hd3 : q ∣ q ^ (K + 1) * (w ^ 2 * z) :=
          Nat.dvd_trans ⟨q ^ K, by rw [Nat.pow_succ, Nat.mul_comm]⟩ (Nat.dvd_mul_right _ _)
        have hkw : q ∣ k * w := (Nat.dvd_add_left hd3).1 hd2
        exact hpk (Nat.Coprime.dvd_of_dvd_mul_right hw hkw)
    · rintro ⟨k, rfl⟩
      obtain ⟨w, hw, hx⟩ := lift_exponent hp hu (K + 1)
      rw [Nat.pow_mul, hx, Nat.pow_mod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hP _),
        Nat.one_pow, Nat.mod_eq_of_lt (hP _)]

theorem coprime_two_of_odd {q : Nat} (hp : q % 2 = 1) : Nat.Coprime q 2 := by
  unfold Nat.Coprime; rw [Nat.gcd_comm, Nat.gcd_rec, hp]; rfl

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

theorem coprime_of_mod_one {q x : Nat} (h : x % q = 1) : Nat.Coprime q x := by
  unfold Nat.Coprime; rw [Nat.gcd_rec, h, Nat.gcd_one_left]

theorem pow_mod_one {q x : Nat} (hp : 2 ≤ q) (h : x % q = 1) (t : Nat) : x ^ t % q = 1 := by
  rw [Nat.pow_mod, h, Nat.one_pow]; exact Nat.mod_eq_of_lt (by omega)

theorem unit_power_cover {q u : Nat} (hp : q % 2 = 1) (hp3 : 3 ≤ q) (hu : Nat.Coprime q u)
    (K x : Nat) (hx : x % q = 1) : ∃ t, t < q ^ K ∧ (1 + q * u) ^ t % q ^ (K + 1) = x % q ^ (K + 1) := by
  apply Classical.byContradiction
  intro hno
  have hP : 0 < q ^ (K + 1) := Nat.pow_pos (by omega)
  have hpK : 0 < q ^ K := Nat.pow_pos (by omega)
  have hPe : q ^ (K + 1) = q * q ^ K := by rw [Nat.pow_succ, Nat.mul_comm]
  have hdv : q ∣ q ^ (K + 1) := ⟨q ^ K, hPe⟩
  have hc1 : (1 + q * u) % q = 1 := by rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)
  have hcop : Nat.Coprime (q ^ (K + 1)) (1 + q * u) := Nat.Coprime.pow_left _ (coprime_of_mod_one hc1)
  let U : List Nat := (List.range (q ^ (K + 1))).filter (fun y => decide (y % q = 1))
  let L1 : List Nat := (List.range (q ^ K)).map (fun t => (1 + q * u) ^ t % q ^ (K + 1))
  have hUnodup : U.Nodup := List.Pairwise.filter _ List.nodup_range
  have key : ∀ a b, a ≤ b → b < q ^ K →
      (1 + q * u) ^ a % q ^ (K + 1) = (1 + q * u) ^ b % q ^ (K + 1) → a = b := by
    intro a b hab hb h
    have hb' : (1 + q * u) ^ b = (1 + q * u) ^ a * (1 + q * u) ^ (b - a) := by
      rw [← Nat.pow_add]; congr 1; omega
    have h' : ((1 + q * u) ^ a * (1 + q * u) ^ (b - a)) % q ^ (K + 1)
        = ((1 + q * u) ^ a * 1) % q ^ (K + 1) := by rw [← hb', Nat.mul_one]; exact h.symm
    have h'' := mod_cancel_mul_left (Nat.Coprime.pow_right a hcop)
      (Nat.pow_pos (Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_add_right 1 _))) h'
    have h1P : 1 % q ^ (K + 1) = 1 :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) q))
    rw [h1P] at h''
    have hd := (order_iff hp hp3 hu K (b - a)).1 h''
    have : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  have hL1nodup : L1.Nodup := by
    apply List.pairwise_map.2
    apply List.Pairwise.imp_of_mem _ List.nodup_range
    intro a b ha hb hab heq
    rw [List.mem_range] at ha hb
    rcases Nat.le_total a b with hle | hle
    · exact hab (key a b hle hb heq)
    · exact hab (key b a hle ha heq.symm).symm
  have hL1U : L1 ⊆ U := by
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨t, _, rfl⟩ := hy
    rw [List.mem_filter, List.mem_range]
    refine ⟨Nat.mod_lt _ hP, ?_⟩
    rw [Nat.mod_mod_of_dvd _ hdv, pow_mod_one (by omega) hc1]; simp
  have hxU : x % q ^ (K + 1) ∈ U := by
    rw [List.mem_filter, List.mem_range]
    refine ⟨Nat.mod_lt _ hP, ?_⟩
    rw [Nat.mod_mod_of_dvd _ hdv, hx]; simp
  have hxL : x % q ^ (K + 1) ∉ L1 := by
    intro h; rw [List.mem_map] at h
    obtain ⟨t, ht, he⟩ := h
    exact hno ⟨t, List.mem_range.1 ht, he⟩
  have hsub : (x % q ^ (K + 1) :: L1) ⊆ U := by
    intro y hy
    rcases List.mem_cons.1 hy with h | h
    · rw [h]; exact hxU
    · exact hL1U h
  have hlen1 := (List.nodup_cons.2 ⟨hxL, hL1nodup⟩).length_le_of_subset hsub
  have hUsub : U ⊆ (List.range (q ^ K)).map (fun j => q * j + 1) := by
    intro y hy
    rw [List.mem_filter, List.mem_range] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have hy2' : y % q = 1 := by simpa using hy2
    rw [List.mem_map]
    refine ⟨y / q, List.mem_range.2 ((Nat.div_lt_iff_lt_mul (by omega)).2 (by rw [← hPe, Nat.mul_comm] at *; rw [Nat.mul_comm]; rwa [hPe] at hy1)), ?_⟩
    have := Nat.div_add_mod y q; omega
  have hlen2 : U.length ≤ q ^ K := by
    have := hUnodup.length_le_of_subset hUsub; simpa using this
  have hL1len : L1.length = q ^ K := by simp [L1]
  simp only [List.length_cons] at hlen1
  omega

section Map
variable (q : Nat)

def collatz (n : Nat) : Nat := if n % 2 = 0 then n / 2 else q * n + 1

def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter f k (f n)

theorem iter_add (f : Nat → Nat) (m n : Nat) : ∀ x, iter f (m + n) x = iter f m (iter f n x) := by
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; exact ih (f x)

def Reaches (n v : Nat) : Prop := ∃ k, iter (collatz q) k n = v

theorem collatz_double (a : Nat) : collatz q (2 * a) = a := by
  unfold collatz; split <;> omega

theorem reaches_trans {a b c : Nat} (h1 : Reaches q a b) (h2 : Reaches q b c) : Reaches q a c := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  exact ⟨k2 + k1, by rw [iter_add, hk1, hk2]⟩

end Map

class NonWieferich (q : Nat) : Prop where
  one_lt : 1 < q
  unit : ∃ d u, 2 ^ d = 1 + q * u ∧ Nat.Coprime q u

theorem pow_mod_period {b y n : Nat} (h : b ^ y % n = 1 % n) (x : Nat) :
    ∀ N, b ^ (x + y * N) % n = b ^ x % n
  | 0 => by simp
  | N + 1 => by
    rw [Nat.mul_succ, ← Nat.add_assoc, Nat.pow_add, Nat.mul_mod, pow_mod_period h x N, h,
      ← Nat.mul_mod, Nat.mul_one]

theorem mod_cancel_mul_right {m c x y : Nat} (hcop : Nat.Coprime m c)
    (h : (x * c) % m = (y * c) % m) : x % m = y % m := by
  rcases Nat.le_total y x with hle | hle
  · exact mod_cancel_mul_left hcop hle (by rwa [Nat.mul_comm c x, Nat.mul_comm c y])
  · exact (mod_cancel_mul_left hcop hle (by rw [Nat.mul_comm c x, Nat.mul_comm c y]; exact h.symm)).symm

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

theorem exists_pow2_period (m' : Nat) (hM : 0 < m') (hc : Nat.Coprime m' 2) :
    ∃ D, 0 < D ∧ D ≤ m' ∧ 2 ^ D % m' = 1 % m' := by
  apply Classical.byContradiction
  intro hno
  have hinj : ∀ a b, a < b → b ≤ m' → 2 ^ a % m' ≠ 2 ^ b % m' := by
    intro a b hab hb heq
    apply hno
    refine ⟨b - a, by omega, by omega, ?_⟩
    have hcop : Nat.Coprime m' (2 ^ a) := Nat.Coprime.pow_right _ hc
    exact mod_cancel_mul_right (x := 2 ^ (b - a)) (y := 1) hcop
      (by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega), Nat.one_mul]; exact heq.symm)
  have hnd : ((List.range (m' + 1)).map (fun i => 2 ^ i % m')).Nodup := by
    apply List.pairwise_map.2
    apply List.Pairwise.imp_of_mem _ List.nodup_range
    intro a b ha hb hab
    rw [List.mem_range] at ha hb
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · exact hinj a b h (by omega)
    · exact fun h' => hinj b a h (by omega) h'.symm
  have hsub : ((List.range (m' + 1)).map (fun i => 2 ^ i % m')) ⊆ List.range m' := by
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨i, _, rfl⟩ := hv
    rw [List.mem_range]; exact Nat.mod_lt _ hM
  have := hnd.length_le_of_subset hsub
  simp at this
  omega

theorem NonWieferich.odd {q : Nat} [NonWieferich q] : q % 2 = 1 := by
  obtain ⟨d, u, hd, hu⟩ := NonWieferich.unit (q := q)
  have h1 := NonWieferich.one_lt (q := q)
  rcases d with _ | d
  · have hu0 : u = 0 := by
      rcases Nat.eq_zero_or_pos u with h | h
      · exact h
      · have : q * u ≥ 1 * 1 := Nat.mul_le_mul (by omega) h
        simp at hd; omega
    rw [hu0, Nat.Coprime, Nat.gcd_zero_right] at hu; omega
  · rcases Nat.mod_two_eq_zero_or_one q with h | h
    · have e1 : (2 ^ (d + 1)) % 2 = 0 := by rw [Nat.pow_succ]; simp
      rw [hd, Nat.add_mod, Nat.mul_mod, h] at e1; simp at e1
    · exact h

theorem NonWieferich.three_le {q : Nat} [NonWieferich q] : 3 ≤ q := by
  have := NonWieferich.odd (q := q); have := NonWieferich.one_lt (q := q); omega

theorem NonWieferich.gen {q : Nat} [NonWieferich q] : ∃ d u, 0 < d ∧ d ≤ q ∧ 2 ^ d = 1 + q * u ∧ Nat.Coprime q u := by
  obtain ⟨d, u, hd, hu⟩ := NonWieferich.unit (q := q)
  have hp3 := NonWieferich.three_le (q := q)
  have hodd := NonWieferich.odd (q := q)
  obtain ⟨D0, hD0, hD0p, hD0m⟩ := exists_pow2_period q (by omega) (coprime_two_of_odd hodd)
  obtain ⟨D, ⟨hD, hDm⟩, hmin⟩ := exists_least (fun D => 0 < D ∧ 2 ^ D % q = 1 % q) ⟨D0, hD0, hD0m⟩
  have hDp : D ≤ q := by
    apply Classical.byContradiction; intro h
    exact hmin D0 (by omega) ⟨hD0, hD0m⟩
  have hdm : 2 ^ d % q = 1 % q := by rw [hd, Nat.add_mul_mod_self_left]
  have hr : d % D = 0 := by
    apply Classical.byContradiction; intro h
    have e := pow_mod_period hDm (d % D) (d / D)
    rw [Nat.mod_add_div] at e
    exact hmin (d % D) (Nat.mod_lt _ hD) ⟨by omega, by rw [← e]; exact hdm⟩
  have hp1 : 1 % q = 1 := Nat.mod_eq_of_lt (by omega)
  have hv : 2 ^ D = 1 + q * (2 ^ D / q) := by
    have := Nat.mod_add_div (2 ^ D) q; rw [hDm, hp1] at this; omega
  have hdD : d = D * (d / D) := by have := Nat.mod_add_div d D; omega
  obtain ⟨z, hz⟩ := binom_quadratic (q * (2 ^ D / q)) (d / D)
  have hpu : q * u = q * ((2 ^ D / q) * (d / D + q * (2 ^ D / q) * z)) := by
    have e : 2 ^ d = (2 ^ D) ^ (d / D) := by rw [← Nat.pow_mul, ← hdD]
    rw [e, hv, hz] at hd; grind
  have hu' := Nat.eq_of_mul_eq_mul_left (by omega) hpu
  refine ⟨D, 2 ^ D / q, hD, hDp, hv, ?_⟩
  exact Nat.Coprime.coprime_dvd_right ⟨_, hu'⟩ hu

theorem p_dvd_pow (q K : Nat) : q ∣ q ^ (K + 1) := ⟨q ^ K, by rw [Nat.pow_succ, Nat.mul_comm]⟩

section Basics
variable (q : Nat) [NonWieferich q]

theorem one_lt_powp (K : Nat) : 1 < q ^ (K + 1) :=
  Nat.one_lt_pow (Nat.succ_ne_zero K) (by have := NonWieferich.three_le (q := q); omega)

theorem powp_pos (K : Nat) : 0 < q ^ K := Nat.pow_pos (by have := NonWieferich.three_le (q := q); omega)

theorem coprime_p_two : Nat.Coprime q 2 := coprime_two_of_odd NonWieferich.odd

theorem powp_odd (n : Nat) : q ^ n % 2 = 1 := by
  rw [Nat.pow_mod, NonWieferich.odd (q := q), Nat.one_pow]

theorem one_mod_P (K : Nat) : 1 % q ^ (K + 1) = 1 := Nat.mod_eq_of_lt (one_lt_powp q K)

theorem period (K : Nat) : ∃ T, 0 < T ∧ 2 ^ T % q ^ (K + 1) = 1 % q ^ (K + 1) := by
  obtain ⟨d, u, hd0, -, hd, hu⟩ := NonWieferich.gen (q := q)
  refine ⟨d * q ^ K, Nat.mul_pos hd0 (powp_pos q K), ?_⟩
  rw [Nat.pow_mul, hd, one_mod_P]
  exact (order_iff NonWieferich.odd NonWieferich.three_le hu K _).2 (Nat.dvd_refl _)

theorem two_gen (K x : Nat) (hx : x % q = 1) : ∃ s, 2 ^ s % q ^ (K + 1) = x % q ^ (K + 1) := by
  obtain ⟨d, u, _, -, hd, hu⟩ := NonWieferich.gen (q := q)
  obtain ⟨t, _, ht⟩ := unit_power_cover NonWieferich.odd NonWieferich.three_le hu K x hx
  exact ⟨d * t, by rw [Nat.pow_mul, hd]; exact ht⟩

def InPowTwo (K a : Nat) : Prop := ∃ m, 2 ^ m % q ^ (K + 1) = a % q ^ (K + 1)

theorem inPowTwo_ratio {K a b : Nat} (ha : InPowTwo q K a) (hb : InPowTwo q K b) :
    ∃ j, (2 ^ j * a) % q ^ (K + 1) = b % q ^ (K + 1) := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  obtain ⟨T, hT0, hT⟩ := period q K
  refine ⟨n + m * (T - 1), ?_⟩
  rw [Nat.mul_mod, ← hm, ← Nat.mul_mod, ← Nat.pow_add, ← hn]
  have e : n + m * (T - 1) + m = n + T * m := by
    rw [Nat.add_assoc, Nat.mul_comm T m]
    have : m * (T - 1) + m = m * T := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega
  rw [e]; exact pow_mod_period hT n m

theorem target_inPowTwo {w i : Nat} (hw : w % q = 2 ^ i % q) (K : Nat) : InPowTwo q K w := by
  obtain ⟨T, hT0, hT⟩ := period q K
  have hTp : 2 ^ T % q = 1 := by
    rw [← Nat.mod_mod_of_dvd _ (p_dvd_pow q K), hT, one_mod_P,
      Nat.mod_eq_of_lt (by have := NonWieferich.three_le (q := q); omega)]
  have h1 : (2 ^ (i * (T - 1)) * w) % q = 1 := by
    rw [Nat.mul_mod, hw, ← Nat.mul_mod, ← Nat.pow_add,
      show i * (T - 1) + i = T * i by rw [Nat.mul_comm T i, ← Nat.mul_succ]; congr 1; omega,
      Nat.pow_mul, Nat.pow_mod, hTp, Nat.one_pow]
    exact Nat.mod_eq_of_lt (by have := NonWieferich.three_le (q := q); omega)
  obtain ⟨s, hs⟩ := two_gen q K _ h1
  refine ⟨s + i, ?_⟩
  rw [Nat.pow_add, Nat.mul_mod, hs, ← Nat.mul_mod, Nat.mul_assoc, Nat.mul_comm w, ← Nat.mul_assoc,
    ← Nat.pow_add, show i * (T - 1) + i = 0 + T * i by
      rw [Nat.zero_add, Nat.mul_comm T i, ← Nat.mul_succ]; congr 1; omega,
    Nat.mul_mod, pow_mod_period hT 0 i, ← Nat.mul_mod, Nat.pow_zero, Nat.one_mul]

end Basics

section Residues
variable (m' : Nat) [NeZero m']

def residue (n : Nat) : Fin m' := Fin.ofNat m' n

theorem residue_val (n : Nat) : (residue m' n).val = n % m' := Fin.val_ofNat m' n

theorem residue_eq_iff (a b : Nat) : residue m' a = residue m' b ↔ a % m' = b % m' := by
  constructor
  · intro h; have := congrArg Fin.val h; rwa [residue_val, residue_val] at this
  · intro h; apply Fin.ext; rw [residue_val, residue_val]; exact h

theorem residue_add (a b : Nat) : residue m' (a + b) = residue m' a + residue m' b := by
  apply Fin.ext; rw [Fin.val_add, residue_val, residue_val, residue_val, Nat.add_mod]

theorem residue_mul (a b : Nat) : residue m' (a * b) = residue m' a * residue m' b := by
  apply Fin.ext; rw [Fin.val_mul, residue_val, residue_val, residue_val, Nat.mul_mod]

theorem residue_zero : residue m' 0 = (0 : Fin m') := rfl
theorem residue_one : residue m' 1 = (1 : Fin m') := rfl
theorem residue_two : residue m' 2 = (2 : Fin m') := rfl
class Invertible2p (q m' : Nat) [NeZero m'] : Prop where
  two : ∃ b : Fin m', (2 : Fin m') * b = 1
  pinv : ∃ b : Fin m', residue m' q * b = 1

open Classical in
noncomputable def unitInv (a : Fin m') : Fin m' := if h : ∃ b : Fin m', a * b = 1 then h.choose else 0

theorem mul_unitInv {a : Fin m'} (h : ∃ b : Fin m', a * b = 1) : a * unitInv m' a = 1 := by
  unfold unitInv
  split
  · rename_i h'; exact h'.choose_spec
  · rename_i h'; exact absurd h h'

theorem two_mul_unitInv {q : Nat} [Invertible2p q m'] : (2 : Fin m') * unitInv m' 2 = 1 := mul_unitInv m' (Invertible2p.two (q := q))
theorem cancel_invertible {u v a b : Fin m'} (hu : u * v = 1) (h : u * a = u * b) : a = b := by
  calc a = (u * v) * a := by rw [hu]; grind
    _ = v * (u * a) := by grind
    _ = v * (u * b) := by rw [h]
    _ = (u * v) * b := by grind
    _ = b := by rw [hu]; grind

end Residues

section Counting
variable {m' : Nat}

open Classical in
noncomputable def cardinality (S : Fin m' → Prop) : Nat :=
  ((List.finRange m').filter (fun t => decide (S t))).length

open Classical in
theorem mem_cardlist {S : Fin m' → Prop} {t : Fin m'} :
    t ∈ (List.finRange m').filter (fun t => decide (S t)) ↔ S t := by
  rw [List.mem_filter]; simp [List.mem_finRange]

open Classical in
theorem cardinality_le_of_inj {S T : Fin m' → Prop} (g : Fin m' → Fin m')
    (hinj : ∀ a b, g a = g b → a = b) (hmap : ∀ t, S t → T (g t)) : cardinality S ≤ cardinality T := by
  unfold cardinality
  have hnd : ((List.finRange m').filter (fun t => decide (S t))).Nodup :=
    List.Pairwise.filter _ (List.nodup_finRange m')
  have hnd2 : (((List.finRange m').filter (fun t => decide (S t))).map g).Nodup := by
    apply List.pairwise_map.2
    apply List.Pairwise.imp_of_mem _ hnd
    intro a b _ _ hab hg
    exact hab (hinj a b hg)
  have hsub : ((List.finRange m').filter (fun t => decide (S t))).map g
      ⊆ (List.finRange m').filter (fun t => decide (T t)) := by
    intro u hu
    rw [List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    rw [mem_cardlist] at ht ⊢
    exact hmap t ht
  have := hnd2.length_le_of_subset hsub
  simpa using this

open Classical in
theorem cardinality_eq_of_sub {S T : Fin m' → Prop} (hsub : ∀ t, S t → T t) (hc : cardinality T ≤ cardinality S) :
    ∀ t, T t → S t := by
  intro t0 ht0
  apply Classical.byContradiction
  intro hn
  unfold cardinality at hc
  have hnd : ((List.finRange m').filter (fun t => decide (S t))).Nodup :=
    List.Pairwise.filter _ (List.nodup_finRange m')
  have hnd2 : (t0 :: (List.finRange m').filter (fun t => decide (S t))).Nodup := by
    rw [List.nodup_cons]
    exact ⟨fun h => hn ((mem_cardlist).1 h), hnd⟩
  have hsub2 : (t0 :: (List.finRange m').filter (fun t => decide (S t)))
      ⊆ (List.finRange m').filter (fun t => decide (T t)) := by
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact (mem_cardlist).2 ht0
    · exact (mem_cardlist).2 (hsub u ((mem_cardlist).1 hu))
  have := hnd2.length_le_of_subset hsub2
  simp only [List.length_cons] at this
  omega

end Counting

theorem exists_inv_of_coprime {m' : Nat} [NeZero m'] (a : Fin m') (hcop : Nat.Coprime m' a.val) :
    ∃ b : Fin m', a * b = 1 := by
  have hinj : ∀ s t : Fin m', a * s = a * t → s = t := by
    intro s t h
    have h1 := congrArg Fin.val h
    rw [Fin.val_mul, Fin.val_mul] at h1
    have h2 : (s.val * a.val) % m' = (t.val * a.val) % m' := by
      rw [Nat.mul_comm s.val, Nat.mul_comm t.val]; exact h1
    have h3 := mod_cancel_mul_right hcop h2
    rw [Nat.mod_eq_of_lt s.isLt, Nat.mod_eq_of_lt t.isLt] at h3
    exact Fin.ext h3
  have hc : cardinality (fun _ : Fin m' => True) ≤ cardinality (fun t : Fin m' => ∃ s, a * s = t) :=
    cardinality_le_of_inj (fun t => a * t) hinj (fun t _ => ⟨t, rfl⟩)
  exact cardinality_eq_of_sub (S := fun t : Fin m' => ∃ s, a * s = t) (T := fun _ : Fin m' => True)
    (fun _ _ => trivial) hc 1 trivial

theorem exists_inv_residue {m' : Nat} [NeZero m'] (n : Nat) (hcop : Nat.Coprime m' n) :
    ∃ b : Fin m', residue m' n * b = 1 := by
  apply exists_inv_of_coprime
  rw [residue_val]
  unfold Nat.Coprime at hcop ⊢
  rw [Nat.gcd_comm, ← Nat.gcd_rec]; exact hcop

theorem invertible2p_of_coprime {q m' : Nat} [NeZero m'] (h : Nat.Coprime m' (2 * q)) : Invertible2p q m' :=
  ⟨exists_inv_residue 2 (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right 2 q) h),
   exists_inv_residue q (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_left q 2) h)⟩

theorem mod_combine_le {a b n r : Nat} (hPQ : Nat.Coprime a b) (hle : r ≤ n)
    (hP : n % a = r % a) (hQ : n % b = r % b) : n % (a * b) = r % (a * b) := by
  have h1 : a ∣ n - r := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hP)
  have h2 : b ∣ n - r := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hQ)
  obtain ⟨k, hk⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd hPQ h1 h2
  have : n = r + (a * b) * k := by omega
  rw [this, Nat.add_mul_mod_self_left]

theorem mod_combine {a b n r : Nat} (hPQ : Nat.Coprime a b)
    (hP : n % a = r % a) (hQ : n % b = r % b) : n % (a * b) = r % (a * b) := by
  rcases Nat.le_total r n with h | h
  · exact mod_combine_le hPQ h hP hQ
  · exact (mod_combine_le hPQ h hP.symm hQ.symm).symm

theorem residue_self_val {n : Nat} [NeZero n] (v : Fin n) : residue n v.val = v :=
  Fin.ext (by rw [residue_val, Nat.mod_eq_of_lt v.isLt])

section Least
variable (m' : Nat) [NeZero m']
theorem residue_self : residue m' m' = 0 := by
  rw [← residue_zero m']; apply (residue_eq_iff m' _ _).2; simp

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
theorem mod_of_dvd_mod {a b P Z : Nat} (hZ : Z ∣ P) (h : a % P = b % P) : a % Z = b % Z := by
  rw [← Nat.mod_mod_of_dvd a hZ, h, Nat.mod_mod_of_dvd b hZ]

theorem coprime_p_of_coprime_two_mul {m' q : Nat} (hM : Nat.Coprime m' (2 * q)) : Nat.Coprime m' q :=
  Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_left q 2) hM
theorem coprime_two_of_coprime_two_mul {m' q : Nat} (hM : Nat.Coprime m' (2 * q)) : Nat.Coprime m' 2 :=
  Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right 2 q) hM

section Words
variable (q : Nat)

def oneCount : List Nat → Nat
  | [] => 0
  | e :: u => oneCount u + e

def offset : List Nat → Nat
  | [] => 0
  | e :: u => q ^ oneCount u * e + 2 * offset u

theorem collatz_odd [NonWieferich q] (y : Nat) :
    collatz q (2 * y + 1) = 2 * (q * y + (q + 1) / 2) := by
  have := NonWieferich.odd (q := q)
  unfold collatz
  rw [ite_eq_right (by omega)]
  have h : q + 1 = 2 * ((q + 1) / 2) := by omega
  generalize (q + 1) / 2 = c at h ⊢
  grind

theorem integrality [NonWieferich q] : ∀ (u : List Nat), (∀ e ∈ u, e ≤ 1) → ∀ x : Nat,
    2 ^ u.length ∣ q ^ oneCount u * x + offset q u →
    ∃ k, iter (collatz q) k x = (q ^ oneCount u * x + offset q u) / 2 ^ u.length
  | [], _, x, _ => ⟨0, by simp [oneCount, offset, iter]⟩
  | e :: u, hu, x, h => by
    have he : e = 0 ∨ e = 1 := by have := hu e (by simp); omega
    have hu' : ∀ d ∈ u, d ≤ 1 := fun d hd => hu d (by simp [hd])
    have hp : q ^ oneCount u % 2 = 1 := powp_odd q _
    have hc : q + 1 = 2 * ((q + 1) / 2) := by have := NonWieferich.odd (q := q); omega
    have h2 : 2 ∣ 2 ^ (u.length + 1) := ⟨2 ^ u.length, by grind⟩
    have hpow : 2 ^ (u.length + 1) = 2 * 2 ^ u.length := by grind
    simp only [List.length_cons, oneCount, offset] at h ⊢
    rcases he with rfl | rfl
    · have h0 := Nat.dvd_trans h2 h
      obtain ⟨y, hy | hy⟩ : ∃ y, x = 2 * y ∨ x = 2 * y + 1 := ⟨x / 2, by omega⟩
      · subst hy
        have hn : q ^ (oneCount u + 0) * (2 * y) + (q ^ oneCount u * 0 + 2 * offset q u)
            = 2 * (q ^ oneCount u * y + offset q u) := by grind
        rw [hn, hpow] at h
        have h' := (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).1 h
        obtain ⟨k, hk⟩ := integrality u hu' y h'
        refine ⟨k + 1, ?_⟩
        show iter (collatz q) k (collatz q (2 * y)) = _
        rw [collatz_double, hk, hn, hpow, Nat.mul_div_mul_left _ _ (by omega : 0 < 2)]
      · subst hy
        exfalso
        have hn : q ^ (oneCount u + 0) * (2 * y + 1) + (q ^ oneCount u * 0 + 2 * offset q u)
            = 2 * (q ^ oneCount u * y + offset q u) + q ^ oneCount u := by grind
        rw [hn] at h0
        generalize q ^ oneCount u * y + offset q u = P at h0
        omega
    · have h0 := Nat.dvd_trans h2 h
      obtain ⟨y, hy | hy⟩ : ∃ y, x = 2 * y ∨ x = 2 * y + 1 := ⟨x / 2, by omega⟩
      · subst hy
        exfalso
        have hn : q ^ (oneCount u + 1) * (2 * y) + (q ^ oneCount u * 1 + 2 * offset q u)
            = 2 * (q ^ oneCount u * (q * y) + offset q u) + q ^ oneCount u := by grind
        rw [hn] at h0
        generalize q ^ oneCount u * (q * y) + offset q u = P at h0
        omega
      · subst hy
        have hn : q ^ (oneCount u + 1) * (2 * y + 1) + (q ^ oneCount u * 1 + 2 * offset q u)
            = 2 * (q ^ oneCount u * (q * y + (q + 1) / 2) + offset q u) := by
          rw [Nat.pow_succ]
          generalize (q + 1) / 2 = c at hc ⊢
          grind
        rw [hn, hpow] at h
        have h' := (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).1 h
        obtain ⟨k, hk⟩ := integrality u hu' (q * y + (q + 1) / 2) h'
        refine ⟨k + 2, ?_⟩
        show iter (collatz q) k (collatz q (collatz q (2 * y + 1))) = _
        rw [collatz_odd, collatz_double, hk, hn, hpow, Nat.mul_div_mul_left _ _ (by omega : 0 < 2)]

theorem integrality_reaches [NonWieferich q] (u : List Nat) (hu : ∀ e ∈ u, e ≤ 1) (x : Nat)
    (h : 2 ^ u.length ∣ q ^ oneCount u * x + offset q u) :
    Reaches q x ((q ^ oneCount u * x + offset q u) / 2 ^ u.length) := integrality q u hu x h

theorem oneCount_le : ∀ u : List Nat, (∀ e ∈ u, e ≤ 1) → oneCount u ≤ u.length
  | [], _ => by simp [oneCount]
  | e :: u, hu => by
    have h1 := oneCount_le u (fun d hd => hu d (by simp [hd]))
    have h2 := hu e (by simp)
    simp only [oneCount, List.length_cons]; omega

theorem reaches_pow2 [NonWieferich q] (w : Nat) : ∀ n, Reaches q (2 ^ n * w) w
  | 0 => ⟨0, by simp [iter]⟩
  | n + 1 => by
    obtain ⟨k, hk⟩ := reaches_pow2 w n
    refine ⟨k + 1, ?_⟩
    rw [iter_add]
    show iter (collatz q) k (collatz q (2 ^ (n + 1) * w)) = w
    rw [show 2 ^ (n + 1) * w = 2 * (2 ^ n * w) by rw [Nat.pow_succ]; grind, collatz_double]; exact hk

end Words

theorem coprime_target (q : Nat) [NonWieferich q] {w : Nat} (hw : ∃ i, w % q = 2 ^ i % q) : Nat.Coprime q w := by
  obtain ⟨i, hi⟩ := hw
  have h : Nat.Coprime q (2 ^ i) := Nat.Coprime.pow_right i (coprime_p_two q)
  unfold Nat.Coprime at h ⊢
  rw [Nat.gcd_rec, hi, ← Nat.gcd_rec]; exact h

theorem oneCount_append (u v : List Nat) : oneCount (u ++ v) = oneCount u + oneCount v := by
  induction u with
  | nil => simp [oneCount]
  | cons e u ih => simp only [List.cons_append, oneCount, ih]; omega

theorem offset_append (q : Nat) (u v : List Nat) :
    offset q (u ++ v) = q ^ oneCount v * offset q u + 2 ^ u.length * offset q v := by
  induction u with
  | nil => simp [offset]
  | cons e u ih =>
    simp only [List.cons_append, offset, oneCount_append, ih, List.length_cons]
    rw [Nat.pow_add, Nat.pow_succ]
    grind

theorem oneCount_replicate_zero (m : Nat) : oneCount (List.replicate m 0) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, oneCount, ih]

theorem offset_replicate_zero (q m : Nat) : offset q (List.replicate m 0) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, offset, ih]

theorem oneCount_replicate_one (k : Nat) : oneCount (List.replicate k 1) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, oneCount, ih]

theorem offset_ones (q k : Nat) :
    (q + 2) ^ k = 2 ^ k + q * offset (q + 2) (List.replicate k 1) := by
  induction k with
  | zero => simp [offset]
  | succ k ih =>
    have e : offset (q + 2) (List.replicate (k + 1) 1)
        = (q + 2) ^ k + 2 * offset (q + 2) (List.replicate k 1) := by
      simp [List.replicate_succ, offset, oneCount_replicate_one]
    rw [e, Nat.pow_succ, Nat.pow_succ]
    generalize offset (q + 2) (List.replicate k 1) = o at *
    generalize (q + 2) ^ k = A at *
    grind

theorem pow_period_pow (P T : Nat) (hT : 2 ^ T % P = 1 % P) : ∀ k : Nat, (2 ^ T) ^ k % P = 1 % P := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.pow_succ, Nat.mul_mod, ih, hT, ← Nat.mul_mod, Nat.one_mul]

theorem pow_two_mod_period (P T : Nat) (hT : 2 ^ T % P = 1 % P) (x y : Nat) (hxy : x % T = y % T) :
    2 ^ x % P = 2 ^ y % P := by
  have key : ∀ z : Nat, 2 ^ z % P = 2 ^ (z % T) % P := by
    intro z
    have hz : 2 ^ z = (2 ^ T) ^ (z / T) * 2 ^ (z % T) := by
      rw [← Nat.pow_mul, ← Nat.pow_add, Nat.div_add_mod]
    rw [hz, Nat.mul_mod, pow_period_pow P T hT, ← Nat.mul_mod, Nat.one_mul]
  rw [key x, key y, hxy]

variable {m' : Nat} [NeZero m']

noncomputable def backStep (q : Nat) [Invertible2p q m'] (e : Nat) (x : Fin m') : Fin m' :=
  (residue m' (q ^ e) * x + residue m' e) * unitInv m' 2

noncomputable def backWord (q : Nat) [Invertible2p q m'] : List Nat → Fin m' → Fin m'
  | [] => fun x => x
  | e :: u => fun x => backWord q u (backStep q e x)

theorem cancel_two (q : Nat) [Invertible2p q m'] (a b : Fin m') (h : (2 : Fin m') * a = 2 * b) : a = b :=
  cancel_invertible (m' := m') (two_mul_unitInv (m' := m') (q := q)) h

theorem two_mul_backStep (q : Nat) [Invertible2p q m'] (e : Nat) (x : Fin m') :
    (2 : Fin m') * backStep q e x = residue m' (q ^ e) * x + residue m' e := by
  unfold backStep
  have h2 : (2 : Fin m') * unitInv m' 2 = 1 := two_mul_unitInv (m' := m') (q := q)
  grind

theorem residue_two_pow (k : Nat) : residue m' (2 ^ (k + 1)) = 2 * residue m' (2 ^ k) := by
  rw [Nat.pow_succ, residue_mul, residue_two]; grind

theorem residue_p_pow_add (q a e : Nat) :
    residue m' (q ^ (a + e)) = residue m' (q ^ a) * residue m' (q ^ e) := by
  rw [Nat.pow_add, residue_mul]

theorem backWord_iff (q : Nat) [Invertible2p q m'] : ∀ (u : List Nat) (s t : Fin m'),
    residue m' (q ^ oneCount u) * s + residue m' (offset q u) = residue m' (2 ^ u.length) * t
      ↔ backWord q u s = t := by
  intro u
  induction u with
  | nil =>
    intro s t
    simp [oneCount, offset, backWord, residue_zero, residue_one]
    grind
  | cons e u ih =>
    intro s t
    have hsf := two_mul_backStep (m' := m') q e s
    have hIH := ih (backStep q e s) t
    show _ ↔ backWord q u (backStep q e s) = t
    rw [← hIH]
    have hoff : residue m' (offset q (e :: u)) = residue m' (q ^ oneCount u) * residue m' e
        + 2 * residue m' (offset q u) := by
      simp only [offset, residue_add, residue_mul, residue_two]
    have hon : residue m' (q ^ oneCount (e :: u))
        = residue m' (q ^ oneCount u) * residue m' (q ^ e) := by
      rw [oneCount, Nat.add_comm, residue_p_pow_add]; grind
    have hlen : residue m' (2 ^ (e :: u).length) = 2 * residue m' (2 ^ u.length) := by
      rw [List.length_cons, residue_two_pow]
    rw [hon, hoff, hlen]
    generalize residue m' (q ^ oneCount u) = A at *
    generalize residue m' (offset q u) = B at *
    generalize residue m' (2 ^ u.length) = C at *
    generalize residue m' (q ^ e) = Qe at *
    generalize residue m' e = E at *
    generalize backStep q e s = sf at *
    constructor
    · intro h
      apply cancel_two q
      grind
    · intro h
      grind

theorem backStep_zero (q : Nat) [Invertible2p q m'] (y : Fin m') : backStep q 0 y = y * unitInv m' 2 := by
  unfold backStep; rw [Nat.pow_zero, residue_one, residue_zero]; grind

theorem backWord_append (q : Nat) [Invertible2p q m'] : ∀ (u v : List Nat) (x : Fin m'),
    backWord q (u ++ v) x = backWord q v (backWord q u x) := by
  intro u
  induction u with
  | nil => intro v x; rfl
  | cons e u ih => intro v x; exact ih v (backStep q e x)

theorem backWord_zeros (q : Nat) [Invertible2p q m'] : ∀ (m : Nat) (y : Fin m'),
    backWord q (List.replicate m 0) (residue m' (2 ^ m) * y) = y := by
  intro m
  induction m with
  | zero => intro y; simp [backWord, residue_one]; grind
  | succ m ih =>
    intro y
    have h2 : (2 : Fin m') * unitInv m' 2 = 1 := two_mul_unitInv (m' := m') (q := q)
    have hstep : backStep q 0 (residue m' (2 ^ (m + 1)) * y) = residue m' (2 ^ m) * y := by
      rw [backStep_zero, residue_two_pow]
      grind
    show backWord q (List.replicate m 0) (backStep q 0 (residue m' (2 ^ (m + 1)) * y)) = y
    rw [hstep, ih]

theorem backWord_ones_iff (q : Nat) [Invertible2p q m'] (k : Nat) (x t : Fin m') :
    residue m' (q ^ k) * x + residue m' (offset q (List.replicate k 1))
      = residue m' (2 ^ k) * t ↔ backWord q (List.replicate k 1) x = t := by
  have h := backWord_iff (m' := m') q (List.replicate k 1) x t
  have hc : oneCount (List.replicate k 1) = k := oneCount_replicate_one k
  have hl : (List.replicate k 1).length = k := List.length_replicate
  rw [hc, hl] at h
  exact h

theorem ones_surj (q : Nat) [Invertible2p q m'] (hM : Nat.Coprime m' (2 * q)) (k : Nat) (tgt : Fin m') :
    ∃ t : Fin m', backWord q (List.replicate k 1) t = tgt := by
  obtain ⟨b, hb⟩ := exists_inv_residue (m' := m') (q ^ k)
    (Nat.Coprime.pow_right k (coprime_p_of_coprime_two_mul hM))
  refine ⟨b * (residue m' (2 ^ k) * tgt - residue m' (offset q (List.replicate k 1))), ?_⟩
  rw [← backWord_ones_iff]
  grind

theorem fixed_point (q K : Nat) (hp : Nat.Coprime q 2) [NeZero (q ^ (K + 1))] :
    ∃ b : Fin (q ^ (K + 1)), (2 : Fin (q ^ (K + 1))) * b = residue (q ^ (K + 1)) q * b + 1 := by
  have hp0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp [Nat.Coprime] at hp
    · exact h
  have hpP : q ≤ q ^ (K + 1) := by
    have := Nat.pow_le_pow_right hp0 (show 1 ≤ K + 1 by omega)
    simpa using this
  obtain ⟨n, hn⟩ : ∃ n, n = q ^ (K + 1) + 2 - q := ⟨_, rfl⟩
  have hnp : n + q = q ^ (K + 1) + 2 := by omega
  have hgp : Nat.Coprime q n := by
    have h1 : Nat.gcd q n ∣ 2 := by
      have d1 : Nat.gcd q n ∣ q := Nat.gcd_dvd_left q n
      have d2 : Nat.gcd q n ∣ n := Nat.gcd_dvd_right q n
      have d3 : Nat.gcd q n ∣ q ^ (K + 1) :=
        Nat.dvd_trans d1 (by simpa using Nat.pow_dvd_pow q (show 1 ≤ K + 1 by omega))
      have d4 : Nat.gcd q n ∣ q ^ (K + 1) + 2 := by
        rw [← hnp]; exact Nat.dvd_add d2 d1
      exact (Nat.dvd_add_right d3).1 d4
    have h2 : Nat.gcd (Nat.gcd q n) 2 = 1 := Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left q n) hp
    rw [Nat.gcd_eq_left h1] at h2
    exact h2
  have hcopn : Nat.Coprime (q ^ (K + 1)) n := Nat.Coprime.pow_left (K + 1) hgp
  obtain ⟨b, hb⟩ := exists_inv_residue n hcopn
  have hrel : residue (q ^ (K + 1)) n + residue (q ^ (K + 1)) q = (2 : Fin (q ^ (K + 1))) := by
    rw [← residue_add, hnp, residue_add, residue_self, residue_two]; grind
  refine ⟨b, ?_⟩
  rw [← hrel]; grind

theorem ones_offset_fin (q K : Nat) (hp3 : 3 ≤ q) [NeZero (q ^ (K + 1))]
    (b : Fin (q ^ (K + 1))) (hb : (2 : Fin (q ^ (K + 1))) * b = residue (q ^ (K + 1)) q * b + 1) :
    residue (q ^ (K + 1)) (offset q (List.replicate (K + 1) 1))
      = residue (q ^ (K + 1)) (2 ^ (K + 1)) * b := by
  obtain ⟨c, rfl⟩ : ∃ c, q = c + 2 := ⟨q - 2, by omega⟩
  have h := offset_ones c (K + 1)
  have hres : residue ((c + 2) ^ (K + 1)) (2 ^ (K + 1) + c * offset (c + 2) (List.replicate (K + 1) 1))
      = 0 := by
    rw [← h]; exact residue_self _
  rw [residue_add, residue_mul] at hres
  have hq : residue ((c + 2) ^ (K + 1)) c + 2 = residue ((c + 2) ^ (K + 1)) (c + 2) := by
    rw [residue_add, residue_two]
  grind

theorem padic_word (q K d u w : Nat) [NonWieferich q] (hp3 : 3 ≤ q) (hodd : q % 2 = 1) (hd0 : 0 < d)
    (hd : 2 ^ d = 1 + q * u) (hu : Nat.Coprime q u) (hw : ∃ i, w % q = 2 ^ i % q) :
    ∃ nz, nz < d * q ^ K ∧
      (2 ^ (K + 1 + nz) * w) % q ^ (K + 1) = offset q (List.replicate (K + 1) 1) % q ^ (K + 1) := by
  haveI : NeZero (q ^ (K + 1)) := ⟨Nat.pos_iff_ne_zero.1 (Nat.pow_pos (by omega))⟩
  obtain ⟨b, hb⟩ := fixed_point q K (coprime_two_of_odd hodd)
  have hO := ones_offset_fin q K hp3 b hb

  have hbp : b.val % q = 2 ^ (d - 1) % q := by
    have e1 : residue (q ^ (K + 1)) (2 * b.val) = residue (q ^ (K + 1)) (q * b.val + 1) := by
      rw [residue_mul, residue_self_val, residue_add, residue_mul, residue_self_val, residue_one]
      exact hb
    have e2 : (2 * b.val) % q = 1 % q := by
      have hpP : q ∣ q ^ (K + 1) := ⟨q ^ K, by rw [Nat.pow_succ, Nat.mul_comm]⟩
      have := (residue_eq_iff _ _ _).1 e1
      rw [← Nat.mod_mod_of_dvd (2 * b.val) hpP, this, Nat.mod_mod_of_dvd _ hpP, Nat.mul_add_mod]
    have hd1 : d - 1 + 1 = d := by omega
    have e3 : (2 ^ (d - 1) * 2) % q = 1 % q := by
      have h2d : 2 ^ d = 2 ^ (d - 1) * 2 :=
        calc 2 ^ d = 2 ^ (d - 1 + 1) := by rw [hd1]
          _ = 2 ^ (d - 1) * 2 := Nat.pow_succ 2 (d - 1)
      rw [← h2d, hd, Nat.add_mul_mod_self_left]
    have h4 : (2 ^ (d - 1) * (2 * b.val)) % q = (2 ^ (d - 1) * 2 * b.val) % q := by
      rw [Nat.mul_assoc]
    have h5 : (2 ^ (d - 1) * (2 * b.val)) % q = 2 ^ (d - 1) % q := by
      rw [Nat.mul_mod, e2, ← Nat.mul_mod, Nat.mul_one]
    have h6 : (2 ^ (d - 1) * 2 * b.val) % q = b.val % q := by
      rw [Nat.mul_mod, e3, ← Nat.mul_mod, Nat.one_mul]
    rw [← h6, ← h4, h5]
  obtain ⟨s, hs⟩ := target_inPowTwo q hbp K
  obtain ⟨i, hi⟩ := hw
  obtain ⟨m0, hm0⟩ := target_inPowTwo q hi K
  have hPgt : 1 < q ^ (K + 1) := Nat.lt_of_lt_of_le (by omega : 1 < q) (Nat.le_self_pow (by omega) q)
  have hT : 2 ^ (d * q ^ K) % q ^ (K + 1) = 1 % q ^ (K + 1) := by
    rw [Nat.pow_mul, hd, Nat.mod_eq_of_lt hPgt]
    exact (order_iff hodd hp3 hu K (q ^ K)).2 (Nat.dvd_refl _)
  have hTpos : 0 < d * q ^ K := Nat.mul_pos hd0 (Nat.pow_pos (by omega))
  obtain ⟨T, hTdef⟩ : ∃ T, T = d * q ^ K := ⟨_, rfl⟩
  rw [← hTdef] at hT hTpos
  rw [← hTdef]
  refine ⟨(s + (T - 1) * m0) % T, Nat.mod_lt _ hTpos, ?_⟩
  have hmodeq : ((s + (T - 1) * m0) % T + m0) % T = s % T := by
    rw [Nat.mod_add_mod]
    have : s + (T - 1) * m0 + m0 = s + T * m0 := by
      have h1 : (T - 1) * m0 + m0 = T * m0 := by
        rw [← Nat.succ_mul]; congr 1; omega
      omega
    rw [this, Nat.add_mul_mod_self_left]
  generalize (s + (T - 1) * m0) % T = nz at hmodeq ⊢
  have e : residue (q ^ (K + 1)) w = residue (q ^ (K + 1)) (2 ^ m0) :=
    (residue_eq_iff _ _ _).2 hm0.symm
  have hA : residue (q ^ (K + 1)) (2 ^ nz) * residue (q ^ (K + 1)) w = b := by
    rw [e, ← residue_mul, ← Nat.pow_add]
    have f : residue (q ^ (K + 1)) (2 ^ (nz + m0)) = residue (q ^ (K + 1)) (2 ^ s) :=
      (residue_eq_iff _ _ _).2 (pow_two_mod_period _ T hT _ _ hmodeq)
    rw [f, (residue_eq_iff _ _ _).2 hs, residue_self_val]
  have hmain : residue (q ^ (K + 1)) (2 ^ (K + 1 + nz) * w)
      = residue (q ^ (K + 1)) (offset q (List.replicate (K + 1) 1)) := by
    rw [show 2 ^ (K + 1 + nz) = 2 ^ (K + 1) * 2 ^ nz from Nat.pow_add 2 (K + 1) nz,
      residue_mul, residue_mul, hO]
    grind
  exact (residue_eq_iff _ _ _).1 hmain

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
    grind

theorem linear_congruence (D N a : Nat) (hN : 0 < N) (hg : Nat.gcd D N ∣ a) :
    ∃ t : Nat, (N : Int) ∣ ((D : Int) * (t : Int) - (a : Int)) := by
  obtain ⟨x, y, hxy⟩ := bezout D N
  obtain ⟨c, hc⟩ := hg
  have ha : (a : Int) = (c : Int) * x * D + (c : Int) * y * N := by
    have h1 : (a : Int) = ((Nat.gcd D N : Nat) : Int) * (c : Int) := by
      rw [hc]; push_cast; grind
    rw [h1, hxy]; grind
  have hNi : (0 : Int) < N := by exact_mod_cast hN
  have hnn : (0 : Int) ≤ ((c : Int) * x) % (N : Int) := Int.emod_nonneg _ (by omega)
  refine ⟨(((c : Int) * x) % (N : Int)).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hnn]
  have e : ((c : Int) * x) % (N : Int) = (c : Int) * x - (N : Int) * (((c : Int) * x) / (N : Int)) :=
    Int.emod_def _ _
  rw [e, ha]
  exact ⟨-((c : Int) * y) - (D : Int) * (((c : Int) * x) / (N : Int)), by grind⟩

theorem exponent_linear (D d q j s : Nat) (_hD : 0 < D) (hdp : 0 < d * q ^ j)
    (hcompat : Nat.gcd D (d * q ^ j) ∣ d * s) :
    ∃ E : Nat, D ∣ E ∧ ((d * q ^ j : Nat) : Int) ∣ ((E : Int) - ((d * s : Nat) : Int)) := by
  obtain ⟨t, ht⟩ := linear_congruence D (d * q ^ j) (d * s) hdp hcompat
  refine ⟨D * t, Nat.dvd_mul_right D t, ?_⟩
  have : ((D * t : Nat) : Int) = (D : Int) * (t : Int) := by push_cast; rfl
  rw [this]
  exact ht

theorem gcd_compat (q K D' d j : Nat) (hD' : Nat.Coprime q D') :
    Nat.gcd (q ^ K * D') (d * q ^ j) ∣ d * q ^ K := by
  rcases Nat.le_total j K with hjK | hjK
  · have h1 : d * q ^ j ∣ d * q ^ K :=
      Nat.mul_dvd_mul_left d (Nat.pow_dvd_pow q hjK)
    exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) h1
  · obtain ⟨i, rfl⟩ : ∃ i, j = K + i := ⟨j - K, by omega⟩
    have e : d * q ^ (K + i) = q ^ K * (d * q ^ i) := by
      rw [Nat.pow_add]; grind
    rw [e, Nat.gcd_mul_left]
    have hc : Nat.Coprime D' (q ^ i) := (Nat.Coprime.pow_left i hD').symm
    have h2 : Nat.gcd D' (d * q ^ i) ∣ d := by
      rw [Nat.gcd_comm, Nat.Coprime.gcd_mul_right_cancel d hc.symm]
      exact Nat.gcd_dvd_left _ _
    rw [Nat.mul_comm d (q ^ K)]
    exact Nat.mul_dvd_mul_left _ h2

theorem int_dvd_sub_mod (E a T : Nat) (h : (T : Int) ∣ (E : Int) - (a : Int)) : E % T = a % T := by
  have h1 : ((E : Int) - (a : Int)) % (T : Int) = 0 := Int.emod_eq_zero_of_dvd h
  have h2 := (Int.emod_emod_of_dvd)
  have h3 : (E : Int) % (T : Int) = (a : Int) % (T : Int) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.2 h1
  exact_mod_cast h3

theorem exponent_padic (q : Nat) [NonWieferich q] {d u : Nat} (hd : 2 ^ d = 1 + q * u) (hu : Nat.Coprime q u)
    (K j w ℓ Y : Nat) (hw : ∃ i, w % q = 2 ^ i % q) (hKj : K ≤ j)
    (hY : Y % (q ^ (K + 1)) = (2 ^ ℓ * w) % (q ^ (K + 1))) :
    ∃ s, q ^ K ∣ s ∧ ∀ E, E % (d * q ^ j) = (d * s) % (d * q ^ j) →
      (2 ^ (ℓ + E) * w) % q ^ (j + 1) = Y % q ^ (j + 1) := by
  have hp := NonWieferich.odd (q := q)
  have hp3 := NonWieferich.three_le (q := q)
  have hone : ∀ n, 1 < q ^ (n + 1) := fun n =>
    Nat.lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) q)
  have hpm : q ^ (K + 1) ∣ q ^ (j + 1) := Nat.pow_dvd_pow q (by omega)
  obtain ⟨i, hi⟩ := hw
  have ha : (2 ^ ℓ * w) % q = 2 ^ (ℓ + i) % q := by
    rw [Nat.mul_mod, hi, ← Nat.mul_mod, ← Nat.pow_add]
  have hYp : Y % q = (2 ^ ℓ * w) % q := mod_of_dvd_mod (p_dvd_pow q K) hY
  have hInA : InPowTwo q j (2 ^ ℓ * w) := target_inPowTwo q ha j
  have hInY : InPowTwo q j Y := target_inPowTwo q (hYp.trans ha) j
  obtain ⟨j', hj'⟩ := inPowTwo_ratio q hInA hInY
  have hcopa : Nat.Coprime (q ^ (K + 1)) (2 ^ ℓ * w) :=
    Nat.Coprime.pow_left (K + 1)
      (Nat.Coprime.mul_right (Nat.Coprime.pow_right ℓ (coprime_p_two q)) (coprime_target q ⟨i, hi⟩))
  have hP1 : (2 ^ j' * (2 ^ ℓ * w)) % q ^ (K + 1) = (1 * (2 ^ ℓ * w)) % q ^ (K + 1) := by
    rw [Nat.one_mul, mod_of_dvd_mod hpm hj']
    exact hY
  have hg1 : 2 ^ j' % q ^ (K + 1) = 1 % q ^ (K + 1) := mod_cancel_mul_right hcopa hP1
  have hone' : 1 % q ^ (K + 1) = 1 := Nat.mod_eq_of_lt (hone K)
  have hgp : 2 ^ j' % q = 1 := by
    have := mod_of_dvd_mod (p_dvd_pow q K) hg1
    rw [this]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨t, -, ht⟩ := unit_power_cover hp hp3 hu j (2 ^ j') hgp
  have ht1 : (1 + q * u) ^ t % q ^ (K + 1) = 1 := by
    have e : (1 + q * u) ^ t % q ^ (K + 1) = 2 ^ j' % q ^ (K + 1) := by
      rw [← Nat.mod_mod_of_dvd ((1 + q * u) ^ t) hpm, ht, Nat.mod_mod_of_dvd _ hpm]
    rw [e, hg1, hone']
  have hpt : q ^ K ∣ t := (order_iff hp hp3 hu K t).1 ht1
  refine ⟨t, hpt, ?_⟩
  intro E hE
  have hT : 2 ^ (d * q ^ j) % q ^ (j + 1) = 1 % q ^ (j + 1) := by
    rw [Nat.pow_mul, hd, (order_iff hp hp3 hu j (q ^ j)).2 (Nat.dvd_refl _),
      Nat.mod_eq_of_lt (hone j)]
  have h2E := pow_two_mod_period (q ^ (j + 1)) (d * q ^ j) hT E (d * t) hE
  rw [Nat.pow_mul, hd, ht] at h2E
  have e2 : 2 ^ (ℓ + E) * w = 2 ^ E * (2 ^ ℓ * w) := by
    rw [Nat.pow_add]; grind
  rw [e2, Nat.mul_mod, h2E, ← Nat.mul_mod]
  exact hj'

theorem exponent_lemma (q : Nat) [NonWieferich q] {d u : Nat} (hd0 : 0 < d) (hd : 2 ^ d = 1 + q * u)
    (hu : Nat.Coprime q u) (m' K j w D' ℓ Y : Nat) (hM : Nat.Coprime m' (2 * q))
    (hw : ∃ i, w % q = 2 ^ i % q) (hD0 : 0 < D') (hD3 : Nat.Coprime q D')
    (hD : 2 ^ (q ^ K * D') % m' = 1 % m') (hKj : K ≤ j)
    (hY : Y % (q ^ (K + 1) * m') = (2 ^ ℓ * w) % (q ^ (K + 1) * m')) :
    ∃ E0, ∀ E, E % Nat.lcm (q ^ K * D') (d * q ^ j) = E0 % Nat.lcm (q ^ K * D') (d * q ^ j) →
      (2 ^ (ℓ + E) * w) % (q ^ (j + 1) * m') = Y % (q ^ (j + 1) * m') := by
  have hpK : 0 < q ^ K := powp_pos q K
  have hDpos : 0 < q ^ K * D' := Nat.mul_pos hpK hD0
  have hY1 : Y % q ^ (K + 1) = (2 ^ ℓ * w) % q ^ (K + 1) :=
    mod_of_dvd_mod (Nat.dvd_mul_right _ _) hY
  have hYM : Y % m' = (2 ^ ℓ * w) % m' := mod_of_dvd_mod (Nat.dvd_mul_left _ _) hY
  obtain ⟨s, hps, hs⟩ := exponent_padic q hd hu K j w ℓ Y hw hKj hY1
  have hdpj : 0 < d * q ^ j := Nat.mul_pos hd0 (powp_pos q j)
  have hcompat : Nat.gcd (q ^ K * D') (d * q ^ j) ∣ d * s :=
    Nat.dvd_trans (gcd_compat q K D' d j hD3) (Nat.mul_dvd_mul_left d hps)
  obtain ⟨E1, hE1D, hE1⟩ := exponent_linear (q ^ K * D') d q j s hDpos hdpj hcompat
  have hE1m : E1 % (d * q ^ j) = (d * s) % (d * q ^ j) := int_dvd_sub_mod _ _ _ hE1
  have hL0 : 0 < Nat.lcm (q ^ K * D') (d * q ^ j) := Nat.lcm_pos hDpos hdpj
  have hDL : q ^ K * D' ∣ Nat.lcm (q ^ K * D') (d * q ^ j) := Nat.dvd_lcm_left _ _
  have hPL : d * q ^ j ∣ Nat.lcm (q ^ K * D') (d * q ^ j) := Nat.dvd_lcm_right _ _
  refine ⟨E1, ?_⟩
  intro E hE
  have hED : E % (q ^ K * D') = E1 % (q ^ K * D') := mod_of_dvd_mod hDL hE
  have hEdv : (q ^ K * D') ∣ E := by
    have h0 : E1 % (q ^ K * D') = 0 := Nat.mod_eq_zero_of_dvd hE1D
    exact Nat.dvd_of_mod_eq_zero (hED.trans h0)
  have hET : E % (d * q ^ j) = (d * s) % (d * q ^ j) := by
    rw [mod_of_dvd_mod hPL hE]; exact hE1m
  have hpart := hs E hET
  obtain ⟨k, hk⟩ := hEdv
  have hMpart : (2 ^ (ℓ + E) * w) % m' = Y % m' := by
    have h2 : 2 ^ E % m' = 1 % m' := by rw [hk, Nat.pow_mul]; exact pow_period_pow m' _ hD k
    have e2 : 2 ^ (ℓ + E) * w = 2 ^ E * (2 ^ ℓ * w) := by rw [Nat.pow_add]; grind
    rw [e2, Nat.mul_mod, h2, ← Nat.mul_mod, Nat.one_mul, hYM]
  have hcop : Nat.Coprime (q ^ (j + 1)) m' := Nat.Coprime.pow_left (j + 1) (coprime_p_of_coprime_two_mul hM).symm
  exact mod_combine hcop hpart hMpart

theorem offset_le_pow (q : Nat) (hp : 2 ≤ q) : ∀ u : List Nat, (∀ e ∈ u, e ≤ 1) →
    offset q u ≤ q ^ oneCount u * 2 ^ u.length
  | [], _ => by simp [offset, oneCount]
  | e :: u, hu => by
    have hu' : ∀ d ∈ u, d ≤ 1 := fun d hd => hu d (by simp [hd])
    have ih := offset_le_pow q hp u hu'
    have he : e = 0 ∨ e = 1 := by have := hu e (by simp); omega
    have hB : 0 < 2 ^ u.length := Nat.pow_pos (by omega)
    have hA : 0 < q ^ oneCount u := Nat.pow_pos (by omega)
    rcases he with rfl | rfl
    · simp only [offset, oneCount, List.length_cons, Nat.add_zero, Nat.mul_zero, Nat.zero_add]
      rw [Nat.pow_succ (2 : Nat)]
      generalize q ^ oneCount u = A at *
      generalize 2 ^ u.length = B at *
      generalize offset q u = O at *
      have : A * (B * 2) = (A * B) * 2 := by grind
      omega
    · simp only [offset, oneCount, List.length_cons, Nat.mul_one]
      rw [Nat.pow_succ (2 : Nat), Nat.pow_succ q]
      generalize q ^ oneCount u = A at *
      generalize 2 ^ u.length = B at *
      generalize offset q u = O at *
      have h1 : A * 2 * (B * 2) ≤ A * q * (B * 2) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A hp)
      have h2 : A * 2 * (B * 2) = 4 * (A * B) := by grind
      have h3 : A ≤ A * B := Nat.le_mul_of_pos_right A hB
      omega

theorem exists_in_class (a e T : Nat) (hT : 0 < T) :
    ∃ E, e ≤ E ∧ E < e + T ∧ E % T = a % T := by
  refine ⟨e + (a + (T - e % T)) % T, by omega, ?_, ?_⟩
  · have := Nat.mod_lt (a + (T - e % T)) hT
    omega
  · rw [Nat.add_mod e, Nat.mod_mod, Nat.add_mod_mod]
    have h1 := Nat.mod_lt e hT
    have : e % T + (a + (T - e % T)) = a + T := by omega
    rw [this, Nat.add_mod_right]

theorem exists_pow_two_between (V ℓ : Nat) (hV : 2 ^ ℓ ≤ V) :
    ∃ e, V ≤ 2 ^ (ℓ + e) ∧ 2 ^ (ℓ + e) ≤ 2 * V := by
  have hex : ∃ e, V ≤ 2 ^ (ℓ + e) :=
    ⟨V, Nat.le_trans (Nat.le_of_lt Nat.lt_two_pow_self)
      (Nat.pow_le_pow_right (by omega) (by omega))⟩
  obtain ⟨e, he, hmin⟩ := exists_least _ hex
  refine ⟨e, he, ?_⟩
  cases e with
  | zero => simpa using Nat.le_trans hV (by omega : V ≤ 2 * V)
  | succ e =>
    have h := hmin e (by omega)
    have h2 : 2 ^ (ℓ + e) < V := Nat.lt_of_not_le h
    rw [show ℓ + (e + 1) = (ℓ + e) + 1 by omega, Nat.pow_succ]
    omega

theorem witness_exists (q o C z1 Z m' : Nat) (hpo : 0 < q ^ o) (hC : C ≤ Z)
    (h : Z % (q ^ o * m') = (q ^ o * z1 + C) % (q ^ o * m')) :
    ∃ z, Z = q ^ o * z + C ∧ z % m' = z1 % m' := by
  have h1 : Z % q ^ o = C % q ^ o := by
    rw [mod_of_dvd_mod (Nat.dvd_mul_right (q ^ o) m') h, Nat.add_comm, Nat.add_mul_mod_self_left]
  have h2 := Nat.sub_mod_eq_zero_of_mod_eq h1
  obtain ⟨z, hz⟩ := Nat.dvd_of_mod_eq_zero h2
  have hZ : Z = q ^ o * z + C := by omega
  refine ⟨z, hZ, ?_⟩
  rw [hZ, Nat.add_comm (q ^ o * z), Nat.add_comm (q ^ o * z1)] at h
  have h3 := mod_add_left_cancel h
  rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at h3
  exact Nat.eq_of_mul_eq_mul_left hpo h3

theorem parity_prefix (q : Nat) [NonWieferich q] : ∀ α x : Nat, ∃ u : List Nat, (∀ e ∈ u, e ≤ 1) ∧
    u.length = α ∧ 2 ^ α ∣ q ^ oneCount u * x + offset q u := by
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
      · simp only [oneCount, offset]
        have hn : q ^ (oneCount u + 0) * x + (q ^ oneCount u * 0 + 2 * offset q u)
            = 2 * (q ^ oneCount u * y + offset q u) := by subst hy; grind
        rw [hn, Nat.pow_succ']
        exact Nat.mul_dvd_mul_left 2 hd
    · obtain ⟨u, hu, hl, hd⟩ := ih (q * y + (q + 1) / 2)
      refine ⟨1 :: u, ?_, by simp [hl], ?_⟩
      · intro e he; simp at he; rcases he with rfl | he; omega; exact hu e he
      · simp only [oneCount, offset]
        have hn : q ^ (oneCount u + 1) * x + (q ^ oneCount u * 1 + 2 * offset q u)
            = 2 * (q ^ oneCount u * (q * y + (q + 1) / 2) + offset q u) := by
          subst hy; rw [Nat.pow_succ]
          generalize (q + 1) / 2 = c at hc ⊢
          grind
        rw [hn, Nat.pow_succ']
        exact Nat.mul_dvd_mul_left 2 hd

theorem prefix_mod (q : Nat) [NonWieferich q] (α o C x y : Nat)
    (hx : 2 ^ α ∣ q ^ o * x + C) (hy : 2 ^ α ∣ q ^ o * y + C) : x % 2 ^ α = y % 2 ^ α := by
  have hcop : Nat.Coprime (2 ^ α) (q ^ o) :=
    Nat.Coprime.pow _ _ (coprime_p_two q).symm
  have h1 : (C + q ^ o * x) % 2 ^ α = (C + q ^ o * y) % 2 ^ α := by
    rw [Nat.add_comm C, Nat.add_comm C, Nat.mod_eq_zero_of_dvd hx, Nat.mod_eq_zero_of_dvd hy]
  have h2 := mod_add_left_cancel h1
  rcases Nat.le_total y x with h | h
  · exact mod_cancel_mul_left hcop h h2
  · exact (mod_cancel_mul_left hcop h h2.symm).symm

theorem follow_prefix (q : Nat) [NonWieferich q] (u v : List Nat) (n : Nat)
    (h : 2 ^ (u ++ v).length ∣ q ^ oneCount (u ++ v) * n + offset q (u ++ v)) :
    2 ^ u.length ∣ q ^ oneCount u * n + offset q u := by
  rw [offset_append, oneCount_append, List.length_append, Nat.pow_add] at h
  have e : q ^ (oneCount u + oneCount v) * n + (q ^ oneCount v * offset q u + 2 ^ u.length * offset q v)
      = q ^ oneCount v * (q ^ oneCount u * n + offset q u) + 2 ^ u.length * offset q v := by
    rw [Nat.pow_add]; grind
  rw [e] at h
  have h1 := Nat.dvd_trans (Nat.dvd_mul_right _ _) h
  have h2 : 2 ^ u.length ∣ q ^ oneCount v * (q ^ oneCount u * n + offset q u) :=
    (Nat.dvd_add_right (Nat.dvd_mul_right _ _)).1 (by rwa [Nat.add_comm] at h1)
  exact (Nat.Coprime.pow _ _ (coprime_p_two q).symm).dvd_of_dvd_mul_left h2

theorem witness_size (P C ℓ E E0 Λ w n B : Nat) (hP : 0 < P) (hw : 1 ≤ w)
    (hC : C ≤ P * 2 ^ ℓ) (hn : P * n + C = 2 ^ (ℓ + E) * w)
    (h1 : P * (B + 1 + 2 ^ ℓ) ≤ 2 ^ (ℓ + E0)) (h2 : 2 ^ (ℓ + E0) ≤ 2 * (P * (B + 1 + 2 ^ ℓ)))
    (hE1 : E0 ≤ E) (hE2 : E < E0 + Λ) :
    B < n ∧ n ≤ (B + 1) * w * 2 ^ (Λ + ℓ + 1) := by
  have hGG : 2 ^ (ℓ + E0) ≤ 2 ^ (ℓ + E) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2G : 2 * 2 ^ (ℓ + E) ≤ 2 ^ (ℓ + E0) * 2 ^ Λ := by
    rw [← Nat.pow_succ', ← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have hT : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hpow : 2 ^ (Λ + ℓ + 1) = 2 ^ Λ * 2 ^ ℓ * 2 := by rw [Nat.pow_succ, Nat.pow_add]
  rw [hpow]
  generalize 2 ^ (ℓ + E) = G at *
  generalize 2 ^ (ℓ + E0) = G0 at *
  generalize 2 ^ Λ = S at *
  generalize 2 ^ ℓ = T at *
  constructor
  ·
    have hGw : G ≤ G * w := Nat.le_mul_of_pos_right _ (by omega)
    have e1 : P * (B + 1 + T) = P * (B + 1) + P * T := by grind
    have : P * (B + 1) ≤ P * n := by omega
    exact Nat.le_of_mul_le_mul_left this hP
  · have e1 : 2 * (P * n) ≤ 2 * G * w := by
      have : P * n ≤ G * w := by omega
      have := Nat.mul_le_mul_left 2 this; grind
    have e2 : 2 * G * w ≤ G0 * S * w := Nat.mul_le_mul_right _ h2G
    have e3 : G0 * S * w ≤ 2 * (P * (B + 1 + T)) * S * w :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h2)
    have e4 : 2 * (P * (B + 1 + T)) * S * w = 2 * (P * ((B + 1 + T) * S * w)) := by grind
    have e5 : P * n ≤ P * ((B + 1 + T) * S * w) := by omega
    have e6 := Nat.le_of_mul_le_mul_left e5 hP
    have e7 : B + 1 + T ≤ (B + 1) * T * 2 := by
      have : (B + 1) * T ≥ T := Nat.le_mul_of_pos_left _ (by omega)
      have : (B + 1) * T ≥ B + 1 := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have e8 : (B + 1 + T) * S * w ≤ (B + 1) * T * 2 * S * w :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ e7)
    have e9 : (B + 1) * T * 2 * S * w = (B + 1) * w * (S * T * 2) := by grind
    omega

theorem split_coprime (a : Nat) : ∀ X, 1 ≤ X → ∃ A Y k, X = A * Y ∧ Nat.Coprime Y a ∧ A ∣ a ^ k ∧ 2 ^ k ≤ A := by
  intro X
  induction X using Nat.strongRecOn with
  | _ X ih =>
    intro hX
    by_cases hc : Nat.Coprime X a
    · exact ⟨1, X, 0, by simp, hc, by simp, by simp⟩
    · have hg1 : Nat.gcd X a ≠ 1 := hc
      have hg0 : 0 < Nat.gcd X a := Nat.gcd_pos_of_pos_left _ (by omega)
      obtain ⟨X1, hX1⟩ := Nat.gcd_dvd_left X a
      have hga := Nat.gcd_dvd_right X a
      generalize Nat.gcd X a = g at hg1 hg0 hX1 hga
      have hX10 : 1 ≤ X1 := by
        apply Classical.byContradiction; intro h
        have : X1 = 0 := by omega
        rw [this, Nat.mul_zero] at hX1; omega
      have hlt : X1 < X := by
        have : X1 * 2 ≤ X1 * g := Nat.mul_le_mul_left _ (by omega)
        have e : X1 * g = g * X1 := Nat.mul_comm _ _
        omega
      obtain ⟨A1, Y, k, h1, h2, h3, h4⟩ := ih X1 hlt hX10
      refine ⟨g * A1, Y, k + 1, ?_, h2, ?_, ?_⟩
      · rw [hX1, h1, Nat.mul_assoc]
      · rw [Nat.pow_succ, Nat.mul_comm (a ^ k)]
        exact Nat.mul_dvd_mul hga h3
      · rw [Nat.pow_succ, Nat.mul_comm]
        exact Nat.mul_le_mul (by omega) h4

theorem split_two_power : ∀ m, 1 ≤ m → ∃ α O, m = 2 ^ α * O ∧ O % 2 = 1 := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro hN
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · obtain ⟨α, O, h1, h2⟩ := ih (m / 2) (by omega) (by omega)
      exact ⟨α + 1, O, by rw [Nat.pow_succ, Nat.mul_comm (2 ^ α) 2, Nat.mul_assoc, ← h1]; omega, h2⟩
    · exact ⟨0, m, by simp, h⟩

namespace TS

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
  have key : r * a = 1 - (y + c * a) * m' := by grind
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
    grind
  exact_mod_cast this

def card (m' : Nat) (S : Nat → Bool) : Nat := (List.range m').countP S

theorem countP_union_inter {α} (S T : α → Bool) (l : List α) :
    l.countP (fun x => S x || T x) + l.countP (fun x => S x && T x)
      = l.countP S + l.countP T := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.countP_cons]
    cases S x <;> cases T x <;> simp <;> omega

theorem countP_split {α} (S T : α → Bool) (l : List α) (h : ∀ x ∈ l, S x → T x) :
    l.countP T = l.countP S + l.countP (fun x => T x && !S x) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.countP_cons]
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (List.mem_cons_self ..)
    cases hS : S x <;> cases hT : T x <;> simp_all <;> omega

variable {m' : Nat}

theorem card_le (S : Nat → Bool) : card m' S ≤ m' := by
  unfold card; have := List.countP_le_length (p := S) (l := List.range m'); simpa using this

theorem card_mono {S T : Nat → Bool} (h : ∀ x, x < m' → S x → T x) : card m' S ≤ card m' T :=
  List.countP_mono_left (fun x hx => h x (List.mem_range.mp hx))

theorem card_congr {S T : Nat → Bool} (h : ∀ x, x < m' → S x = T x) : card m' S = card m' T :=
  List.countP_congr (fun x hx => by rw [h x (List.mem_range.mp hx)])

theorem card_union_inter (S T : Nat → Bool) :
    card m' (fun x => S x || T x) + card m' (fun x => S x && T x) = card m' S + card m' T :=
  countP_union_inter S T _

theorem eq_of_card {S T : Nat → Bool} (h : ∀ x, x < m' → S x → T x)
    (hc : card m' T ≤ card m' S) : ∀ x, x < m' → T x → S x := by
  intro x hx hT
  have e := countP_split S T (List.range m') (fun y hy => h y (List.mem_range.mp hy))
  unfold card at hc
  have z : (List.range m').countP (fun y => T y && !S y) = 0 := by omega
  rw [List.countP_eq_zero] at z
  have := z x (List.mem_range.mpr hx)
  cases hS : S x <;> simp_all

theorem card_lt {S T : Nat → Bool} (h : ∀ x, x < m' → S x → T x)
    (x : Nat) (hx : x < m') (hT : T x) (hS : S x = false) : card m' S < card m' T := by
  have := card_mono h
  cases Nat.lt_or_ge (card m' S) (card m' T) with
  | inl l => exact l
  | inr g => have := eq_of_card h g x hx hT; simp_all

theorem card_full {S : Nat → Bool} (h : ∀ x, x < m' → S x) : card m' S = m' := by
  unfold card; rw [List.countP_eq_length.mpr (fun x hx => h x (List.mem_range.mp hx))]; simp

theorem card_le_one_zero {S : Nat → Bool} (h : ∀ x, x < m' → S x → x = 0) : card m' S ≤ 1 := by
  cases m' with
  | zero => simp [card]
  | succ n =>
    unfold card
    rw [List.range_succ_eq_map, List.countP_cons, List.countP_map]
    have : (List.range n).countP (S ∘ Nat.succ) = 0 := by
      rw [List.countP_eq_zero]; intro y hy hS
      have := h (y+1) (by have := List.mem_range.mp hy; omega) hS; omega
    rw [this]; cases S 0 <;> simp

theorem card_shift1 (hm : 0 < m') (S : Nat → Bool) :
    card m' (fun x => S ((x + 1) % m')) = card m' S := by
  obtain ⟨n, rfl⟩ : ∃ n, m' = n + 1 := ⟨m' - 1, by omega⟩
  unfold card
  conv => lhs; rw [List.range_succ, List.countP_append]
  conv => rhs; rw [List.range_succ_eq_map, List.countP_cons, List.countP_map]
  have : (List.range n).countP (fun x => S ((x + 1) % (n + 1))) = (List.range n).countP (S ∘ Nat.succ) :=
    List.countP_congr (fun x hx => by
      have := List.mem_range.mp hx
      simp [Nat.mod_eq_of_lt (show x + 1 < n + 1 by omega)])
  rw [this]; simp [Nat.mod_self]

theorem card_shift (hm : 0 < m') (S : Nat → Bool) (u : Nat) :
    card m' (fun x => S ((x + u) % m')) = card m' S := by
  induction u with
  | zero => exact card_congr (fun x hx => by simp [Nat.mod_eq_of_lt hx])
  | succ u ih =>
    rw [← ih, ← card_shift1 hm (fun x => S ((x + u) % m'))]
    exact card_congr (fun x _ => by
      simp only [Nat.mod_add_mod]; congr 2; omega)

variable {m' : Nat}

theorem md (y m' : Nat) (h : y < 2*m') : (y < m' ∧ y % m' = y) ∨ (m' ≤ y ∧ y % m' = y - m') := by
  cases Nat.lt_or_ge y m' with
  | inl l => exact Or.inl ⟨l, Nat.mod_eq_of_lt l⟩
  | inr g => exact Or.inr ⟨g, by rw [Nat.mod_eq_sub_mod g, Nat.mod_eq_of_lt (by omega)]⟩

def add (m' : Nat) (A B : Nat → Bool) (x : Nat) : Bool :=
  (List.range m').any (fun a => A a && B ((x + (m' - a)) % m'))

theorem mem_add {A B : Nat → Bool} {x : Nat} :
    add m' A B x = true ↔ ∃ a, a < m' ∧ A a = true ∧ B ((x + (m' - a)) % m') = true := by
  simp [add, List.any_eq_true, List.mem_range]

theorem sub_add_eq (a b : Nat) (ha : a < m') (hb : b < m') : ((a + b) % m' + (m' - a)) % m' = b := by
  rcases md (a+b) m' (by omega) with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rw [e1]
  · rcases md (a + b + (m' - a)) m' (by omega) with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;> rw [e2] <;> omega
  · rcases md (a + b - m' + (m' - a)) m' (by omega) with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;> rw [e2] <;> omega

theorem add_of {A B : Nat → Bool} {a b : Nat} (ha : a < m') (hb : b < m')
    (hA : A a = true) (hB : B b = true) : add m' A B ((a + b) % m') = true :=
  mem_add.mpr ⟨a, ha, hA, by rw [sub_add_eq a b ha hb]; exact hB⟩

theorem closed_full (hm : 1 < m') (A : Nat → Bool) (a0 : Nat) (ha0 : a0 < m') (hA : A a0 = true)
    (b : Nat) (hcop : Nat.gcd b m' = 1)
    (hcl : ∀ a, a < m' → A a = true → A ((a + b) % m') = true) : ∀ x, x < m' → A x = true := by
  have step : ∀ k, A ((a0 + k*b) % m') = true := by
    intro k; induction k with
    | zero => simpa [Nat.mod_eq_of_lt ha0] using hA
    | succ k ih =>
      have := hcl _ (Nat.mod_lt _ (by omega)) ih
      rw [Nat.mod_add_mod] at this
      have e : a0 + k*b + b = a0 + (k+1)*b := by rw [Nat.succ_mul]; omega
      rwa [e] at this
  obtain ⟨k0, w, hbk⟩ := nat_bez b m' hm hcop
  intro x hx
  have := step (k0 * (x + m' - a0))
  have e : a0 + k0 * (x + m' - a0) * b = (x + m') + m' * ((x + m' - a0) * w) := by
    generalize ht : x + m' - a0 = t
    have : a0 + t = x + m' := by omega
    rw [← this]
    have : k0 * t * b = t * (b * k0) := by grind
    rw [this, hbk]; grind
  rw [e, Nat.add_mul_mod_self_left, Nat.add_mod_right, Nat.mod_eq_of_lt hx] at this
  exact this

theorem card_le_add {A B : Nat → Bool} (hB : B 0 = true) : card m' A ≤ card m' (add m' A B) :=
  card_mono (fun x hx hA => mem_add.mpr ⟨x, hx, hA, by
    rw [show x + (m' - x) = m' by omega, Nat.mod_self]; exact hB⟩)

theorem mod_eq3 (x a a1 : Nat) (hx : x < m') (ha : a < m') (ha1 : a1 < m') :
    (x + (m' - ((x + (m' - a1)) % m' + a) % m')) % m' = (a1 + (m' - a)) % m' := by
  have h1 := md (x + (m' - a1)) m' (by omega)
  generalize (x + (m' - a1)) % m' = b1 at *
  have hb1 : b1 < m' := by omega
  have h2 := md (b1 + a) m' (by omega)
  generalize (b1 + a) % m' = a2 at *
  have ha2 : a2 < m' := by omega
  have h3 := md (x + (m' - a2)) m' (by omega)
  have h4 := md (a1 + (m' - a)) m' (by omega)
  generalize (x + (m' - a2)) % m' = l at *
  generalize (a1 + (m' - a)) % m' = r at *
  omega

theorem chowla (hm : 0 < m') : ∀ n (A B : Nat → Bool), card m' B = n →
    (∃ a, a < m' ∧ A a = true) → B 0 = true →
    (∀ b, b < m' → B b = true → b ≠ 0 → Nat.gcd b m' = 1) →
    min m' (card m' A + card m' B - 1) ≤ card m' (add m' A B) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro A B hn hA hB0 hunit
  obtain ⟨a0, ha0, hAa0⟩ := hA
  by_cases hc : ∃ a b, a < m' ∧ b < m' ∧ A a = true ∧ B b = true ∧ A ((a + b) % m') = false
  · obtain ⟨a, b, ha, hb, hAa, hBb, hn'⟩ := hc
    let T : Nat → Bool := fun x => B ((x + (m' - a)) % m')
    let A' : Nat → Bool := fun x => A x || T x
    let B' : Nat → Bool := fun x => B x && A ((x + a) % m')
    have hB'B : ∀ x, x < m' → B' x = true → B x = true := by
      intro x _ h; simp only [B', Bool.and_eq_true] at h; exact h.1
    have hlt : card m' B' < card m' B := card_lt hB'B b hb hBb (by
      simp only [B', hBb, Bool.true_and]; rw [Nat.add_comm]; exact hn')
    have hB'0 : B' 0 = true := by simp [B', hB0, Nat.mod_eq_of_lt ha, hAa]
    have IH := ih _ (hn ▸ hlt) A' B' rfl ⟨a0, ha0, by simp [A', hAa0]⟩ hB'0
      (fun x hx h hne => hunit x hx (hB'B x hx h) hne)
    have hT : card m' T = card m' B := card_shift hm B (m' - a)
    have hI : card m' (fun x => A x && T x) = card m' B' := by
      rw [← card_shift hm (fun x => A x && T x) a]
      apply card_congr; intro x hx
      simp only [B', T]
      rw [Nat.add_comm x a, sub_add_eq a x ha hx, Bool.and_comm]
    have hU := card_union_inter (m' := m') A T
    have hsub : card m' (add m' A' B') ≤ card m' (add m' A B) := by
      apply card_mono; intro x hx h
      obtain ⟨a1, ha1, hA'1, hB'1⟩ := mem_add.mp h
      simp only [B', Bool.and_eq_true] at hB'1
      simp only [A', T, Bool.or_eq_true] at hA'1
      rcases hA'1 with h1 | h1
      · exact mem_add.mpr ⟨a1, ha1, h1, hB'1.1⟩
      · refine mem_add.mpr ⟨_, Nat.mod_lt _ hm, hB'1.2, ?_⟩
        rw [mod_eq3 x a a1 hx ha ha1]; exact h1
    have : card m' A' + card m' B' = card m' A + card m' B := by
      simp only [A']; omega
    omega
  · have hcl : ∀ a b, a < m' → b < m' → A a = true → B b = true → A ((a + b) % m') = true := by
      intro a b ha hb hAa hBb
      cases h : A ((a + b) % m')
      · exact absurd ⟨a, b, ha, hb, hAa, hBb, h⟩ hc
      · rfl
    have hle := card_le_add (m' := m') (A := A) hB0
    by_cases hnz : ∃ b, b < m' ∧ B b = true ∧ b ≠ 0
    · obtain ⟨b, hb, hBb, hb0⟩ := hnz
      have full := closed_full (by omega) A a0 ha0 hAa0 b (hunit b hb hBb hb0)
        (fun a ha hAa => hcl a b ha hb hAa hBb)
      have := card_full (m' := m') full
      have := card_le (m' := m') (add m' A B)
      omega
    · have : card m' B ≤ 1 := card_le_one_zero (fun x hx hBx => by
        cases Nat.decEq x 0 with
        | isTrue h => exact h
        | isFalse h => exact absurd ⟨x, hx, hBx, h⟩ hnz)
      omega

variable {m' : Nat}

theorem card_single {y : Nat} (hy : y < m') : card m' (fun x => x == y) = 1 := by
  unfold card
  rw [← List.count_eq_countP]
  exact List.Nodup.count_of_mem List.nodup_range (List.mem_range.mpr hy)

theorem card_zero {S : Nat → Bool} (h : ∀ x, x < m' → S x = false) : card m' S = 0 := by
  unfold card; rw [List.countP_eq_zero]; intro x hx; simp [h x (List.mem_range.mp hx)]

theorem card_image (f : Nat → Nat) : ∀ (L : List Nat), L.Nodup → (∀ i ∈ L, f i < m') →
    (∀ i ∈ L, ∀ j ∈ L, f i = f j → i = j) →
    card m' (fun x => L.any (fun i => f i == x)) = L.length := by
  intro L
  induction L with
  | nil => intros; exact card_zero (fun x _ => by simp)
  | cons a L ih =>
    intro hL hf hinj
    rw [List.nodup_cons] at hL
    have ih' := ih hL.2 (fun i hi => hf i (List.mem_cons_of_mem _ hi))
      (fun i hi j hj h => hinj i (List.mem_cons_of_mem _ hi) j (List.mem_cons_of_mem _ hj) h)
    have hU := card_union_inter (m' := m') (fun x => x == f a) (fun x => L.any (fun i => f i == x))
    have h1 := card_single (m' := m') (hf a (List.mem_cons_self ..))
    have h0 : card m' (fun x => (x == f a) && L.any (fun i => f i == x)) = 0 := card_zero (fun x _ => by
      cases hx : (x == f a) <;> simp only [Bool.false_and, Bool.true_and]
      simp only [beq_iff_eq] at hx; subst hx
      rw [Bool.eq_false_iff]; intro hc
      simp only [List.any_eq_true, beq_iff_eq] at hc
      obtain ⟨i, hi, hfi⟩ := hc
      have := hinj a (List.mem_cons_self ..) i (List.mem_cons_of_mem _ hi) hfi.symm
      exact hL.1 (this ▸ hi))
    have e : card m' (fun x => (a :: L).any (fun i => f i == x))
        = card m' (fun x => (x == f a) || L.any (fun i => f i == x)) :=
      card_congr (fun x _ => by simp only [List.any_cons]; congr 1; exact Bool.beq_comm)
    simp only [List.length_cons]; omega

section
variable {m' q e : Nat} (hm : 1 < m') (hodd : m' % 2 = 1) (hq : Nat.gcd q m' = 1)
  (he : 2 ^ e % m' = 1) (hmin : ∀ i, 0 < i → i < e → 2 ^ i % m' ≠ 1) (he0 : 0 < e)

include hm hodd he he0 in
theorem two_le_e : 2 ≤ e := by
  cases Nat.lt_or_ge e 2 with
  | inr h => exact h
  | inl h =>
    have : e = 1 := by omega
    subst this
    rw [Nat.pow_one, Nat.mod_eq_of_lt (by omega)] at he; omega

theorem pow_mod_one {g a : Nat} (k : Nat) (h : a % g = 1 % g) : a ^ k % g = 1 % g := by
  rw [Nat.pow_mod, h]
  cases Nat.lt_or_ge g 2 with
  | inl hg =>
    cases Nat.lt_or_ge g 1 with
    | inl h0 => have : g = 0 := by omega
                subst this; simp
    | inr h1 => have : g = 1 := by omega
                subst this; simp [Nat.mod_one]
  | inr hg => rw [Nat.mod_eq_of_lt (by omega : 1 < g), Nat.one_pow]; exact Nat.mod_eq_of_lt (by omega)

include hm hodd he he0 in
theorem unit_two_pow_sub_one (i : Nat) (hi : Nat.gcd i e = 1) : Nat.gcd (2 ^ i - 1) m' = 1 := by
  have e2 := two_le_e hm hodd he he0
  generalize hg : Nat.gcd (2 ^ i - 1) m' = g
  have hg1 : g ∣ 2 ^ i - 1 := hg ▸ Nat.gcd_dvd_left _ _
  have hg2 : g ∣ m' := hg ▸ Nat.gcd_dvd_right _ _
  have hgpos : 0 < g := hg ▸ Nat.gcd_pos_of_pos_right _ (by omega)
  have A : 2 ^ i % g = 1 % g := by
    obtain ⟨c, hc⟩ := hg1
    have := Nat.two_pow_pos i
    rw [show 2 ^ i = 1 + g * c by omega, Nat.add_mul_mod_self_left]
  have B : 2 ^ e % g = 1 % g := by rw [← Nat.mod_mod_of_dvd _ hg2, he]
  obtain ⟨k, w, hkw⟩ := nat_bez i e (by omega) hi
  have C := pow_mod_one k A
  rw [← Nat.pow_mul, hkw, Nat.pow_succ, Nat.pow_mul, Nat.mul_mod, pow_mod_one w B] at C
  rcases (by omega : g = 1 ∨ g = 2 ∨ 3 ≤ g) with h | h | h
  · exact h
  · subst h; simp at C
  · have : 2 % g = 2 := Nat.mod_eq_of_lt (by omega)
    have : 1 % g = 1 := Nat.mod_eq_of_lt (by omega)
    simp_all

include hm hodd hq hmin in
theorem distinct (s i j : Nat) (hij : i < j) (hj : j < e) :
    (q ^ s * (2 ^ i - 1)) % m' ≠ (q ^ s * (2 ^ j - 1)) % m' := by
  intro h
  have m2 : Nat.Coprime m' 2 := by
    show Nat.gcd m' 2 = 1
    rw [Nat.gcd_comm, Nat.gcd_rec, hodd]; rfl
  have cQP : Nat.Coprime m' (q ^ s * 2 ^ i) :=
    Nat.Coprime.mul_right (Nat.Coprime.pow_right s (by show Nat.gcd m' q = 1; rw [Nat.gcd_comm]; exact hq))
      (Nat.Coprime.pow_right i m2)
  have hnot := hmin (j - i) (by omega) (by omega)
  have h0 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
  have hP := Nat.two_pow_pos i
  have hR := Nat.two_pow_pos (j - i)
  have hj' : 2 ^ j = 2 ^ i * 2 ^ (j - i) := by rw [← Nat.pow_add]; congr 1; omega
  rw [hj'] at h0
  generalize 2 ^ i = P at *
  generalize 2 ^ (j - i) = R at *
  generalize q ^ s = Q at *
  have key : Q * (P * R - 1) - Q * (P - 1) = (Q * P) * (R - 1) := by
    rw [Nat.mul_sub_one, Nat.mul_sub_one, Nat.mul_sub_one, Nat.mul_assoc]
    have : Q * P ≤ Q * (P * R) := Nat.mul_le_mul_left _ (by
      have := Nat.mul_le_mul_left P hR; simpa using this)
    have : Q ≤ Q * P := by have := Nat.mul_le_mul_left Q hP; simpa using this
    omega
  rw [key] at h0
  have hd := Nat.Coprime.dvd_of_dvd_mul_left cQP (Nat.dvd_of_mod_eq_zero h0)
  obtain ⟨c, hc⟩ := hd
  apply hnot
  rw [show R = 1 + m' * c by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm]
end

def Hq (m' q e s : Nat) (x : Nat) : Bool := (List.range e).any (fun i => (q ^ s * 2 ^ i) % m' == x)

def As (m' q e : Nat) : Nat → Nat → Bool
  | 0 => fun x => x == 0
  | s + 1 => add m' (As m' q e s) (Hq m' q e s)

def good (e i : Nat) : Bool := i == 0 || Nat.gcd i e == 1
def Lg (e : Nat) : List Nat := (List.range e).filter (good e)
def fD (m' q s i : Nat) : Nat := (q ^ s * (2 ^ i - 1)) % m'
def D (m' q e s : Nat) (x : Nat) : Bool := (Lg e).any (fun i => fD m' q s i == x)

def phi (e : Nat) : Nat := card e (fun i => Nat.gcd i e == 1)

theorem mod_eq4 {m' : Nat} (x a c : Nat) (hx : x < m') (ha : a < m') (hc : c < m') :
    (((x + (m' - c)) % m' + (m' - a)) % m' + c) % m' = (x + (m' - a)) % m' := by
  have h1 := md (x + (m' - c)) m' (by omega)
  generalize (x + (m' - c)) % m' = y at *
  have h2 := md (y + (m' - a)) m' (by omega)
  generalize (y + (m' - a)) % m' = z at *
  have h3 := md (z + c) m' (by omega)
  have h4 := md (x + (m' - a)) m' (by omega)
  generalize (z + c) % m' = l at *
  generalize (x + (m' - a)) % m' = r at *
  omega

section
variable {m' q e : Nat} (hm : 1 < m') (hodd : m' % 2 = 1) (hq : Nat.gcd q m' = 1)
  (he : 2 ^ e % m' = 1) (hmin : ∀ i, 0 < i → i < e → 2 ^ i % m' ≠ 1) (he0 : 0 < e)

include hm hodd he he0 in
theorem length_Lg : (Lg e).length = phi e + 1 := by
  have e2 := two_le_e hm hodd he he0
  have hU := card_union_inter (m' := e) (fun i => i == 0) (fun i => Nat.gcd i e == 1)
  have h1 := card_single (m' := e) (y := 0) he0
  have h0 : card e (fun i => (i == 0) && (Nat.gcd i e == 1)) = 0 := card_zero (fun x _ => by
    cases hx : (x == 0) <;> simp only [Bool.false_and, Bool.true_and]
    simp only [beq_iff_eq] at hx; subst hx; simp; omega)
  have : (Lg e).length = card e (good e) := by
    unfold Lg card; rw [List.countP_eq_length_filter]
  unfold phi; unfold good at this; omega

include hm hodd hq he hmin he0 in
theorem card_D (s : Nat) : card m' (D m' q e s) = phi e + 1 := by
  rw [← length_Lg hm hodd he he0]
  apply card_image
  · exact List.nodup_range.sublist List.filter_sublist
  · intro i _; exact Nat.mod_lt _ (by omega)
  · intro i hi j hj h
    have hi' := List.mem_range.mp (List.mem_filter.mp hi).1
    have hj' := List.mem_range.mp (List.mem_filter.mp hj).1
    rcases Nat.lt_trichotomy i j with l | l | l
    · exact absurd h (distinct hm hodd hq hmin s i j l hj')
    · exact l
    · exact absurd h.symm (distinct hm hodd hq hmin s j i l hi')

include hm hodd hq he he0 in
theorem D_unit (s : Nat) : ∀ b, b < m' → D m' q e s b = true → b ≠ 0 → Nat.gcd b m' = 1 := by
  intro b _ hb hb0
  simp only [D, List.any_eq_true, beq_iff_eq] at hb
  obtain ⟨i, hi, rfl⟩ := hb
  have hg := (List.mem_filter.mp hi).2
  simp only [good, Bool.or_eq_true, beq_iff_eq] at hg
  rcases hg with h | h
  · subst h; simp [fD] at hb0
  · unfold fD
    rw [← Nat.gcd_rec, Nat.gcd_comm]
    exact Nat.Coprime.symm (Nat.Coprime.mul_right (Nat.Coprime.symm (Nat.Coprime.pow_left s hq))
      (Nat.Coprime.symm (unit_two_pow_sub_one hm hodd he he0 i h)))

include he0 in
theorem D_zero (s : Nat) : D m' q e s 0 = true := by
  simp only [D, List.any_eq_true, beq_iff_eq]
  exact ⟨0, List.mem_filter.mpr ⟨List.mem_range.mpr he0, by simp [good]⟩, by simp [fD]⟩

include hm in
theorem shift_sub (s : Nat) : ∀ x, x < m' →
    add m' (As m' q e s) (D m' q e s) ((x + (m' - q ^ s % m')) % m') = true → As m' q e (s + 1) x = true := by
  intro x hx h
  obtain ⟨a, ha, hA, hDa⟩ := mem_add.mp h
  simp only [D, List.any_eq_true, beq_iff_eq] at hDa
  obtain ⟨i, hi, hfi⟩ := hDa
  refine mem_add.mpr ⟨a, ha, hA, ?_⟩
  simp only [Hq, List.any_eq_true, beq_iff_eq, List.mem_range]
  refine ⟨i, List.mem_range.mp (List.mem_filter.mp hi).1, ?_⟩
  have hP := Nat.two_pow_pos i
  have : q ^ s * 2 ^ i = q ^ s * (2 ^ i - 1) + q ^ s := by
    rw [Nat.mul_sub_one]; have := Nat.mul_le_mul_left (q ^ s) hP; simp at this; omega
  rw [this, Nat.add_mod, ← fD, hfi]
  exact mod_eq4 x a _ hx ha (Nat.mod_lt _ (by omega))

include he0 in
theorem As_nonempty (hm0 : 0 < m') : ∀ s, ∃ a, a < m' ∧ As m' q e s a = true := by
  intro s; induction s with
  | zero => exact ⟨0, hm0, by simp [As]⟩
  | succ s ih =>
    obtain ⟨a, ha, h⟩ := ih
    refine ⟨_, Nat.mod_lt _ hm0, add_of ha (Nat.mod_lt (q ^ s) hm0) h ?_⟩
    simp only [Hq, List.any_eq_true, beq_iff_eq, List.mem_range]
    exact ⟨0, he0, by simp⟩

include hm hodd hq he hmin he0 in
theorem growth : ∀ s, min m' (1 + s * phi e) ≤ card m' (As m' q e s) := by
  intro s; induction s with
  | zero =>
    have := card_single (m' := m') (y := 0) (by omega)
    simp only [As, Nat.zero_mul]; omega
  | succ s ih =>
    have hc := chowla (m' := m') (by omega) _ (As m' q e s) (D m' q e s) rfl
      (As_nonempty he0 (by omega) s) (D_zero he0 s) (D_unit hm hodd hq he he0 s)
    rw [card_D hm hodd hq he hmin he0 s] at hc
    have hsh := card_shift (m' := m') (by omega) (add m' (As m' q e s) (D m' q e s)) (m' - q ^ s % m')
    have hmono := card_mono (m' := m') (shift_sub (q := q) (e := e) hm s)
    rw [Nat.succ_mul]; omega

include hm hodd hq he hmin he0 in
theorem covers (s : Nat) (hs : m' ≤ 1 + s * phi e) : ∀ x, x < m' → As m' q e s x = true := by
  have g := growth hm hodd hq he hmin he0 s
  have hle := card_le (m' := m') (As m' q e s)
  have hfull := card_full (m' := m') (S := fun _ => true) (fun _ _ => rfl)
  intro x hx
  exact eq_of_card (S := As m' q e s) (T := fun _ => true) (fun _ _ _ => rfl) (by omega) x hx rfl
end
end TS

def spread (D : Nat) : List Nat → List Nat
  | [] => []
  | i :: is => List.replicate i 0 ++ [1] ++ List.replicate (D - 1 - i) 0 ++ spread D is

def wsum (q : Nat) : List Nat → Nat
  | [] => 0
  | i :: is => q ^ is.length * 2 ^ i + wsum q is

theorem spread_binary (D : Nat) (is : List Nat) : ∀ e ∈ spread D is, e ≤ 1 := by
  induction is with
  | nil => simp [spread]
  | cons i is ih =>
    intro e he
    simp only [spread, List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil] at he
    rcases he with ((⟨_, rfl⟩ | rfl | h) | ⟨_, rfl⟩) | h
    all_goals first | omega | exact ih e h | simp_all

theorem oneCount_spread (D : Nat) (is : List Nat) : oneCount (spread D is) = is.length := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [spread, oneCount_append, oneCount_replicate_zero, ih, List.length_cons]
    simp [oneCount]; omega

theorem length_spread (D : Nat) (is : List Nat) (h : ∀ i ∈ is, i < D) :
    (spread D is).length = D * is.length := by
  induction is with
  | nil => simp [spread]
  | cons i is ih =>
    have hi := h i (by simp)
    have := ih (fun j hj => h j (by simp [hj]))
    simp only [spread, List.length_append, List.length_replicate, List.length_cons, List.length_nil, this]
    rw [Nat.mul_succ]; omega

theorem offset_block (q D i : Nat) :
    offset q (List.replicate i 0 ++ [1] ++ List.replicate (D - 1 - i) 0) = 2 ^ i := by
  rw [offset_append, offset_replicate_zero, Nat.mul_zero, Nat.add_zero, oneCount_replicate_zero,
    Nat.pow_zero, Nat.one_mul, offset_append, offset_replicate_zero, List.length_replicate]
  simp [offset, oneCount]

theorem offset_spread (q D m' : Nat) (hD : 2 ^ D % m' = 1 % m') (is : List Nat)
    (h : ∀ i ∈ is, i < D) : offset q (spread D is) % m' = wsum q is % m' := by
  induction is with
  | nil => simp [spread, wsum, offset]
  | cons i is ih =>
    have ih' := ih (fun j hj => h j (by simp [hj]))
    have hblk : (List.replicate i 0 ++ [1] ++ List.replicate (D - 1 - i) 0).length = D := by
      have := h i (by simp); simp [List.length_append]; omega
    simp only [spread]
    rw [offset_append, offset_block, oneCount_spread, hblk]
    have h2 : (2 ^ D * offset q (spread D is)) % m' = wsum q is % m' := by
      rw [Nat.mul_mod, hD, ← Nat.mul_mod, Nat.one_mul, ih']
    simp only [wsum]
    rw [Nat.add_mod, h2, ← Nat.add_mod]

section
variable {m' : Nat} [NeZero m']

theorem backWord_spread (q : Nat) [Invertible2p q m'] (D : Nat) (hD : 2 ^ D % m' = 1 % m')
    (is : List Nat) (h : ∀ i ∈ is, i < D) (z t : Fin m') :
    backWord q (spread D is) z = t ↔
      residue m' (q ^ is.length) * z + residue m' (wsum q is) = t := by
  rw [← backWord_iff, oneCount_spread, length_spread D is h]
  have h1 : residue m' (2 ^ (D * is.length)) = 1 := by
    rw [← residue_one, residue_eq_iff, Nat.pow_mul]; exact pow_period_pow m' D hD _
  have h2 : residue m' (offset q (spread D is)) = residue m' (wsum q is) :=
    (residue_eq_iff _ _ _).2 (offset_spread q D m' hD is h)
  rw [h1, h2, Fin.one_mul]

theorem sparse_word (q : Nat) [Invertible2p q m'] (D s : Nat) (hD : 2 ^ D % m' = 1 % m')
    (hcov : ∀ c : Fin m', ∃ is : List Nat, is.length = s ∧ (∀ i ∈ is, i < D) ∧
      residue m' (wsum q is) = c)
    (z t : Fin m') :
    ∃ ω : List Nat, (∀ e ∈ ω, e ≤ 1) ∧ oneCount ω = s ∧ ω.length = D * s ∧
      backWord q ω z = t := by
  obtain ⟨is, hl, hi, hw⟩ := hcov (t - residue m' (q ^ s) * z)
  refine ⟨spread D is, spread_binary D is, by rw [oneCount_spread, hl], by rw [length_spread D is hi, hl], ?_⟩
  rw [backWord_spread q D hD is hi, hl, hw]
  grind
end

def Covers (q m' s : Nat) : Prop :=
  ∀ x, x < m' → ∃ I : List Nat, I.length = s ∧ wsum q I % m' = x % m'

theorem As_wsum (q m' e : Nat) (hm0 : 0 < m') : ∀ s x, x < m' → TS.As m' q e s x = true →
    ∃ I : List Nat, I.length = s ∧ wsum q I % m' = x := by
  intro s
  induction s with
  | zero =>
    intro x _ h
    simp only [TS.As, beq_iff_eq] at h
    exact ⟨[], rfl, by simp [wsum, h]⟩
  | succ s ih =>
    intro x hx h
    obtain ⟨a, ha, hA, hB⟩ := TS.mem_add.mp h
    obtain ⟨I, hl, hw⟩ := ih a ha hA
    simp only [TS.Hq, List.any_eq_true, beq_iff_eq, List.mem_range] at hB
    obtain ⟨i, _, hi⟩ := hB
    refine ⟨i :: I, by simp [hl], ?_⟩
    simp only [wsum, hl]
    rw [Nat.add_mod, hi, hw]
    have h1 := TS.md (x + (m' - a)) m' (by omega)
    generalize (x + (m' - a)) % m' = y at *
    have h2 := TS.md (y + a) m' (by omega)
    generalize (y + a) % m' = z at *
    omega

theorem covers_of_growth (q m' e s : Nat) (hm : 1 < m') (hodd : m' % 2 = 1)
    (hq : Nat.gcd q m' = 1) (he : 2 ^ e % m' = 1 % m') (hmin : ∀ i, 0 < i → i < e → 2 ^ i % m' ≠ 1 % m')
    (he0 : 0 < e) (hs : m' ≤ 1 + s * TS.phi e) : Covers q m' s := by
  have h1 : 1 % m' = 1 := Nat.mod_eq_of_lt hm
  have he' : 2 ^ e % m' = 1 := by rw [he, h1]
  have hmin' : ∀ i, 0 < i → i < e → 2 ^ i % m' ≠ 1 := fun i a b => by rw [← h1]; exact hmin i a b
  intro x hx
  obtain ⟨I, hl, hw⟩ := As_wsum q m' e (by omega) s x hx (TS.covers hm hodd hq he' hmin' he0 s hs x hx)
  exact ⟨I, hl, by rw [hw, Nat.mod_eq_of_lt hx]⟩

theorem exponent_bound_s (q L m α b A m' K Da D' d jj ℓ Λ s D : Nat) (hq3 : 3 ≤ q) (hqL : q ≤ 2 ^ L)
    (hm2 : 2 ≤ m) (hmA : m = 2 ^ α * A * m') (hbA : 2 ^ b ≤ A) (hKD : 2 ^ K ≤ Da)
    (hDM : Da * D' ≤ m') (hD'0 : 0 < D') (hDm : D ≤ m') (hdq : d ≤ q)
    (hjj : jj ≤ α + b + K + s) (hℓ : ℓ + 1 ≤ α + D * s + K + 1 + q * q ^ K)
    (hΛ : Λ ≤ D' * (d * q ^ jj)) :
    Λ + ℓ + 1 ≤ 2 * m ^ (L + 1) * q ^ (s + 1) := by
  have hp0 : 0 < q := by omega
  have hL : 1 ≤ L := by
    apply Classical.byContradiction; intro h
    have : L = 0 := by omega
    subst this; simp at hqL; omega
  have hDaM : Da ≤ m' := Nat.le_trans (Nat.le_mul_of_pos_right _ hD'0) hDM
  have hD'M : D' ≤ m' := Nat.le_trans (Nat.le_mul_of_pos_left _ (Nat.lt_of_lt_of_le Nat.one_le_two_pow hKD)) hDM
  have hA0 : 0 < A := Nat.lt_of_lt_of_le Nat.one_le_two_pow hbA
  have hMpos : 0 < m' := by
    apply Classical.byContradiction; intro h
    have : m' = 0 := by omega
    subst this; simp at hmA; omega
  have hMN : m' ≤ m := by
    rw [hmA]; exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.pow_pos (by omega)) hA0)
  have h2s : 2 ^ (α + b + K) ≤ m := by
    rw [Nat.pow_add, Nat.pow_add, hmA]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hbA) (Nat.le_trans hKD hDaM)
  have hpow : ∀ x, 2 ^ x ≤ m → q ^ x ≤ m ^ L := fun x hx => by
    calc q ^ x ≤ (2 ^ L) ^ x := Nat.pow_le_pow_left hqL _
      _ = (2 ^ x) ^ L := by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
      _ ≤ m ^ L := Nat.pow_le_pow_left hx _
  have hps := hpow _ h2s
  have h2K : 2 ^ K ≤ m := Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) h2s
  have hpK := hpow _ h2K
  have hsN : α + b + K < m := Nat.lt_of_lt_of_le Nat.lt_two_pow_self h2s
  have hΛ' : Λ ≤ m ^ (L + 1) * q ^ (s + 1) := by
    have e1 : D' * (d * q ^ jj) ≤ m' * (q * q ^ jj) :=
      Nat.mul_le_mul hD'M (Nat.mul_le_mul_right _ hdq)
    have e2 : q * q ^ jj ≤ q ^ (α + b + K) * q ^ (s + 1) := by
      rw [← Nat.pow_succ', ← Nat.pow_add]; exact Nat.pow_le_pow_right hp0 (by omega)
    calc Λ ≤ m' * (q ^ (α + b + K) * q ^ (s + 1)) :=
          Nat.le_trans hΛ (Nat.le_trans e1 (Nat.mul_le_mul_left _ e2))
      _ ≤ m * (m ^ L * q ^ (s + 1)) := Nat.mul_le_mul hMN (Nat.mul_le_mul_right _ hps)
      _ = m ^ (L + 1) * q ^ (s + 1) := by rw [Nat.pow_succ]; grind
  have hsq : s + 1 ≤ q ^ s := by
    have h1 := Nat.lt_two_pow_self (n := s)
    have h2 : 2 ^ s ≤ q ^ s := Nat.pow_le_pow_left (by omega) s
    omega
  have hqs0 : 1 ≤ q ^ s := Nat.one_le_pow _ _ hp0
  have hDs : D * s + 1 ≤ m * q ^ s := by
    have h1 : D * s ≤ m * s := Nat.mul_le_mul_right _ (Nat.le_trans hDm hMN)
    have h2 : m * (s + 1) ≤ m * q ^ s := Nat.mul_le_mul_left _ hsq
    rw [Nat.mul_succ] at h2; omega
  have hmL : m ≤ m ^ L := by
    calc m = m ^ 1 := (Nat.pow_one m).symm
      _ ≤ m ^ L := Nat.pow_le_pow_right (by omega) hL
  have hqK : q * q ^ K ≤ q * m ^ L := Nat.mul_le_mul_left _ hpK
  have hY1 : q * m ^ L ≤ m ^ L * q * q ^ s := by
    have := Nat.mul_le_mul_left (m ^ L * q) hqs0; grind
  have hY2 : 2 * (m * q ^ s) ≤ m ^ L * q * q ^ s := by
    have := Nat.mul_le_mul (Nat.mul_le_mul hmL (show 2 ≤ q by omega)) (Nat.le_refl (q ^ s)); grind
  have hR : 2 * (m ^ L * q * q ^ s) ≤ m ^ (L + 1) * q ^ (s + 1) := by
    have e : m ^ (L + 1) * q ^ (s + 1) = m * (m ^ L * q * q ^ s) := by
      rw [Nat.pow_succ, Nat.pow_succ]; grind
    rw [e]; exact Nat.mul_le_mul_right _ hm2
  have hmq : m ≤ m * q ^ s := Nat.le_mul_of_pos_right _ hqs0
  have hfin : 2 * m ^ (L + 1) * q ^ (s + 1) = m ^ (L + 1) * q ^ (s + 1) + m ^ (L + 1) * q ^ (s + 1) := by grind
  rw [hfin]
  generalize m ^ (L + 1) * q ^ (s + 1) = R at hΛ' hR ⊢
  generalize m ^ L * q * q ^ s = Y at hY1 hY2 hR
  generalize m * q ^ s = X at hDs hY2 hmq
  generalize q * q ^ K = W at hℓ hqK
  generalize q * m ^ L = V at hqK hY1
  generalize D * s = Z at hℓ hDs
  omega

theorem wsum_reduce (q D m' : Nat) (hD : 2 ^ D % m' = 1 % m') :
    ∀ I : List Nat, wsum q (I.map (· % D)) % m' = wsum q I % m' := by
  intro I
  induction I with
  | nil => rfl
  | cons i I ih =>
    simp only [List.map_cons, wsum, List.length_map]
    have h2 : 2 ^ (i % D) % m' = 2 ^ i % m' := pow_two_mod_period m' D hD _ _ (Nat.mod_mod _ _)
    rw [Nat.add_mod, Nat.mul_mod, h2, ← Nat.mul_mod, ih, ← Nat.add_mod]

theorem covers_fin (q m' s D : Nat) [NeZero m'] (hD0 : 0 < D) (hD : 2 ^ D % m' = 1 % m')
    (hcov : Covers q m' s) :
    ∀ c : Fin m', ∃ is : List Nat, is.length = s ∧ (∀ i ∈ is, i < D) ∧ residue m' (wsum q is) = c := by
  intro c
  obtain ⟨I, hl, hw⟩ := hcov c.val c.isLt
  refine ⟨I.map (· % D), by rw [List.length_map, hl], ?_, ?_⟩
  · intro i hi; obtain ⟨j, _, rfl⟩ := List.mem_map.1 hi; exact Nat.mod_lt _ hD0
  · rw [← residue_self_val c, residue_eq_iff, wsum_reduce q D m' hD, hw]

theorem word_exists_s (q K s : Nat) [NonWieferich q] (m' D x w d u' : Nat) [NeZero m']
    (hM : Nat.Coprime m' (2 * q)) (hw : ∃ i, w % q = 2 ^ i % q) (hD : 2 ^ D % m' = 1 % m')
    (hcov : Covers q m' s) (hD0 : 0 < D) (hd0 : 0 < d) (hd : 2 ^ d = 1 + q * u') (hu : Nat.Coprime q u') :
    ∃ (u₀ : List Nat) (nz : Nat), (∀ e ∈ u₀, e ≤ 1) ∧ oneCount u₀ = s + K + 1 ∧
      u₀.length = D * s + K + 1 ∧ nz < d * q ^ K ∧
      (q ^ oneCount (u₀ ++ List.replicate nz 0) * x + offset q (u₀ ++ List.replicate nz 0))
          % (q ^ (K + 1) * m')
        = (2 ^ (u₀ ++ List.replicate nz 0).length * w) % (q ^ (K + 1) * m') := by
  have hodd : q % 2 = 1 := NonWieferich.odd
  have hp3 : 3 ≤ q := NonWieferich.three_le
  haveI : Invertible2p q m' := invertible2p_of_coprime hM
  obtain ⟨nz, hmT, hmP⟩ := padic_word q K d u' w hp3 hodd hd0 hd hu hw
  obtain ⟨t, ht⟩ := ones_surj (m' := m') q hM (K + 1) (residue m' (2 ^ nz) * residue m' w)
  obtain ⟨ω, hω, hon, hl, hwω⟩ := sparse_word q D s hD (covers_fin q m' s D hD0 hD hcov) (residue m' x) t
  have hwM : backWord q (ω ++ List.replicate (K + 1) 1 ++ List.replicate nz 0) (residue m' x) = residue m' w := by
    rw [List.append_assoc, backWord_append, backWord_append, hwω, ht, backWord_zeros]
  refine ⟨ω ++ List.replicate (K + 1) 1, nz, ?_, ?_, ?_, hmT, ?_⟩
  · intro e he
    rcases List.mem_append.1 he with h | h
    · exact hω e h
    · rw [List.eq_of_mem_replicate h]; exact Nat.le_refl 1
  · rw [oneCount_append, oneCount_replicate_one, hon]; omega
  · simp only [List.length_append, List.length_replicate]; omega
  ·
    have hM' : (q ^ oneCount (ω ++ List.replicate (K + 1) 1 ++ List.replicate nz 0) * x
        + offset q (ω ++ List.replicate (K + 1) 1 ++ List.replicate nz 0)) % m'
        = (2 ^ (ω ++ List.replicate (K + 1) 1 ++ List.replicate nz 0).length * w) % m' := by
      apply (residue_eq_iff _ _ _).1
      have h := (backWord_iff q _ (residue m' x) (residue m' w)).2 hwM
      simp only [residue_add, residue_mul]
      exact h

    have hcu : oneCount (ω ++ List.replicate (K + 1) 1 ++ List.replicate nz 0)
        = oneCount ω + (K + 1) := by
      rw [oneCount_append, oneCount_append, oneCount_replicate_one, oneCount_replicate_zero,
        Nat.add_zero]
    have hou : offset q (ω ++ List.replicate (K + 1) 1 ++ List.replicate nz 0)
        = q ^ (K + 1) * offset q ω + 2 ^ ω.length * offset q (List.replicate (K + 1) 1) := by
      rw [offset_append, offset_replicate_zero, oneCount_replicate_zero, Nat.pow_zero, Nat.one_mul,
        Nat.mul_zero, Nat.add_zero, offset_append, oneCount_replicate_one]
    have hlen : (ω ++ List.replicate (K + 1) 1 ++ List.replicate nz 0).length
        = ω.length + (K + 1) + nz := by
      simp only [List.length_append, List.length_replicate]
    haveI : NeZero (q ^ (K + 1)) := ⟨Nat.pos_iff_ne_zero.1 (Nat.pow_pos (by omega))⟩
    have hP' : (q ^ oneCount (ω ++ List.replicate (K + 1) 1 ++ List.replicate nz 0) * x
        + offset q (ω ++ List.replicate (K + 1) 1 ++ List.replicate nz 0)) % q ^ (K + 1)
        = (2 ^ (ω ++ List.replicate (K + 1) 1 ++ List.replicate nz 0).length * w) % q ^ (K + 1) := by
      rw [hcu, hou, hlen]
      apply (residue_eq_iff _ _ _).1
      have hA1 : residue (q ^ (K + 1)) (q ^ (oneCount ω + (K + 1))) = 0 := by
        rw [residue_p_pow_add, residue_self]; grind
      have hpow : 2 ^ (ω.length + (K + 1) + nz) * w
          = 2 ^ ω.length * (2 ^ (K + 1 + nz) * w) := by
        rw [← Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
      have hO' : residue (q ^ (K + 1)) (2 ^ (K + 1 + nz) * w)
          = residue (q ^ (K + 1)) (offset q (List.replicate (K + 1) 1)) :=
        (residue_eq_iff _ _ _).2 hmP
      rw [hpow, residue_mul, hO']
      simp only [residue_add, residue_mul, hA1, residue_self]
      grind
    have hcop : Nat.Coprime (q ^ (K + 1)) m' :=
      Nat.Coprime.pow_left (K + 1) (coprime_p_of_coprime_two_mul hM).symm
    exact mod_combine hcop hP' hM'

theorem predecessor_bound_core (q : Nat) [NonWieferich q] (L : Nat) (hpL : q ≤ 2 ^ L)
    (m : Nat) (hN : 2 ≤ m) (α A m' k s : Nat) (hNe : m = 2 ^ α * A * m') (hAb : A ∣ q ^ k)
    (hbA : 2 ^ k ≤ A) (hM : Nat.Coprime m' (2 * q)) (hcov : Covers q m' s)
    (w : Nat) (hw0 : 1 ≤ w) (hw : ∃ i, w % q = 2 ^ i % q) (r B : Nat) :
    ∃ n : Nat, B < n ∧ Reaches q n w ∧ n % m = r % m ∧
      n ≤ (B + 1) * w * 2 ^ (2 * m ^ (L + 1) * q ^ (s + 1)) := by
  have hp3 := NonWieferich.three_le (q := q)
  have hM2 : m' % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one m' with h | h
    · have := Nat.Coprime.gcd_eq_one hM; have h2 : 2 ∣ m' := Nat.dvd_of_mod_eq_zero h
      have : Nat.gcd m' (2 * q) ≠ 1 := by
        intro h1; have : 2 ∣ Nat.gcd m' (2 * q) := Nat.dvd_gcd h2 (Nat.dvd_mul_right 2 q)
        rw [h1] at this; omega
      exact absurd hM (by unfold Nat.Coprime; exact this)
    · exact h
  have hA2 : A % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one A with h | h
    · exfalso; have h3 : 2 ∣ q ^ k := Nat.dvd_trans (Nat.dvd_of_mod_eq_zero h) hAb
      have hq1 : q % 2 = 1 := NonWieferich.odd (q := q)
      have : q ^ k % 2 = 1 := by rw [Nat.pow_mod, hq1]; simp
      omega
    · exact h
  have hMpos : 0 < m' := by
    apply Classical.byContradiction; intro h0; have : m' = 0 := by omega
    subst this; simp at hNe; omega
  have hMpos : 0 < m' := by omega
  haveI : NeZero m' := ⟨by omega⟩
  obtain ⟨D, hD0, hDM, hDper⟩ := exists_pow2_period m' hMpos (coprime_two_of_coprime_two_mul hM)
  obtain ⟨Da, D', K, hDe, hD'a, hDaK, hKD⟩ := split_coprime q D hD0
  obtain ⟨d, u, hd0, hdp, hd, hu⟩ := NonWieferich.gen (q := q)
  have hD'cop : Nat.Coprime q D' := hD'a.symm
  have hpK : 0 < q ^ K := powp_pos q K
  have hD'0 : 0 < D' := by
    apply Classical.byContradiction; intro h
    have : D' = 0 := by omega
    rw [this] at hDe; simp at hDe; omega
  have hDper' : 2 ^ (q ^ K * D') % m' = 1 % m' := by
    obtain ⟨c, hc⟩ := hDaK
    have : q ^ K * D' = D * c := by rw [hc, hDe]; grind
    rw [this, Nat.pow_mul, Nat.pow_mod, hDper, ← Nat.pow_mod, Nat.one_pow]
  have hDM' : Da * D' ≤ m' := by rw [← hDe]; exact hDM

  obtain ⟨π, hπ, hπl, hπd⟩ := parity_prefix q α r
  have h2α0 : 0 < 2 ^ α := Nat.pow_pos (by omega)
  obtain ⟨z, hz⟩ := hπd

  obtain ⟨u₀, nz, hlet, hou0, hlen0, hm, hcong⟩ :=
    word_exists_s q K s m' D z w d u hM hw hDper hcov hD0 hd0 hd hu
  have hU : ∀ e ∈ u₀ ++ List.replicate nz 0, e ≤ 1 := by
    intro e he
    rcases List.mem_append.1 he with h | h
    · exact hlet e h
    · rw [List.eq_of_mem_replicate h]; omega
  have hW : ∀ e ∈ π ++ (u₀ ++ List.replicate nz 0), e ≤ 1 := by
    intro e he
    rcases List.mem_append.1 he with h | h
    · exact hπ e h
    · exact hU e h
  have hoU : oneCount (u₀ ++ List.replicate nz 0) = oneCount u₀ := by
    rw [oneCount_append, oneCount_replicate_zero, Nat.add_zero]
  have hlU : (u₀ ++ List.replicate nz 0).length = u₀.length + nz := by
    simp only [List.length_append, List.length_replicate]
  have hoW : oneCount (π ++ (u₀ ++ List.replicate nz 0)) = oneCount π + oneCount u₀ := by
    rw [oneCount_append, hoU]
  have hlW : (π ++ (u₀ ++ List.replicate nz 0)).length = α + (u₀.length + nz) := by
    rw [List.length_append, hlU, hπl]
  have hCW : offset q (π ++ (u₀ ++ List.replicate nz 0))
      = q ^ oneCount u₀ * offset q π + 2 ^ α * offset q (u₀ ++ List.replicate nz 0) := by
    rw [offset_append, hoU, hπl]
  have hCle := offset_le_pow q (by omega) _ hW
  have hreach := integrality_reaches q _ hW
  have hfol := follow_prefix q π (u₀ ++ List.replicate nz 0)
  rw [hoU, hlU] at hcong
  rw [hoW, hlW] at hCle hreach hfol
  rw [hπl] at hfol
  have hoπ := oneCount_le π hπ
  have hou := hou0
  rw [hπl] at hoπ
  rw [hCW] at hCle hreach hfol

  have hY : (q ^ (oneCount π + oneCount u₀) * r
        + (q ^ oneCount u₀ * offset q π + 2 ^ α * offset q (u₀ ++ List.replicate nz 0)))
      % (q ^ (K + 1) * m') = (2 ^ (α + (u₀.length + nz)) * w) % (q ^ (K + 1) * m') := by
    have e1 : q ^ (oneCount π + oneCount u₀) * r
        + (q ^ oneCount u₀ * offset q π + 2 ^ α * offset q (u₀ ++ List.replicate nz 0))
        = 2 ^ α * (q ^ oneCount u₀ * z + offset q (u₀ ++ List.replicate nz 0)) := by
      rw [Nat.pow_add]
      have : q ^ oneCount π * r + offset q π = 2 ^ α * z := hz
      grind
    rw [e1]
    generalize q ^ (K + 1) * m' = Q at hcong ⊢
    rw [Nat.pow_add, Nat.mul_assoc, Nat.mul_mod, hcong, ← Nat.mul_mod]
  generalize oneCount π = oπ at *
  generalize oneCount u₀ = o' at *
  generalize offset q π = Cπ at *
  generalize offset q (u₀ ++ List.replicate nz 0) = C' at *
  generalize hℓdef : α + (u₀.length + nz) = ℓ at *

  obtain ⟨j, hj⟩ : ∃ j, (oπ + o') + k = j + 1 := ⟨oπ + o' + k - 1, by omega⟩
  have hKj : K ≤ j := by omega
  obtain ⟨E0, hE0⟩ := exponent_lemma q hd0 hd hu m' K j w D' ℓ _ hM hw hD'0 hD'cop hDper' hKj hY
  have hLm0 : 0 < Nat.lcm (q ^ K * D') (d * q ^ j) :=
    Nat.lcm_pos (Nat.mul_pos hpK hD'0) (Nat.mul_pos hd0 (powp_pos q j))
  have hLmle : Nat.lcm (q ^ K * D') (d * q ^ j) ≤ D' * (d * q ^ j) := by
    apply Nat.le_of_dvd (Nat.mul_pos hD'0 (Nat.mul_pos hd0 (powp_pos q j)))
    apply Nat.lcm_dvd
    · have h := Nat.mul_dvd_mul (Nat.pow_dvd_pow q hKj) (Nat.dvd_mul_right D' d)
      have e : q ^ j * (D' * d) = D' * (d * q ^ j) := by grind
      rwa [e] at h
    · exact Nat.dvd_mul_left _ _
  generalize Nat.lcm (q ^ K * D') (d * q ^ j) = Lm at hE0 hLm0 hLmle
  generalize hCdef : q ^ o' * Cπ + 2 ^ α * C' = C at *
  generalize hodef : oπ + o' = o at *
  have hpo : 0 < q ^ o := powp_pos q o
  have hV : 2 ^ ℓ ≤ q ^ o * (B + 1 + 2 ^ ℓ) := by
    have : 1 * 2 ^ ℓ ≤ q ^ o * (B + 1 + 2 ^ ℓ) := Nat.mul_le_mul hpo (Nat.le_add_left _ _)
    omega
  obtain ⟨e, hVe, he2⟩ := exists_pow_two_between _ ℓ hV
  obtain ⟨E, heE, hEe, hEmod⟩ := exists_in_class E0 e Lm hLm0
  have hZ := hE0 E hEmod
  have hpow : q ^ (j + 1) * m' = q ^ o * (q ^ k * m') := by
    rw [← hj, Nat.pow_add, Nat.mul_assoc]
  rw [hpow] at hZ
  have hCZ : C ≤ 2 ^ (ℓ + E) * w := by
    have h1 : 2 ^ (ℓ + e) ≤ 2 ^ (ℓ + E) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 2 ^ (ℓ + E) ≤ 2 ^ (ℓ + E) * w := Nat.le_mul_of_pos_right _ hw0
    have h3 : q ^ o * 2 ^ ℓ ≤ q ^ o * (B + 1 + 2 ^ ℓ) := Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨n, hZn, hnmod⟩ := witness_exists q o C r (2 ^ (ℓ + E) * w) (q ^ k * m') hpo hCZ hZ
  refine ⟨n, ?_, ?_, ?_, ?_⟩
  · exact (witness_size (q ^ o) C ℓ E e Lm w n B hpo hw0 hCle hZn.symm hVe he2 heE (by omega)).1
  ·
    have hdvd : 2 ^ ℓ ∣ q ^ o * n + C := ⟨2 ^ E * w, by rw [← hZn, Nat.pow_add]; grind⟩
    have hq : (q ^ o * n + C) / 2 ^ ℓ = 2 ^ E * w := by
      rw [← hZn, Nat.pow_add, Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.pow_pos (by omega)
