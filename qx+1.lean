macro "nat_ring" : tactic => `(tactic| first
  | omega
  | (simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega)
  | (simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at * <;> omega))

macro "int_ring" : tactic => `(tactic| first
  | omega
  | (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_add, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Int.add_assoc, Int.add_comm, Int.add_left_comm, Int.neg_mul, Int.mul_neg, Int.sub_eq_add_neg] <;> omega)
  | (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_add, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Int.add_assoc, Int.add_comm, Int.add_left_comm, Int.neg_mul, Int.mul_neg, Int.sub_eq_add_neg] at * <;> omega))

namespace Collatz

theorem nat_beq_iff {x y : Nat} : (x == y) = true ↔ x = y :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl x⟩

theorem my_nodup_range : ∀ n, (List.range n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
    rw [List.range_succ, List.nodup_append]
    refine ⟨my_nodup_range n, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    subst hb; subst hab
    exact Nat.lt_irrefl _ (List.mem_range.mp ha)

theorem my_mem_erase {α : Type} [DecidableEq α] : ∀ (l : List α) (a x : α), x ≠ a → (x ∈ l.erase a ↔ x ∈ l)
  | [], _, _, _ => Iff.rfl
  | b :: l, a, x, hx => by
    rw [List.erase_cons]
    split
    · rename_i h
      have hba : b = a := eq_of_beq h
      subst hba
      exact ⟨fun h' => List.mem_cons_of_mem _ h', fun h' => by
        rcases List.mem_cons.1 h' with h1 | h1
        · exact absurd h1 hx
        · exact h1⟩
    · constructor
      · intro h'
        rcases List.mem_cons.1 h' with h1 | h1
        · exact List.mem_cons.2 (Or.inl h1)
        · exact List.mem_cons.2 (Or.inr ((my_mem_erase l a x hx).1 h1))
      · intro h'
        rcases List.mem_cons.1 h' with h1 | h1
        · exact List.mem_cons.2 (Or.inl h1)
        · exact List.mem_cons.2 (Or.inr ((my_mem_erase l a x hx).2 h1))

theorem my_length_erase {α : Type} [DecidableEq α] : ∀ (l : List α) (a : α), a ∈ l → (l.erase a).length + 1 = l.length
  | [], _, h => absurd h List.not_mem_nil
  | b :: l, a, h => by
    rw [List.erase_cons]
    split
    · rename_i hb
      have hba : b = a := eq_of_beq hb
      subst hba
      rfl
    · rename_i hb
      have hab : a ≠ b := fun e => hb (beq_iff_eq.2 e.symm)
      have hal : a ∈ l := by
        rcases List.mem_cons.1 h with h1 | h1
        · exact absurd h1 hab
        · exact h1
      rw [List.length_cons, List.length_cons]
      exact congrArg Nat.succ (my_length_erase l a hal)

theorem my_len_le {α : Type} [DecidableEq α] : ∀ (l1 l2 : List α), l1.Nodup → (∀ x ∈ l1, x ∈ l2) → l1.length ≤ l2.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l2, hnd, hs => by
    obtain ⟨hat, htnd⟩ := List.nodup_cons.1 hnd
    have ha : a ∈ l2 := hs a (List.mem_cons.2 (Or.inl rfl))
    have hsub : ∀ x ∈ t, x ∈ l2.erase a := fun x hx =>
      (my_mem_erase l2 a x (fun h => hat (by rw [← h]; exact hx))).2 (hs x (List.mem_cons.2 (Or.inr hx)))
    have key := my_len_le t (l2.erase a) htnd hsub
    rw [List.length_cons, ← my_length_erase l2 a ha]
    exact Nat.add_le_add_right key 1

theorem my_countP_eq_zero {α : Type} : ∀ (l : List α) (p : α → Bool), l.countP p = 0 ↔ ∀ x ∈ l, p x = false
  | [], _ => ⟨fun _ _ h => absurd h List.not_mem_nil, fun _ => rfl⟩
  | a :: l, p => by
    cases hp : p a
    · rw [List.countP_cons_of_neg (by rw [hp]; exact Bool.false_ne_true)]
      constructor
      · intro h x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hp
        · exact (my_countP_eq_zero l p).1 h x hx
      · intro h
        exact (my_countP_eq_zero l p).2 (fun x hx => h x (List.mem_cons.2 (Or.inr hx)))
    · rw [List.countP_cons_of_pos (by rw [hp])]
      constructor
      · intro h
        exact absurd h (Nat.succ_ne_zero _)
      · intro h
        exact absurd (h a (List.mem_cons.2 (Or.inl rfl))) (by rw [hp]; exact Bool.noConfusion)

theorem my_len_le' {α : Type} [DecidableEq α] {l1 l2 : List α} (h1 : l1.Nodup) (hs : l1 ⊆ l2) : l1.length ≤ l2.length :=
  my_len_le l1 l2 h1 (fun _x hx => hs hx)

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
    | succ n => simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm]; omega

theorem binom_cubic (a : Nat) : ∀ n, ∃ z, (1 + a) ^ n = 1 + n * a + triangle n * a ^ 2 + a ^ 3 * z
  | 0 => ⟨0, by simp [triangle]⟩
  | n + 1 => by
    obtain ⟨z, hz⟩ := binom_cubic a n
    refine ⟨triangle n + z + z * a, ?_⟩
    rw [Nat.pow_succ, hz]
    show (1 + n * a + triangle n * a ^ 2 + a ^ 3 * z) * (1 + a) = 1 + (n + 1) * a + triangle (n + 1) * a ^ 2 + a ^ 3 * (triangle n + z + z * a)
    simp [Nat.mul_add, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, triangle]
    omega

theorem binom_quadratic (a : Nat) : ∀ n, ∃ z, (1 + a) ^ n = 1 + n * a + a ^ 2 * z := by
  intro n; obtain ⟨z, hz⟩ := binom_cubic a n
  exact ⟨triangle n + a * z, by
    rw [hz]
    have h : a ^ 3 * z = a ^ 2 * (a * z) := by
      rw [Nat.pow_succ]
      rw [← Nat.mul_assoc]
    calc 1 + n * a + triangle n * a ^ 2 + a ^ 3 * z
        = 1 + n * a + triangle n * a ^ 2 + a ^ 2 * (a * z) := by rw [h]
      _ = 1 + n * a + a ^ 2 * triangle n + a ^ 2 * (a * z) := by rw [Nat.mul_comm (triangle n) (a ^ 2)]
      _ = 1 + n * a + (a ^ 2 * triangle n + a ^ 2 * (a * z)) := by rw [← Nat.add_assoc]
      _ = 1 + n * a + a ^ 2 * (triangle n + a * z) := by rw [← Nat.mul_add]
  ⟩

theorem lift_step {q j u : Nat} (hp : q % 2 = 1) (hj : 1 ≤ j) (hu : Nat.Coprime q u) :
    ∃ w, Nat.Coprime q w ∧ (1 + q ^ j * u) ^ q = 1 + q ^ (j + 1) * w := by
  obtain ⟨z, hz⟩ := binom_cubic (q ^ j * u) q
  obtain ⟨h, hh⟩ : ∃ h, triangle q = q * h := by
    refine ⟨(q - 1) / 2, ?_⟩
    have htwo := triangle_two q
    have hmod : (q - 1) % 2 = 0 := by omega
    have e : q - 1 = 2 * ((q - 1) / 2) := by omega
    rw [e] at htwo
    rw [← Nat.mul_assoc] at htwo
    rw [Nat.mul_comm q 2] at htwo
    rw [Nat.mul_assoc] at htwo
    exact Nat.mul_left_cancel (by omega : 0 < 2) htwo
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  let w := u + q * (h * q ^ k * u ^ 2 + q ^ (2 * k) * u ^ 3 * z)
  refine ⟨w, ?_, ?_⟩
  · show Nat.Coprime q (u + q * _)
    rw [Nat.Coprime, Nat.gcd_add_mul_left_right]; exact hu
  · rw [hz, hh]
    show _ = 1 + q ^ (k + 1 + 1) * (u + q * (h * q ^ k * u ^ 2 + q ^ (2 * k) * u ^ 3 * z))
    have e1 : q ^ (k + 1 + 1) = q * q * q ^ k := by
      rw [Nat.pow_succ]
      rw [Nat.pow_succ]
      rw [Nat.mul_assoc]
      rw [Nat.mul_comm (q ^ k)]
    have e2 : q ^ (k + 1) = q * q ^ k := by
      rw [Nat.pow_succ]
      rw [Nat.mul_comm]
    have e3 : q ^ (2 * k) = q ^ k * q ^ k := by rw [Nat.two_mul, Nat.pow_add]
    rw [e1, e2, e3]; generalize q ^ k = A; simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.pow_succ, Nat.pow_zero, Nat.mul_one]; omega

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

theorem pow_mod_one (n a k : Nat) (h : a % n = 1 % n) : a ^ k % n = 1 % n := by
  rw [Nat.pow_mod, h, ← Nat.pow_mod, Nat.one_pow]

def natMemDec (a : Nat) : (L : List Nat) → Decidable (a ∈ L)
  | [] => isFalse (List.not_mem_nil)
  | b :: L =>
    match Nat.decEq a b with
    | isTrue h => isTrue (h ▸ List.mem_cons_self)
    | isFalse h =>
      match natMemDec a L with
      | isTrue hL => isTrue (List.mem_cons_of_mem b hL)
      | isFalse hL => isFalse (fun hm => by
          rcases List.mem_cons.1 hm with h' | h'
          · exact h h'
          · exact hL h')

instance (priority := high) natMemDecInst (a : Nat) (L : List Nat) : Decidable (a ∈ L) := natMemDec a L
theorem lift_exponent {q j u : Nat} (hp : q % 2 = 1) (hj : 1 ≤ j) (hu : Nat.Coprime q u) :
    ∀ n, ∃ w, Nat.Coprime q w ∧ (1 + q ^ j * u) ^ (q ^ n) = 1 + q ^ (j + n) * w
  | 0 => ⟨u, hu, by simp⟩
  | n + 1 => by
    obtain ⟨w, hw, hx⟩ := lift_exponent hp hj hu n
    obtain ⟨w', hw', hx'⟩ := lift_step (j := j + n) hp (by omega) hw
    exact ⟨w', hw', by rw [Nat.pow_succ, Nat.pow_mul, hx]; exact hx'⟩

theorem order_iff {q u j : Nat} (hp : q % 2 = 1) (hq3 : 3 ≤ q) (hj : 1 ≤ j)
    (hu : Nat.Coprime q u) :
    ∀ M m, (1 + q ^ j * u) ^ m % q ^ (j + M) = 1 ↔ q ^ M ∣ m := by
  have hP : ∀ M, 1 < q ^ (j + M) := fun M =>
    Nat.lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) q)
  intro M
  induction M with
  | zero =>
    intro m
    obtain ⟨z, hz⟩ := binom_quadratic (q ^ j * u) m
    simp only [Nat.add_zero, Nat.pow_zero, Nat.one_dvd, iff_true]
    rw [hz, show 1 + m * (q ^ j * u) + (q ^ j * u) ^ 2 * z
        = 1 + q ^ j * (m * u + q ^ j * (u ^ 2 * z)) by
          simp only [Nat.mul_add, Nat.pow_two]; ac_rfl,
      Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (hP 0)
  | succ M ih =>
    intro m
    constructor
    · intro h
      have hA : (1 + q ^ j * u) ^ m % q ^ (j + M) = 1 := by
        rw [← Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow q (by omega : j + M ≤ j + (M + 1))), h]
        exact Nat.mod_eq_of_lt (hP M)
      obtain ⟨k, rfl⟩ := (ih m).1 hA
      obtain ⟨w, hw, hx⟩ := lift_exponent hp hj hu M
      obtain ⟨z, hz⟩ := binom_quadratic (q ^ (j + M) * w) k
      rw [Nat.pow_mul, hx, hz] at h
      have hc : 1 ≤ j + M := by omega
      have eX : k * (q ^ (j + M) * w) + (q ^ (j + M) * w) ^ 2 * z
          = q ^ (j + M) * (k * w + q ^ (j + M) * (w ^ 2 * z)) := by
        simp only [Nat.mul_add, Nat.pow_two]; ac_rfl
      have hX : q ^ (j + M + 1) ∣ k * (q ^ (j + M) * w) + (q ^ (j + M) * w) ^ 2 * z := by
        have h2 := Nat.sub_mod_eq_zero_of_mod_eq (h.trans (Nat.mod_eq_of_lt (hP (M + 1))).symm)
        have e1 : 1 + k * (q ^ (j + M) * w) + (q ^ (j + M) * w) ^ 2 * z - 1
            = k * (q ^ (j + M) * w) + (q ^ (j + M) * w) ^ 2 * z := by omega
        rw [e1] at h2
        exact Nat.dvd_of_mod_eq_zero h2
      rw [eX, show q ^ (j + M + 1) = q ^ (j + M) * q by rw [Nat.pow_succ]] at hX
      have hY := Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos (by omega)) hX
      have hqc : q ∣ q ^ (j + M) := by
        have := Nat.pow_dvd_pow q hc
        rwa [Nat.pow_one] at this
      have hd3 : q ∣ q ^ (j + M) * (w ^ 2 * z) := Nat.dvd_trans hqc (Nat.dvd_mul_right _ _)
      have hkw : q ∣ k * w := (Nat.dvd_add_left hd3).1 hY
      obtain ⟨k', rfl⟩ := Nat.Coprime.dvd_of_dvd_mul_right hw hkw
      exact ⟨k', by rw [Nat.pow_succ]; ac_rfl⟩
    · rintro ⟨k, rfl⟩
      obtain ⟨w, hw, hx⟩ := lift_exponent hp hj hu (M + 1)
      rw [Nat.pow_mul, hx, Nat.pow_mod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hP (M + 1)),
        Nat.one_pow, Nat.mod_eq_of_lt (hP (M + 1))]

theorem unit_power_cover {q u j : Nat} (hp : q % 2 = 1) (hq3 : 3 ≤ q) (hj : 1 ≤ j)
    (hu : Nat.Coprime q u) (M x : Nat) (hx : x % q ^ j = 1) :
    ∃ t, t < q ^ M ∧ (1 + q ^ j * u) ^ t % q ^ (j + M) = x % q ^ (j + M) := by
  have hP : ∀ M, 1 < q ^ (j + M) := fun M =>
    Nat.lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) q)
  have hPj : 1 < q ^ j := by
    have := hP 0; rwa [Nat.add_zero] at this
  have hQ : 0 < q ^ (j + M) := Nat.lt_trans Nat.zero_lt_one (hP M)
  have hpM : 0 < q ^ M := Nat.pow_pos (by omega)
  have hpj : 0 < q ^ j := Nat.lt_trans Nat.zero_lt_one hPj
  have hQe : q ^ (j + M) = q ^ j * q ^ M := Nat.pow_add q j M
  have hcq : (1 + q ^ j * u) % q = 1 := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [Nat.pow_succ, Nat.mul_comm (q ^ i) q, Nat.mul_assoc, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hcop : Nat.Coprime q (1 + q ^ j * u) := coprime_of_mod_one hcq
  have hcopQ : Nat.Coprime (q ^ (j + M)) (1 + q ^ j * u) := Nat.Coprime.pow_left _ hcop
  have hc1 : (1 + q ^ j * u) % q ^ j = 1 := by
    rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hPj
  let U : List Nat := (List.range (q ^ (j + M))).filter (fun y => decide (y % q ^ j = 1))
  let L1 : List Nat := (List.range (q ^ M)).map (fun t => (1 + q ^ j * u) ^ t % q ^ (j + M))
  have hUnodup : U.Nodup := List.Pairwise.filter _ (my_nodup_range _)
  have key : ∀ a b, a ≤ b → b < q ^ M →
      (1 + q ^ j * u) ^ a % q ^ (j + M) = (1 + q ^ j * u) ^ b % q ^ (j + M) → a = b := by
    intro a b hab hb h
    have hb' : (1 + q ^ j * u) ^ b = (1 + q ^ j * u) ^ a * (1 + q ^ j * u) ^ (b - a) := by
      rw [← Nat.pow_add]; congr 1; omega
    have h' : ((1 + q ^ j * u) ^ a * (1 + q ^ j * u) ^ (b - a)) % q ^ (j + M)
        = ((1 + q ^ j * u) ^ a * 1) % q ^ (j + M) := by
      rw [← hb', Nat.mul_one]; exact h.symm
    have h'' := mod_cancel_mul_left (Nat.Coprime.pow_right a hcopQ)
      (Nat.one_le_pow _ _ (by omega)) h'
    have hd := (order_iff hp hq3 hj hu M (b - a)).1 (h''.trans (Nat.mod_eq_of_lt (hP M)))
    have : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  have hL1nodup : L1.Nodup := by
    apply List.pairwise_map.2
    apply List.Pairwise.imp_of_mem _ (my_nodup_range _)
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
    refine ⟨Nat.mod_lt _ hQ, ?_⟩
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow q (by omega : j ≤ j + M)),
      pow_mod_one (q ^ j) (1 + q ^ j * u) _ (by rw [hc1]; exact (Nat.mod_eq_of_lt (show 1 < q ^ j by omega)).symm)]
    simp [Nat.mod_eq_of_lt (show 1 < q ^ j by omega)]
  have hxU : x % q ^ (j + M) ∈ U := by
    rw [List.mem_filter, List.mem_range]
    refine ⟨Nat.mod_lt _ hQ, ?_⟩
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow q (by omega : j ≤ j + M)), hx]
    simp
  have hUsub : U ⊆ (List.range (q ^ M)).map (fun z => 1 + q ^ j * z) := by
    intro y hy
    rw [List.mem_filter, List.mem_range] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have hy2' : y % q ^ j = 1 := by simpa using hy2
    rw [List.mem_map]
    refine ⟨y / q ^ j, List.mem_range.2 ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hpj, Nat.mul_comm, ← hQe]
      exact hy1
    · have := Nat.div_add_mod y (q ^ j)
      rw [hy2'] at this
      show 1 + q ^ j * (y / q ^ j) = y
      rw [Nat.add_comm]; exact this
  have hlen2 : U.length ≤ q ^ M := by
    have := my_len_le' hUnodup hUsub; simpa using this
  have hL1len : L1.length = q ^ M := by simp [L1]
  have hmem : x % q ^ (j + M) ∈ L1 := by
    match (inferInstance : Decidable (x % q ^ (j + M) ∈ L1)) with
    | isTrue hin => exact hin
    | isFalse hxL =>
    have hsub : (x % q ^ (j + M) :: L1) ⊆ U := by
      intro y hy
      rcases List.mem_cons.1 hy with h | h
      · rw [h]; exact hxU
      · exact hL1U h
    have hlen1 := my_len_le' (List.nodup_cons.2 ⟨hxL, hL1nodup⟩) hsub
    simp only [List.length_cons] at hlen1
    omega
  rw [List.mem_map] at hmem
  obtain ⟨t, ht, he⟩ := hmem
  exact ⟨t, List.mem_range.1 ht, he⟩


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

theorem exists_least (P : Nat → Prop) [DecidablePred P] :
    (∃ n, P n) → ∃ n, P n ∧ ∀ r, r < n → ¬ P r := by
  have aux : ∀ N, (∀ r, r < N → ¬ P r) ∨ ∃ n, P n ∧ ∀ r, r < n → ¬ P r := by
    intro N
    induction N with
    | zero => exact Or.inl (fun r hr _ => absurd hr (Nat.not_lt_zero r))
    | succ N ih =>
      rcases ih with h | h
      · match (inferInstance : Decidable (P N)) with
        | isTrue hN =>
          exact Or.inr ⟨N, hN, h⟩
        | isFalse hN =>
          refine Or.inl (fun r hr hPr => ?_)
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr) with hlt | heq
          · exact h r hlt hPr
          · exact hN (by rw [← heq]; exact hPr)
      · exact Or.inr h
  rintro ⟨n, hn⟩
  rcases aux (n + 1) with h | h
  · exact absurd hn (h n (Nat.lt_succ_self n))
  · exact h

theorem exists_pow2_period (m' : Nat) (hM : 0 < m') (hc : Nat.Coprime m' 2) :
    ∃ D, 0 < D ∧ D ≤ m' ∧ 2 ^ D % m' = 1 % m' := by
  cases hf : (List.range (m' + 1)).find? (fun D => decide (0 < D ∧ D ≤ m' ∧ 2 ^ D % m' = 1 % m')) with
  | some D =>
    have hD := List.find?_some hf
    simp only [decide_eq_true_eq] at hD
    exact ⟨D, hD⟩
  | none =>
    exfalso
    have hno : ¬ ∃ D, 0 < D ∧ D ≤ m' ∧ 2 ^ D % m' = 1 % m' := by
      rintro ⟨D, hD0, hDm, hDe⟩
      have hn := List.find?_eq_none.1 hf D (List.mem_range.2 (by omega))
      simp only [decide_eq_true_eq] at hn
      exact hn ⟨hD0, hDm, hDe⟩
    have hinj : ∀ a b, a < b → b ≤ m' → 2 ^ a % m' ≠ 2 ^ b % m' := by
      intro a b hab hb heq
      apply hno
      refine ⟨b - a, by omega, by omega, ?_⟩
      have hcop : Nat.Coprime m' (2 ^ a) := Nat.Coprime.pow_right _ hc
      exact mod_cancel_mul_right (x := 2 ^ (b - a)) (y := 1) hcop
        (by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega), Nat.one_mul]; exact heq.symm)
    have hnd : ((List.range (m' + 1)).map (fun i => 2 ^ i % m')).Nodup := by
      apply List.pairwise_map.2
      apply List.Pairwise.imp_of_mem _ (my_nodup_range _)
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
    have := my_len_le' hnd hsub
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
        rw [Nat.pow_zero] at hd; omega
    rw [hu0, Nat.Coprime, Nat.gcd_zero_right] at hu; omega
  · rcases Nat.mod_two_eq_zero_or_one q with h | h
    · have e1 : (2 ^ (d + 1)) % 2 = 0 := by rw [Nat.pow_succ]; omega
      rw [hd, Nat.add_mod, Nat.mul_mod, h] at e1; omega
    · exact h

theorem NonWieferich.three_le {q : Nat} [NonWieferich q] : 3 ≤ q := by
  have := NonWieferich.odd (q := q); have := NonWieferich.one_lt (q := q); omega

theorem NonWieferich.gen {q : Nat} [NonWieferich q] : ∃ d u, 0 < d ∧ 2 ^ d = 1 + q * u ∧ Nat.Coprime q u := by
  obtain ⟨d, u, hd, hu⟩ := NonWieferich.unit (q := q)
  have hp3 := NonWieferich.three_le (q := q)
  have hodd := NonWieferich.odd (q := q)
  obtain ⟨D0, hD0, hD0p, hD0m⟩ := exists_pow2_period q (by omega) (coprime_two_of_odd hodd)
  obtain ⟨D, ⟨hD, hDm⟩, hmin⟩ := exists_least (fun D => 0 < D ∧ 2 ^ D % q = 1 % q) ⟨D0, hD0, hD0m⟩
  have hdm : 2 ^ d % q = 1 % q := by rw [hd, Nat.add_mul_mod_self_left]
  have hr : d % D = 0 := by
    match (inferInstance : Decidable (d % D = 0)) with
    | isTrue hg => exact hg
    | isFalse h =>
    exfalso
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
    rw [e, hv, hz] at hd; (generalize 2 ^ D / q = W at *; rw [Nat.pow_two] at hd; nat_ring)
  have hu' := Nat.eq_of_mul_eq_mul_left (by omega) hpu
  refine ⟨D, 2 ^ D / q, hD, hv, ?_⟩
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
  obtain ⟨d, u, hd0, hd, hu⟩ := NonWieferich.gen (q := q)
  refine ⟨d * q ^ K, Nat.mul_pos hd0 (powp_pos q K), ?_⟩
  rw [Nat.pow_mul, hd, one_mod_P]
  simpa [Nat.pow_one, Nat.add_comm] using (order_iff NonWieferich.odd NonWieferich.three_le (Nat.le_refl 1) hu K _).2 (Nat.dvd_refl _)

theorem two_gen (K x : Nat) (hx : x % q = 1) : ∃ s, 2 ^ s % q ^ (K + 1) = x % q ^ (K + 1) := by
  obtain ⟨d, u, _, hd, hu⟩ := NonWieferich.gen (q := q)
  obtain ⟨t, _, ht⟩ := unit_power_cover NonWieferich.odd NonWieferich.three_le (Nat.le_refl 1) hu K x (by rw [Nat.pow_one]; exact hx)
  exact ⟨d * t, by rw [Nat.pow_mul, hd]; simpa [Nat.pow_one, Nat.add_comm] using ht⟩

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

namespace TS

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
  rw [my_countP_eq_zero] at z
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
      rw [my_countP_eq_zero]; intro y hy
      show S (y+1) = false
      cases hS : S (y+1)
      · rfl
      · have := h (y+1) (by have := List.mem_range.mp hy; omega) hS; omega
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

theorem mod_cases_of_lt_two_mul (y m' : Nat) (h : y < 2*m') : (y < m' ∧ y % m' = y) ∨ (m' ≤ y ∧ y % m' = y - m') := by
  cases Nat.lt_or_ge y m' with
  | inl l => exact Or.inl ⟨l, Nat.mod_eq_of_lt l⟩
  | inr g => exact Or.inr ⟨g, by rw [Nat.mod_eq_sub_mod g, Nat.mod_eq_of_lt (by omega)]⟩

def add (m' : Nat) (A B : Nat → Bool) (x : Nat) : Bool :=
  (List.range m').any (fun a => A a && B ((x + (m' - a)) % m'))

theorem mem_add {A B : Nat → Bool} {x : Nat} :
    add m' A B x = true ↔ ∃ a, a < m' ∧ A a = true ∧ B ((x + (m' - a)) % m') = true := by
  simp [add, List.any_eq_true, List.mem_range]

theorem sub_add_eq (a b : Nat) (ha : a < m') (hb : b < m') : ((a + b) % m' + (m' - a)) % m' = b := by
  rcases mod_cases_of_lt_two_mul (a+b) m' (by omega) with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rw [e1]
  · rcases mod_cases_of_lt_two_mul (a + b + (m' - a)) m' (by omega) with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;> rw [e2] <;> omega
  · rcases mod_cases_of_lt_two_mul (a + b - m' + (m' - a)) m' (by omega) with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;> rw [e2] <;> omega

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
    have : k0 * t * b = t * (b * k0) := by simp only [Nat.mul_comm, Nat.mul_left_comm]
    rw [this, hbk]; (first | nat_ring | int_ring)
  rw [e, Nat.add_mul_mod_self_left, Nat.add_mod_right, Nat.mod_eq_of_lt hx] at this
  exact this

theorem card_le_add {A B : Nat → Bool} (hB : B 0 = true) : card m' A ≤ card m' (add m' A B) :=
  card_mono (fun x hx hA => mem_add.mpr ⟨x, hx, hA, by
    rw [show x + (m' - x) = m' by omega, Nat.mod_self]; exact hB⟩)

theorem mod_sub_sub_eq (x a a1 : Nat) (hx : x < m') (ha : a < m') (ha1 : a1 < m') :
    (x + (m' - ((x + (m' - a1)) % m' + a) % m')) % m' = (a1 + (m' - a)) % m' := by
  have h1 := mod_cases_of_lt_two_mul (x + (m' - a1)) m' (by omega)
  generalize (x + (m' - a1)) % m' = b1 at *
  have hb1 : b1 < m' := by omega
  have h2 := mod_cases_of_lt_two_mul (b1 + a) m' (by omega)
  generalize (b1 + a) % m' = a2 at *
  have ha2 : a2 < m' := by omega
  have h3 := mod_cases_of_lt_two_mul (x + (m' - a2)) m' (by omega)
  have h4 := mod_cases_of_lt_two_mul (a1 + (m' - a)) m' (by omega)
  generalize (x + (m' - a2)) % m' = l at *
  generalize (a1 + (m' - a)) % m' = r at *
  omega

theorem bool_and3_true {x y z : Bool} (h : (x && y && !z) = true) :
    x = true ∧ y = true ∧ z = false := by
  revert h; cases x <;> cases y <;> cases z <;> decide

theorem bool_and3_intro {x y z : Bool} (hx : x = true) (hy : y = true) (hz : z = false) :
    (x && y && !z) = true := by
  subst hx hy hz; rfl

theorem chowla (hm : 0 < m') : ∀ n (A B : Nat → Bool), card m' B = n →
    (∃ a, a < m' ∧ A a = true) → B 0 = true →
    (∀ b, b < m' → B b = true → b ≠ 0 → Nat.gcd b m' = 1) →
    min m' (card m' A + card m' B - 1) ≤ card m' (add m' A B) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro A B hn hA hB0 hunit
  obtain ⟨a0, ha0, hAa0⟩ := hA
  cases hcb : (List.range m').any (fun a => (List.range m').any
      (fun b => A a && B b && !A ((a + b) % m'))) with
  | true =>
    have hc : ∃ a b, a < m' ∧ b < m' ∧ A a = true ∧ B b = true ∧ A ((a + b) % m') = false := by
      obtain ⟨a, ha, hcb'⟩ := List.any_eq_true.1 hcb
      obtain ⟨b, hb, hab⟩ := List.any_eq_true.1 hcb'
      obtain ⟨hAa, hBb, hn'⟩ := bool_and3_true hab
      exact ⟨a, b, List.mem_range.1 ha, List.mem_range.1 hb, hAa, hBb, hn'⟩
    obtain ⟨a, b, ha, hb, hAa, hBb, hn'⟩ := hc
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
        rw [mod_sub_sub_eq x a a1 hx ha ha1]; exact h1
    have : card m' A' + card m' B' = card m' A + card m' B := by
      simp only [A']; omega
    omega
  | false =>
    have hc : ¬ ∃ a b, a < m' ∧ b < m' ∧ A a = true ∧ B b = true ∧ A ((a + b) % m') = false := by
      rintro ⟨a, b, ha, hb, hAa, hBb, hn'⟩
      have ht : (List.range m').any (fun a => (List.range m').any
          (fun b => A a && B b && !A ((a + b) % m'))) = true :=
        List.any_eq_true.2 ⟨a, List.mem_range.2 ha,
          List.any_eq_true.2 ⟨b, List.mem_range.2 hb, bool_and3_intro hAa hBb hn'⟩⟩
      rw [hcb] at ht
      cases ht
    have hcl : ∀ a b, a < m' → b < m' → A a = true → B b = true → A ((a + b) % m') = true := by
      intro a b ha hb hAa hBb
      cases h : A ((a + b) % m')
      · exact absurd ⟨a, b, ha, hb, hAa, hBb, h⟩ hc
      · rfl
    have hle := card_le_add (m' := m') (A := A) hB0
    cases hzb : (List.range m').any (fun b => true && B b && !(b == 0)) with
    | true =>
      have hnz : ∃ b, b < m' ∧ B b = true ∧ b ≠ 0 := by
        obtain ⟨b, hb, hbb⟩ := List.any_eq_true.1 hzb
        obtain ⟨_, hBb, hb0⟩ := bool_and3_true hbb
        refine ⟨b, List.mem_range.1 hb, hBb, ?_⟩
        intro h0; subst h0; exact absurd hb0 (by decide)
      obtain ⟨b, hb, hBb, hb0⟩ := hnz
      have full := closed_full (by omega) A a0 ha0 hAa0 b (hunit b hb hBb hb0)
        (fun a ha hAa => hcl a b ha hb hAa hBb)
      have := card_full (m' := m') full
      have := card_le (m' := m') (add m' A B)
      omega
    | false =>
      have hnz : ¬ ∃ b, b < m' ∧ B b = true ∧ b ≠ 0 := by
        rintro ⟨b, hb, hBb, hb0⟩
        have ht : (List.range m').any (fun b => true && B b && !(b == 0)) = true :=
          List.any_eq_true.2 ⟨b, List.mem_range.2 hb, bool_and3_intro (x := true) rfl hBb (by rw [show (b == 0) = false from Bool.eq_false_iff.2 (fun c => hb0 (nat_beq_iff.1 c))])⟩
        rw [hzb] at ht
        cases ht
      have : card m' B ≤ 1 := card_le_one_zero (fun x hx hBx => by
        cases Nat.decEq x 0 with
        | isTrue h => exact h
        | isFalse h => exact absurd ⟨x, hx, hBx, h⟩ hnz)
      omega

theorem nat_beq_comm (a b : Nat) : (a == b) = (b == a) := by
  match Nat.decEq a b with
  | isTrue h => subst h; rfl
  | isFalse h =>
    have h1 : (a == b) = false := Bool.eq_false_iff.2 (fun c => h (nat_beq_iff.1 c))
    have h2 : (b == a) = false := Bool.eq_false_iff.2 (fun c => h (nat_beq_iff.1 c).symm)
    rw [h1, h2]

theorem countP_beq_one (y : Nat) : ∀ L : List Nat, L.Nodup → y ∈ L →
    L.countP (fun x => x == y) = 1
  | [], _, h => absurd h List.not_mem_nil
  | a :: L, hn, h => by
    rw [List.nodup_cons] at hn
    rw [List.countP_cons]
    match Nat.decEq a y with
    | isTrue hay =>
      subst hay
      have h0 : L.countP (fun x => x == a) = 0 := (my_countP_eq_zero L _).2
        (fun x hx => Bool.eq_false_iff.2 (fun c => hn.1 ((nat_beq_iff.1 c) ▸ hx)))
      have ht : (a == a) = true := nat_beq_iff.2 rfl
      rw [h0, ht]; rfl
    | isFalse hay =>
      have hyL : y ∈ L := by
        rcases List.mem_cons.1 h with h' | h'
        · exact absurd h'.symm hay
        · exact h'
      have hf : (a == y) = false := Bool.eq_false_iff.2 (fun c => hay (nat_beq_iff.1 c))
      rw [countP_beq_one y L hn.2 hyL, hf]; rfl

theorem card_single {y : Nat} (hy : y < m') : card m' (fun x => x == y) = 1 :=
  countP_beq_one y _ (my_nodup_range _) (List.mem_range.mpr hy)

theorem card_zero {S : Nat → Bool} (h : ∀ x, x < m' → S x = false) : card m' S = 0 := by
  unfold card; rw [my_countP_eq_zero]; intro x hx; simp [h x (List.mem_range.mp hx)]

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
      simp only [nat_beq_iff] at hx; subst hx
      rw [Bool.eq_false_iff]; intro hc
      simp only [List.any_eq_true, nat_beq_iff] at hc
      obtain ⟨i, hi, hfi⟩ := hc
      have := hinj a (List.mem_cons_self ..) i (List.mem_cons_of_mem _ hi) hfi.symm
      exact hL.1 (this ▸ hi))
    have e : card m' (fun x => (a :: L).any (fun i => f i == x))
        = card m' (fun x => (x == f a) || L.any (fun i => f i == x)) :=
      card_congr (fun x _ => by simp only [List.any_cons]; congr 1; exact nat_beq_comm _ _)
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
  have C := pow_mod_one _ _ k A
  rw [← Nat.pow_mul, hkw, Nat.pow_succ, Nat.pow_mul, Nat.mul_mod, pow_mod_one _ _ w B] at C
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
  have m2 : Nat.Coprime m' 2 := coprime_two_of_odd hodd
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

def powSet (m' q e s : Nat) (x : Nat) : Bool := (List.range e).any (fun i => (q ^ s * 2 ^ i) % m' == x)

def sumset (m' q e : Nat) : Nat → Nat → Bool
  | 0 => fun x => x == 0
  | s + 1 => add m' (sumset m' q e s) (powSet m' q e s)

def good (e i : Nat) : Bool := i == 0 || Nat.gcd i e == 1
def goodIdx (e : Nat) : List Nat := (List.range e).filter (good e)
def diffVal (m' q s i : Nat) : Nat := (q ^ s * (2 ^ i - 1)) % m'
def diffSet (m' q e s : Nat) (x : Nat) : Bool := (goodIdx e).any (fun i => diffVal m' q s i == x)

def phi (e : Nat) : Nat := card e (fun i => Nat.gcd i e == 1)

theorem mod_sub_sub_add_cancel {m' : Nat} (x a c : Nat) (hx : x < m') (ha : a < m') (hc : c < m') :
    (((x + (m' - c)) % m' + (m' - a)) % m' + c) % m' = (x + (m' - a)) % m' := by
  have h1 := mod_cases_of_lt_two_mul (x + (m' - c)) m' (by omega)
  generalize (x + (m' - c)) % m' = y at *
  have h2 := mod_cases_of_lt_two_mul (y + (m' - a)) m' (by omega)
  generalize (y + (m' - a)) % m' = z at *
  have h3 := mod_cases_of_lt_two_mul (z + c) m' (by omega)
  have h4 := mod_cases_of_lt_two_mul (x + (m' - a)) m' (by omega)
  generalize (z + c) % m' = l at *
  generalize (x + (m' - a)) % m' = r at *
  omega

section
variable {m' q e : Nat} (hm : 1 < m') (hodd : m' % 2 = 1) (hq : Nat.gcd q m' = 1)
  (he : 2 ^ e % m' = 1) (hmin : ∀ i, 0 < i → i < e → 2 ^ i % m' ≠ 1) (he0 : 0 < e)

include hm hodd he he0 in
theorem length_goodIdx : (goodIdx e).length = phi e + 1 := by
  have e2 := two_le_e hm hodd he he0
  have hU := card_union_inter (m' := e) (fun i => i == 0) (fun i => Nat.gcd i e == 1)
  have h1 := card_single (m' := e) (y := 0) he0
  have h0 : card e (fun i => (i == 0) && (Nat.gcd i e == 1)) = 0 := card_zero (fun x _ => by
    cases hx : (x == 0) <;> simp only [Bool.false_and, Bool.true_and]
    simp only [nat_beq_iff] at hx; subst hx
    rw [Nat.gcd_zero_left]
    exact Bool.eq_false_iff.2 (fun c => by have := nat_beq_iff.1 c; omega))
  have : (goodIdx e).length = card e (good e) := by
    unfold goodIdx card; rw [List.countP_eq_length_filter]
  unfold phi; unfold good at this; omega

include hm hodd hq he hmin he0 in
theorem card_diffSet (s : Nat) : card m' (diffSet m' q e s) = phi e + 1 := by
  rw [← length_goodIdx hm hodd he he0]
  apply card_image
  · exact (my_nodup_range _).sublist List.filter_sublist
  · intro i _; exact Nat.mod_lt _ (by omega)
  · intro i hi j hj h
    have hi' := List.mem_range.mp (List.mem_filter.mp hi).1
    have hj' := List.mem_range.mp (List.mem_filter.mp hj).1
    rcases Nat.lt_trichotomy i j with l | l | l
    · exact absurd h (distinct hm hodd hq hmin s i j l hj')
    · exact l
    · exact absurd h.symm (distinct hm hodd hq hmin s j i l hi')

include hm hodd hq he he0 in
theorem diffSet_unit (s : Nat) : ∀ b, b < m' → diffSet m' q e s b = true → b ≠ 0 → Nat.gcd b m' = 1 := by
  intro b _ hb hb0
  simp only [diffSet, List.any_eq_true, nat_beq_iff] at hb
  obtain ⟨i, hi, rfl⟩ := hb
  have hg := (List.mem_filter.mp hi).2
  simp only [good, Bool.or_eq_true, nat_beq_iff] at hg
  rcases hg with h | h
  · subst h; simp [diffVal] at hb0
  · unfold diffVal
    rw [← Nat.gcd_rec, Nat.gcd_comm]
    exact Nat.Coprime.symm (Nat.Coprime.mul_right (Nat.Coprime.symm (Nat.Coprime.pow_left s hq))
      (Nat.Coprime.symm (unit_two_pow_sub_one hm hodd he he0 i h)))

include he0 in
theorem diffSet_zero (s : Nat) : diffSet m' q e s 0 = true := by
  unfold diffSet
  rw [List.any_eq_true]
  refine ⟨0, List.mem_filter.mpr ⟨List.mem_range.mpr he0, rfl⟩, ?_⟩
  have h0 : diffVal m' q s 0 = 0 := by
    unfold diffVal
    rw [Nat.pow_zero, Nat.sub_self, Nat.mul_zero, Nat.zero_mod]
  rw [h0]
  rfl

include hm in
theorem shift_sub (s : Nat) : ∀ x, x < m' →
    add m' (sumset m' q e s) (diffSet m' q e s) ((x + (m' - q ^ s % m')) % m') = true → sumset m' q e (s + 1) x = true := by
  intro x hx h
  obtain ⟨a, ha, hA, hDa⟩ := mem_add.mp h
  simp only [diffSet, List.any_eq_true, nat_beq_iff] at hDa
  obtain ⟨i, hi, hfi⟩ := hDa
  refine mem_add.mpr ⟨a, ha, hA, ?_⟩
  simp only [powSet, List.any_eq_true, nat_beq_iff, List.mem_range]
  refine ⟨i, List.mem_range.mp (List.mem_filter.mp hi).1, ?_⟩
  have hP := Nat.two_pow_pos i
  have : q ^ s * 2 ^ i = q ^ s * (2 ^ i - 1) + q ^ s := by
    rw [Nat.mul_sub_one]; have := Nat.mul_le_mul_left (q ^ s) hP; simp at this; omega
  rw [this, Nat.add_mod, ← diffVal, hfi]
  exact mod_sub_sub_add_cancel x a _ hx ha (Nat.mod_lt _ (by omega))

include he0 in
theorem sumset_nonempty (hm0 : 0 < m') : ∀ s, ∃ a, a < m' ∧ sumset m' q e s a = true := by
  intro s; induction s with
  | zero => exact ⟨0, hm0, rfl⟩
  | succ s ih =>
    obtain ⟨a, ha, h⟩ := ih
    refine ⟨_, Nat.mod_lt _ hm0, add_of ha (Nat.mod_lt (q ^ s) hm0) h ?_⟩
    simp only [powSet, List.any_eq_true, nat_beq_iff, List.mem_range]
    exact ⟨0, he0, by rw [Nat.pow_zero, Nat.mul_one]⟩

include hm hodd hq he hmin he0 in
theorem growth : ∀ s, min m' (1 + s * phi e) ≤ card m' (sumset m' q e s) := by
  intro s; induction s with
  | zero =>
    have := card_single (m' := m') (y := 0) (by omega)
    simp only [sumset, Nat.zero_mul]; omega
  | succ s ih =>
    have hc := chowla (m' := m') (by omega) _ (sumset m' q e s) (diffSet m' q e s) rfl
      (sumset_nonempty he0 (by omega) s) (diffSet_zero he0 s) (diffSet_unit hm hodd hq he he0 s)
    rw [card_diffSet hm hodd hq he hmin he0 s] at hc
    have hsh := card_shift (m' := m') (by omega) (add m' (sumset m' q e s) (diffSet m' q e s)) (m' - q ^ s % m')
    have hmono := card_mono (m' := m') (shift_sub (q := q) (e := e) hm s)
    rw [Nat.succ_mul]; omega

include hm hodd hq he hmin he0 in
theorem covers (s : Nat) (hs : m' ≤ 1 + s * phi e) : ∀ x, x < m' → sumset m' q e s x = true := by
  have g := growth hm hodd hq he hmin he0 s
  have hle := card_le (m' := m') (sumset m' q e s)
  have hfull := card_full (m' := m') (S := fun _ => true) (fun _ _ => rfl)
  intro x hx
  exact eq_of_card (S := sumset m' q e s) (T := fun _ => true) (fun _ _ _ => rfl) (by omega) x hx rfl
end
end TS

def wsum (q : Nat) : List Nat → Nat
  | [] => 0
  | i :: is => q ^ is.length * 2 ^ i + wsum q is

def Covers (q m' γ : Nat) : Prop :=
  ∀ x, x < m' → ∃ I : List Nat, I.length = γ ∧ wsum q I % m' = x % m'

theorem sumset_wsum (q m' e : Nat) (hm0 : 0 < m') : ∀ s x, x < m' → TS.sumset m' q e s x = true →
    ∃ I : List Nat, I.length = s ∧ wsum q I % m' = x := by
  intro s
  induction s with
  | zero =>
    intro x _ h
    simp only [TS.sumset, nat_beq_iff] at h
    exact ⟨[], rfl, by simp [wsum, h]⟩
  | succ s ih =>
    intro x hx h
    obtain ⟨a, ha, hA, hB⟩ := TS.mem_add.mp h
    obtain ⟨I, hl, hw⟩ := ih a ha hA
    simp only [TS.powSet, List.any_eq_true, nat_beq_iff, List.mem_range] at hB
    obtain ⟨i, _, hi⟩ := hB
    refine ⟨i :: I, by simp [hl], ?_⟩
    simp only [wsum, hl]
    rw [Nat.add_mod, hi, hw]
    have h1 := TS.mod_cases_of_lt_two_mul (x + (m' - a)) m' (by omega)
    generalize (x + (m' - a)) % m' = y at *
    have h2 := TS.mod_cases_of_lt_two_mul (y + a) m' (by omega)
    generalize (y + a) % m' = z at *
    omega

theorem covers_of_growth (q m' e s : Nat) (hm : 1 < m') (hodd : m' % 2 = 1)
    (hq : Nat.gcd q m' = 1) (he : 2 ^ e % m' = 1 % m') (hmin : ∀ i, 0 < i → i < e → 2 ^ i % m' ≠ 1 % m')
    (he0 : 0 < e) (hs : m' ≤ 1 + s * TS.phi e) : Covers q m' s := by
  have h1 : 1 % m' = 1 := Nat.mod_eq_of_lt hm
  have he' : 2 ^ e % m' = 1 := by rw [he, h1]
  have hmin' : ∀ i, 0 < i → i < e → 2 ^ i % m' ≠ 1 := fun i a b => by rw [← h1]; exact hmin i a b
  intro x hx
  obtain ⟨I, hl, hw⟩ := sumset_wsum q m' e (by omega) s x hx (TS.covers hm hodd hq he' hmin' he0 s hs x hx)
  exact ⟨I, hl, by rw [hw, Nat.mod_eq_of_lt hx]⟩

theorem wsum_reduce (q D m' : Nat) (hD : 2 ^ D % m' = 1 % m') :
    ∀ I : List Nat, wsum q (I.map (· % D)) % m' = wsum q I % m' := by
  intro I
  induction I with
  | nil => rfl
  | cons i I ih =>
    simp only [List.map_cons, wsum, List.length_map]
    have h2 : 2 ^ (i % D) % m' = 2 ^ i % m' := pow_two_mod_period m' D hD _ _ (Nat.mod_mod _ _)
    rw [Nat.add_mod, Nat.mul_mod, h2, ← Nat.mul_mod, ih, ← Nat.add_mod]

def CoversBounded (q m' γ e : Nat) : Prop :=
  ∀ x, x < m' → ∃ I : List Nat, I.length = γ ∧ (∀ a ∈ I, a < e) ∧ wsum q I % m' = x % m'

theorem covers_iff_bounded (q m' e : Nat) (he0 : 0 < e) (he : 2 ^ e % m' = 1 % m') (γ : Nat) :
    Covers q m' γ ↔ CoversBounded q m' γ e := by
  constructor
  · intro h x hx
    obtain ⟨I, hl, hw⟩ := h x hx
    refine ⟨I.map (· % e), by simp [hl], ?_, ?_⟩
    · intro a ha
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
      exact Nat.mod_lt _ he0
    · rw [wsum_reduce q e m' he I]; exact hw
  · rintro h x hx
    obtain ⟨I, hl, -, hw⟩ := h x hx
    exact ⟨I, hl, hw⟩

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

theorem unit_inv_pow (p g0 : Int) : ∀ M : Nat, ∃ z : Int, p ^ (M + 1) ∣ (1 + p * g0) * z - 1
  | 0 => ⟨1, g0, by rw [Int.pow_succ, Int.pow_zero]; int_ring⟩
  | M + 1 => by
    obtain ⟨z, h, hh⟩ := unit_inv_pow p g0 M
    have e1 : p ^ (M + 1) = p ^ M * p := Int.pow_succ _ _
    have e2 : p ^ (M + 1 + 1) = p ^ M * p * p := by rw [Int.pow_succ, e1]
    rw [e1] at hh
    refine ⟨z * (1 - p ^ M * p * h), -(p ^ M * h * h), ?_⟩
    rw [e2]
    have hz : (1 + p * g0) * z = 1 + p ^ M * p * h := by omega
    have e3 : (1 + p * g0) * (z * (1 - p ^ M * p * h))
        = ((1 + p * g0) * z) * (1 - p ^ M * p * h) := by int_ring
    rw [e3, hz]; int_ring

theorem wide_step_identity (p Yg ρ y0s Δ z xx G X Pw a1 a2 : Int) (hp : p ≠ 0)
    (hxx : xx = 1 + p * y0s) (hΔ : Δ = ρ - y0s) (hX : X = 1 + p * Δ * z)
    (hU : xx * z - 1 = Pw * p * a2) (hA : G - X = Pw * p * a1)
    (hrel : p * Yg + 1 = xx * G) : Yg - ρ = Pw * (p * Δ * a2 + xx * a1) := by
  have hU' : xx * z = 1 + Pw * p * a2 := by omega
  have hG : G = X + Pw * p * a1 := by omega
  apply Int.eq_of_mul_eq_mul_left hp
  have h1 : p * (Yg - ρ) = xx * G - 1 - p * ρ := by rw [Int.mul_sub]; omega
  have e : xx * (X + Pw * p * a1) = xx * X + xx * Pw * p * a1 := by int_ring
  have e' : xx * X = xx + p * Δ * (xx * z) := by rw [hX]; int_ring
  rw [h1, hG, e, e', hU']
  subst hxx hΔ
  int_ring

theorem wide_step {p : Int} {K P : Nat} {uPn : Nat} {b : Nat → Nat} {y0 c : Int}
    (q : Nat) (hq3 : 3 ≤ q) (hodd : q % 2 = 1) (hcop : Nat.Coprime q uPn) (hpq : p = (q : Int))
    (S : Setup p K P (uPn : Int) b y0 c) (τ : Nat) (ρ : Int) (N : Nat) (hN : K ≤ N)
    (f : Nat → Nat)
    (hf : ∀ J : Nat → Nat, (∀ l, 1 ≤ l → l ≤ K + τ → J l = f l) →
      Integral p P y0 b J (K + 1 + τ) ∧ p ^ K ∣ chain p P y0 b J (K + 1 + τ) - ρ) :
    ∃ j0 : Nat, j0 < q ^ (N - K) ∧ ∀ J : Nat → Nat, (∀ l, 1 ≤ l → l ≤ K + τ → J l = f l) →
      J (K + 1 + τ) % q ^ (N - K) = j0 → p ^ N ∣ chain p P y0 b J (K + 1 + τ) - ρ := by
  have hpne : p ≠ 0 := S.hp
  obtain ⟨Jr, hJr⟩ : ∃ Jr : Nat → Nat, Jr = fun l => if l ≤ K + τ then f l else 0 := ⟨_, rfl⟩
  have hJra : ∀ l, l ≤ K + τ → Jr l = f l := by intro l h; rw [hJr]; simp [h]
  have hJrb : Jr (K + 1 + τ) = 0 := by
    have hn : ¬ (K + 1 + τ ≤ K + τ) := by omega
    rw [hJr]; simp [hn]
  obtain ⟨hIr, hCr⟩ := hf Jr (fun l _ h => hJra l h)
  obtain ⟨xx, hxxd⟩ : ∃ xx : Int, xx = (2 : Int) ^ (b (K + 1 + τ)) * chain p P y0 b Jr (K + τ) := ⟨_, rfl⟩
  obtain ⟨y0s, hy0s⟩ : ∃ v : Int, v = chain p P y0 b Jr (K + 1 + τ) := ⟨_, rfl⟩
  have hrelJ : ∀ J : Nat → Nat, (∀ l, 1 ≤ l → l ≤ K + τ → J l = f l) →
      p * chain p P y0 b J (K + 1 + τ) + 1 = xx * 2 ^ (J (K + 1 + τ) * P) := by
    intro J hJ
    obtain ⟨hI, _⟩ := hf J hJ
    have h := chain_rel hI (K + τ) (by omega)
    have e : K + τ + 1 = K + 1 + τ := by omega
    rw [e] at h
    have hc : chain p P y0 b J (K + τ) = chain p P y0 b Jr (K + τ) :=
      chain_congr p P y0 b J Jr (K + τ) (fun l h1 h2 => by rw [hJ l h1 h2, hJra l h2])
    rw [h, hc, hxxd]; int_ring
  have hxx : xx = 1 + p * y0s := by
    have h := hrelJ Jr (fun l _ h => hJra l h)
    rw [hJrb, Nat.zero_mul, Int.pow_zero, Int.mul_one] at h
    rw [hy0s]; omega
  obtain ⟨δ, hδ⟩ := hCr
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : Int, Δ = ρ - y0s := ⟨_, rfl⟩
  have hΔd : Δ = p ^ K * (-δ) := by rw [Int.mul_neg]; omega
  obtain ⟨z, hz⟩ := unit_inv_pow p y0s N
  rw [← hxx] at hz
  obtain ⟨a2, ha2⟩ := hz
  obtain ⟨X, hX⟩ : ∃ X : Int, X = 1 + p * Δ * z := ⟨_, rfl⟩
  have hX1 : p ^ (K + 1) ∣ X - 1 := by
    refine ⟨-(δ * z), ?_⟩
    rw [hX, hΔd, Int.pow_succ]; int_ring
  subst hpq
  obtain ⟨t, ht, hcov⟩ := cover_int q uPn K (N - K) hodd hq3 hcop X hX1
  refine ⟨t, ht, fun J hJ hJt => ?_⟩
  have hg : ((1 + q ^ (K + 1) * uPn : Nat) : Int) = (2 : Int) ^ P := by
    rw [Int.natCast_add, Int.natCast_mul, Int.natCast_pow, Int.natCast_one]
    exact S.h2P.symm
  have hpow : (2 : Int) ^ (J (K + 1 + τ) * P) = ((2 : Int) ^ P) ^ (J (K + 1 + τ)) := by
    rw [Nat.mul_comm, Int.pow_mul]
  have hc := hcov (J (K + 1 + τ)) hJt
  rw [hg, ← hpow, show K + 1 + (N - K) = N + 1 by omega] at hc
  obtain ⟨a1, ha1⟩ := hc
  have e1 : (q : Int) ^ (N + 1) = (q : Int) ^ N * (q : Int) := Int.pow_succ _ _
  rw [e1] at ha1 ha2
  have hres := wide_step_identity (q : Int) (chain (q : Int) P y0 b J (K + 1 + τ)) ρ y0s Δ z xx
    ((2 : Int) ^ (J (K + 1 + τ) * P)) X ((q : Int) ^ N) a1 a2 hpne hxx hΔ hX ha2 ha1
    (hrelJ J hJ)
  exact ⟨_, hres⟩

theorem tail_lemma (q : Nat) [NonWieferich q] (u : List Nat) (hu : ∀ e ∈ u, e ≤ 1) (α : Nat)
    (hlen : u.length = α) (rb ρ : Nat)
    (hρ : 2 ^ α * ρ = q ^ ones u * rb + kappa q u)
    (mq m' β B y : Nat) (hA : mq ∣ q ^ β)
    (hρy : ρ + q ^ ones u * (B + 1) ≤ y)
    (hyc : q ^ (ones u + β) * m' ∣ y - ρ) :
    ∃ w : Nat, B < w ∧ Reaches q w y ∧ w % (2 ^ α * mq * m') = rb % (2 ^ α * mq * m') ∧
      w ≤ 2 ^ α * y := by
  obtain ⟨n, hn⟩ : ∃ n, n = ones u := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = kappa q u := ⟨_, rfl⟩
  rw [← hn, ← hκ] at hρ
  rw [← hn] at hρy hyc
  have hqn : 0 < q ^ n := powp_pos q n
  have h2a : 0 < 2 ^ α := Nat.pow_pos (by omega)
  obtain ⟨c, hc⟩ := hyc
  obtain ⟨a', ha'⟩ := hA
  have hz : y - ρ = q ^ n * (q ^ β * m' * c) := by
    rw [hc, Nat.pow_add]; (first | nat_ring | int_ring)
  have hy : y = ρ + q ^ n * (q ^ β * m' * c) := by
    have : ρ ≤ y := by
      have := Nat.mul_pos hqn (Nat.succ_pos B)
      omega
    omega
  obtain ⟨z, hzdef⟩ : ∃ z, z = q ^ β * m' * c := ⟨_, rfl⟩
  rw [← hzdef] at hz hy
  have hzB : B + 1 ≤ z := by
    have h1 : q ^ n * (B + 1) ≤ q ^ n * z := by omega
    exact Nat.le_of_mul_le_mul_left h1 hqn
  have hw1 : q ^ n * (rb + 2 ^ α * z) + κ = 2 ^ α * y := by
    have e : q ^ n * (rb + 2 ^ α * z) + κ = (q ^ n * rb + κ) + 2 ^ α * (q ^ n * z) := by
      (first | nat_ring | int_ring)
    rw [e, ← hρ, hy]; (first | nat_ring | int_ring)
  refine ⟨rb + 2 ^ α * z, ?_, ?_, ?_, ?_⟩
  · have := Nat.le_mul_of_pos_left z h2a
    omega
  · have hd : 2 ^ u.length ∣ q ^ ones u * (rb + 2 ^ α * z) + kappa q u := by
      rw [hlen, ← hn, ← hκ, hw1]; exact Nat.dvd_mul_right _ _
    have := word_trajectory q u hu (rb + 2 ^ α * z) hd
    rw [← hn, ← hκ, hw1, hlen, Nat.mul_div_cancel_left _ h2a] at this
    exact this
  ·
    have e : 2 ^ α * z = (2 ^ α * mq * m') * (a' * c) := by
      rw [hzdef, ha']; (first | nat_ring | int_ring)
    rw [e, Nat.add_mul_mod_self_left]
  · have hrb : rb ≤ 2 ^ α * ρ := by
      have := Nat.le_mul_of_pos_left rb hqn
      omega
    have hz2 : z ≤ q ^ n * z := Nat.le_mul_of_pos_left z hqn
    have : 2 ^ α * z ≤ 2 ^ α * (q ^ n * z) := Nat.mul_le_mul_left _ hz2
    have e2 : 2 ^ α * y = 2 ^ α * ρ + 2 ^ α * (q ^ n * z) := by
      rw [hy]; (first | nat_ring | int_ring)
    omega

theorem int_cancel (m c : Nat) (hm0 : 0 < m) (hcop : Nat.Coprime m c) (a : Int)
    (h : (m : Int) ∣ (c : Int) * a) : (m : Int) ∣ a := by
  rcases Nat.lt_or_ge 1 m with hm | hm
  · obtain ⟨k, w, hkw⟩ := nat_bez c m hm (Nat.Coprime.symm hcop)
    have hI : (c : Int) * (k : Int) = (m : Int) * (w : Int) + 1 := by
      have := congrArg (fun n : Nat => (n : Int)) hkw
      simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one] at this
      exact this
    obtain ⟨g, hg⟩ := h
    have e : a = ((c : Int) * (k : Int)) * a - (m : Int) * ((w : Int) * a) := by
      rw [hI]; int_ring
    have e2 : ((c : Int) * (k : Int)) * a = (m : Int) * ((k : Int) * g) := by
      have : ((c : Int) * (k : Int)) * a = (k : Int) * ((c : Int) * a) := by int_ring
      rw [this, hg]; int_ring
    refine ⟨(k : Int) * g - (w : Int) * a, ?_⟩
    rw [Int.mul_sub]; omega
  · have : m = 1 := by omega
    subst this
    exact Int.one_dvd _

theorem nat_mod_to_int_dvd (a b m : Nat) (h : a % m = b % m) : (m : Int) ∣ (a : Int) - (b : Int) := by
  have h' : ((a % m : Nat) : Int) = ((b % m : Nat) : Int) := by rw [h]
  rw [Int.natCast_emod, Int.natCast_emod] at h'
  exact Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.1 h')

theorem mul_mod_cong (a a' b m : Nat) (h : a % m = a' % m) : (a * b) % m = (a' * b) % m := by
  rw [Nat.mul_mod, h, ← Nat.mul_mod]

theorem add_mod_cong (x x' y m : Nat) (h : x % m = x' % m) : (x + y) % m = (x' + y) % m := by
  rw [Nat.add_mod, h, ← Nat.add_mod]

def wsumFun (q : Nat) (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => wsumFun q c n + q ^ n * 2 ^ (c (n + 1))

theorem wsumFun_congr (q : Nat) (c c' : Nat → Nat) :
    ∀ n, (∀ k, 1 ≤ k → k ≤ n → c k = c' k) → wsumFun q c n = wsumFun q c' n
  | 0, _ => rfl
  | n + 1, H => by
    have ih := wsumFun_congr q c c' n (fun k h1 h2 => H k h1 (by omega))
    show wsumFun q c n + q ^ n * 2 ^ (c (n + 1)) = wsumFun q c' n + q ^ n * 2 ^ (c' (n + 1))
    rw [ih, H (n + 1) (by omega) (Nat.le_refl _)]

theorem cover_c (q : Nat) : ∀ I : List Nat, ∃ c : Nat → Nat,
    (∀ k, 1 ≤ k → k ≤ I.length → c k ∈ I) ∧ wsumFun q c I.length = wsum q I
  | [] => ⟨fun _ => 0, fun k h1 h2 => absurd h2 (by simp; omega), by simp [wsumFun, wsum]⟩
  | i :: is => by
    obtain ⟨c', hmem, hW⟩ := cover_c q is
    obtain ⟨cc, hcc⟩ : ∃ cc : Nat → Nat, cc = fun k => if k = is.length + 1 then i else c' k := ⟨_, rfl⟩
    have hcc1 : cc (is.length + 1) = i := by rw [hcc]; simp
    have hcc2 : ∀ k, k ≠ is.length + 1 → cc k = c' k := by intro k hk; rw [hcc]; simp [hk]
    refine ⟨cc, ?_, ?_⟩
    · intro k h1 h2
      by_cases hk : k = is.length + 1
      · rw [hk, hcc1]; simp
      · have hk2 : k ≤ is.length := by simp at h2; omega
        rw [hcc2 k hk]
        exact List.mem_cons_of_mem _ (hmem k h1 hk2)
    · have hcong : wsumFun q cc is.length = wsumFun q c' is.length :=
        wsumFun_congr q _ _ _ (fun k h1 h2 => hcc2 k (by omega))
      show wsumFun q cc is.length + q ^ is.length * 2 ^ (cc (is.length + 1)) = wsum q (i :: is)
      rw [hcong, hW, hcc1]
      show _ = q ^ is.length * 2 ^ i + wsum q is
      omega

def asum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => asum f i + f (i + 1)

def fwdSum (q : Nat) (β : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => 2 ^ (β (n + 1)) * fwdSum q β n + q ^ n

theorem steer (q m' e γ : Nat) (hm0 : 0 < m') (he0 : 0 < e) (he : 2 ^ e % m' = 1 % m')
    (hcov : Covers q m' γ) (hqm : Nat.Coprime m' q) (z0 ρb : Int) :
    ∃ β : Nat → Nat, (∀ l, 1 ≤ l → l ≤ γ + 1 → 1 ≤ β l ∧ β l ≤ e) ∧
      ∀ x : Nat → Int, (m' : Int) ∣ x 0 - z0 →
        (∀ l, 1 ≤ l → l ≤ γ + 1 → (m' : Int) ∣ (q : Int) * x l + 1 - 2 ^ (β l) * x (l - 1)) →
        (m' : Int) ∣ x (γ + 1) - ρb := by
  have hmI : (0 : Int) < (m' : Int) := by omega

  obtain ⟨T, hT⟩ : ∃ T : Int, T = z0 - (q : Int) ^ γ - (q : Int) ^ (γ + 1) * ρb := ⟨_, rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T' : Nat, (T' : Int) = T % (m' : Int) :=
    ⟨(T % (m' : Int)).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))⟩
  have hT'lt : T' < m' := Int.ofNat_lt.1 (by rw [hT']; exact Int.emod_lt_of_pos _ hmI)
  obtain ⟨is, hl, hlt, hws⟩ := (covers_iff_bounded q m' e he0 he γ).1 hcov T' hT'lt
  have hwT : (m' : Int) ∣ (wsum q is : Int) - T := by
    have h1 := nat_mod_to_int_dvd _ _ _ hws
    have h2 : (m' : Int) ∣ (T' : Int) - T := by
      rw [hT', Int.emod_def]; exact ⟨-(T / (m' : Int)), by int_ring⟩
    have e3 : (wsum q is : Int) - T = ((wsum q is : Int) - (T' : Int)) + ((T' : Int) - T) := by int_ring
    rw [e3]; exact Int.dvd_add h1 h2

  obtain ⟨c0, hmem0, hW0⟩ := cover_c q is
  obtain ⟨c, hc⟩ : ∃ c : Nat → Nat, c = fun k => if k = 0 then 0 else if k ≤ γ then c0 k else 0 := ⟨_, rfl⟩
  have hc0 : c 0 = 0 := by rw [hc]; simp
  have hcg : c (γ + 1) = 0 := by
    have hn : ¬ (γ + 1 ≤ γ) := by omega
    rw [hc]; simp [hn]
  have hcmid : ∀ k, 1 ≤ k → k ≤ γ → c k = c0 k := by
    intro k h1 h2; rw [hc]; simp [show k ≠ 0 by omega, h2]
  have hclt : ∀ k, k ≤ γ + 1 → c k < e := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, hc0]; exact he0
    · rcases Nat.lt_or_ge γ k with h2 | h2
      · have : k = γ + 1 := by omega
        rw [this, hcg]; exact he0
      · rw [hcmid k h h2]
        have := hmem0 k h (by rw [hl]; exact h2)
        exact hlt _ this
  have hcW : wsumFun q c γ = wsum q is := by
    rw [← hW0, hl] at *
    exact wsumFun_congr q c c0 γ (fun k h1 h2 => hcmid k h1 h2)
  obtain ⟨β, hβ⟩ : ∃ β : Nat → Nat, β = fun l => (c (l - 1) + e - c l - 1) % e + 1 := ⟨_, rfl⟩
  have hβb : ∀ l, 1 ≤ l → l ≤ γ + 1 → 1 ≤ β l ∧ β l ≤ e := by
    intro l h1 h2
    have hbl : β l = (c (l - 1) + e - c l - 1) % e + 1 := by rw [hβ]
    have := Nat.mod_lt (c (l - 1) + e - c l - 1) he0
    rw [hbl]
    exact ⟨by omega, by omega⟩
  have hβc : ∀ l, 1 ≤ l → l ≤ γ + 1 → (c l + β l) % e = c (l - 1) % e := by
    intro l h1 h2
    have hcl := hclt l h2
    have hdm := Nat.div_add_mod (c (l - 1) + e - c l - 1) e
    have hbl : β l = (c (l - 1) + e - c l - 1) % e + 1 := by rw [hβ]
    have hs : c l + β l + e * ((c (l - 1) + e - c l - 1) / e) = c (l - 1) + e := by omega
    have := Nat.add_mul_mod_self_left (c l + β l) e ((c (l - 1) + e - c l - 1) / e)
    rw [hs, Nat.add_mod_right] at this
    exact this.symm

  have claim1 : ∀ n, n ≤ γ + 1 → (2 ^ (c n) * fwdSum q β n) % m' = wsumFun q c n % m' := by
    intro n
    induction n with
    | zero => intro _; simp [fwdSum, wsumFun, hc0]
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      have hU : 2 ^ (c (n + 1) + β (n + 1)) % m' = 2 ^ (c n) % m' := by
        apply pow_two_mod_period m' e he
        have := hβc (n + 1) (by omega) hn
        simpa using this
      have e1 : 2 ^ (c (n + 1)) * fwdSum q β (n + 1)
          = 2 ^ (c (n + 1) + β (n + 1)) * fwdSum q β n + q ^ n * 2 ^ (c (n + 1)) := by
        show 2 ^ (c (n + 1)) * (2 ^ (β (n + 1)) * fwdSum q β n + q ^ n) = _
        rw [Nat.pow_add]; (first | nat_ring | int_ring)
      rw [e1]
      show _ = (wsumFun q c n + q ^ n * 2 ^ (c (n + 1))) % m'
      rw [add_mod_cong _ (2 ^ (c n) * fwdSum q β n) _ _ (mul_mod_cong _ _ _ _ hU)]
      exact add_mod_cong _ _ _ _ ih'

  have claim2 : ∀ n, n ≤ γ + 1 → (asum β n + c n) % e = 0 := by
    intro n
    induction n with
    | zero => intro _; simp [asum, hc0]
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      have h1 := hβc (n + 1) (by omega) hn
      simp only [Nat.add_sub_cancel] at h1
      have e1 : asum β (n + 1) + c (n + 1) = asum β n + (c (n + 1) + β (n + 1)) := by
        show asum β n + β (n + 1) + c (n + 1) = _; omega
      rw [e1, Nat.add_mod, h1, ← Nat.add_mod]
      exact ih'
  have hB : 2 ^ (asum β (γ + 1)) % m' = 1 % m' := by
    have h := claim2 (γ + 1) (Nat.le_refl _)
    rw [hcg, Nat.add_zero] at h
    have := pow_two_mod_period m' e he (asum β (γ + 1)) 0 (by rw [h]; simp)
    simpa using this
  refine ⟨β, hβb, fun x hx0 hrel => ?_⟩

  have unroll : ∀ n, n ≤ γ + 1 → (m' : Int) ∣
      (2 : Int) ^ (asum β n) * x 0 - (q : Int) ^ n * x n - (fwdSum q β n : Int) := by
    intro n
    induction n with
    | zero => intro _; simp [asum, fwdSum]
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 := hrel (n + 1) (by omega) hn
      simp only [Nat.add_sub_cancel] at h2
      obtain ⟨g1, hg1⟩ := h1
      obtain ⟨g2, hg2⟩ := h2
      have hF : ((fwdSum q β (n + 1) : Nat) : Int) = (2 : Int) ^ (β (n + 1)) * (fwdSum q β n : Int) + (q : Int) ^ n := by
        show (((2 ^ (β (n + 1)) * fwdSum q β n + q ^ n : Nat)) : Int) = _
        simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow]
        rfl
      have hBs : (2 : Int) ^ (asum β (n + 1)) = (2 : Int) ^ (asum β n) * (2 : Int) ^ (β (n + 1)) := by
        show (2 : Int) ^ (asum β n + β (n + 1)) = _
        rw [Int.pow_add]
      have hq1 : (q : Int) ^ (n + 1) = (q : Int) ^ n * (q : Int) := Int.pow_succ _ _
      rw [hF, hBs, hq1]
      have e : (2 : Int) ^ (asum β n) * (2 : Int) ^ (β (n + 1)) * x 0
          - (q : Int) ^ n * (q : Int) * x (n + 1)
          - ((2 : Int) ^ (β (n + 1)) * (fwdSum q β n : Int) + (q : Int) ^ n)
          = (2 : Int) ^ (β (n + 1)) * ((2 : Int) ^ (asum β n) * x 0 - (q : Int) ^ n * x n - (fwdSum q β n : Int))
            - (q : Int) ^ n * ((q : Int) * x (n + 1) + 1 - (2 : Int) ^ (β (n + 1)) * x n) := by int_ring
      rw [e, hg1, hg2]
      exact ⟨(2 : Int) ^ (β (n + 1)) * g1 - (q : Int) ^ n * g2, by int_ring⟩
  have hU := unroll (γ + 1) (Nat.le_refl _)

  have hB' : (m' : Int) ∣ (2 : Int) ^ (asum β (γ + 1)) - 1 := by
    have := nat_mod_to_int_dvd _ _ _ hB
    simpa using this
  have hF1 : (m' : Int) ∣ (fwdSum q β (γ + 1) : Int) - ((wsum q is : Int) + (q : Int) ^ γ) := by
    have h := claim1 (γ + 1) (Nat.le_refl _)
    have hWs : wsumFun q c (γ + 1) = wsum q is + q ^ γ * 2 ^ (c (γ + 1)) := by
      show wsumFun q c γ + q ^ γ * 2 ^ (c (γ + 1)) = _
      rw [hcW]
    rw [hcg, Nat.pow_zero, Nat.one_mul, hWs, hcg, Nat.pow_zero, Nat.mul_one] at h
    have := nat_mod_to_int_dvd _ _ _ h
    simpa [Int.natCast_add, Int.natCast_pow] using this
  have hE : (m' : Int) ∣ (q : Int) ^ (γ + 1) * (ρb - x (γ + 1)) := by
    have e : (q : Int) ^ (γ + 1) * (ρb - x (γ + 1))
        = ((2 : Int) ^ (asum β (γ + 1)) * x 0 - (q : Int) ^ (γ + 1) * x (γ + 1) - (fwdSum q β (γ + 1) : Int))
          - ((2 : Int) ^ (asum β (γ + 1)) - 1) * x 0 - (x 0 - z0)
          + ((fwdSum q β (γ + 1) : Int) - ((wsum q is : Int) + (q : Int) ^ γ))
          + ((wsum q is : Int) - T) := by
      rw [hT]; int_ring
    rw [e]
    refine Int.dvd_add (Int.dvd_add (Int.dvd_sub (Int.dvd_sub hU ?_) hx0) hF1) hwT
    exact Int.dvd_mul_of_dvd_left hB'
  have hcoprime : Nat.Coprime m' (q ^ (γ + 1)) := Nat.Coprime.pow_right (γ + 1) hqm
  have hE' : (m' : Int) ∣ ((q ^ (γ + 1) : Nat) : Int) * (ρb - x (γ + 1)) := by
    rw [Int.natCast_pow]; exact hE
  obtain ⟨g, hg⟩ := int_cancel m' (q ^ (γ + 1)) hm0 hcoprime _ hE'
  exact ⟨-g, by rw [Int.mul_neg]; omega⟩

theorem fixed_point_int (q K : Nat) (hq3 : 3 ≤ q) (hp : Nat.Coprime q 2) :
    ∃ c : Nat, (q : Int) ^ (K + 1) ∣ (2 - (q : Int)) * (c : Int) - 1 := by
  have hpP : q ≤ q ^ (K + 1) := by
    have := Nat.pow_le_pow_right (show 0 < q by omega) (show 1 ≤ K + 1 by omega)
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
  have hm1 : 1 < q ^ (K + 1) := Nat.lt_of_lt_of_le (by omega) hpP
  obtain ⟨k, w, hkw⟩ := nat_bez n (q ^ (K + 1)) hm1 (Nat.Coprime.symm (Nat.Coprime.pow_left (K + 1) hgp))
  refine ⟨k, w - k, ?_⟩
  have hn' : (n : Int) + (q : Int) = (q : Int) ^ (K + 1) + 2 := by exact_mod_cast hnp
  have hkw' : (n : Int) * (k : Int) = (q : Int) ^ (K + 1) * (w : Int) + 1 := by exact_mod_cast hkw
  have h2q : (2 : Int) - (q : Int) = (n : Int) - (q : Int) ^ (K + 1) := by omega
  rw [h2q, Int.sub_mul, Int.mul_sub]
  omega

theorem exists_nu (q : Nat) [NonWieferich q] (K d u : Nat) (hd : 2 ^ d = 1 + q * u)
    (hu : Nat.Coprime q u) (t i : Nat) (hi : t % q = 2 ^ i % q) (c : Nat)
    (hc : (q : Int) ^ (K + 1) ∣ (2 - (q : Int)) * (c : Int) - 1) :
    ∃ ν : Nat, ν < d * q ^ K ∧ (q : Int) ^ (K + 1) ∣ (2 : Int) ^ ν * (t : Int) - (c : Int) := by
  have hodd := NonWieferich.odd (q := q)
  have hq3 := NonWieferich.three_le (q := q)
  have hP1 : 1 % q ^ (K + 1) = 1 := one_mod_P q K
  have hqpos : 0 < q := by omega
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; rw [Nat.pow_zero] at hd
      have : q * u = 0 := by omega
      rcases Nat.mul_eq_zero.1 this with h1 | h1
      · omega
      · subst h1; simp [Nat.Coprime] at hu; omega
    · exact h
  have hcq : (2 * c) % q = 1 := by
    have hdvd : (q : Int) ∣ (2 - (q : Int)) * (c : Int) - 1 :=
      Int.dvd_trans ⟨(q : Int) ^ K, by rw [Int.pow_succ, Int.mul_comm]⟩ hc
    obtain ⟨g, hg⟩ := hdvd
    have e0 : (2 - (q : Int)) * (c : Int) - 1 = 2 * (c : Int) - 1 - (q : Int) * (c : Int) := by int_ring
    rw [e0] at hg
    have h1 : (((2 * c : Nat)) : Int) = 1 + (q : Int) * ((c : Int) + g) := by
      simp only [Int.natCast_mul]
      show (2 : Int) * (c : Int) = _
      rw [Int.mul_add]; omega
    have h2 := Int.natCast_emod (2 * c) q
    have h3 : (((2 * c : Nat)) : Int) % (q : Int) = 1 := by
      rw [h1, Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt (by omega) (by omega)
    omega
  have hcpow : c % q = 2 ^ (d - 1) % q := by
    have e2 : 2 ^ d % q = 1 := by
      rw [hd, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)
    have e3 : c * 2 ^ d = (2 * c) * 2 ^ (d - 1) := by
      rw [show d = (d - 1) + 1 by omega, Nat.pow_succ]
      simp only [Nat.add_sub_cancel]; nat_ring
    have := congrArg (· % q) e3
    rw [Nat.mul_mod, e2, Nat.mul_one, Nat.mod_mod, Nat.mul_mod (2 * c), hcq, Nat.one_mul,
      Nat.mod_mod] at this
    exact this
  have hMt := target_inPowTwo q hi K
  have hMc := target_inPowTwo q hcpow K
  obtain ⟨j, hj⟩ := inPowTwo_ratio q hMt hMc
  have hT : 2 ^ (d * q ^ K) % q ^ (K + 1) = 1 % q ^ (K + 1) := by
    rw [Nat.pow_mul, hd, hP1]
    simpa [Nat.pow_one, Nat.add_comm] using (order_iff hodd hq3 (Nat.le_refl 1) hu K (q ^ K)).2 (Nat.dvd_refl _)
  have hTpos : 0 < d * q ^ K := Nat.mul_pos hd0 (powp_pos q K)
  refine ⟨j % (d * q ^ K), Nat.mod_lt _ hTpos, ?_⟩
  have hν : 2 ^ (j % (d * q ^ K)) % q ^ (K + 1) = 2 ^ j % q ^ (K + 1) :=
    pow_two_mod_period (q ^ (K + 1)) (d * q ^ K) hT _ _ (by rw [Nat.mod_mod])
  have hfin : (2 ^ (j % (d * q ^ K)) * t) % q ^ (K + 1) = c % q ^ (K + 1) := by
    rw [mul_mod_cong _ _ _ _ hν]; exact hj
  have h := nat_mod_to_int_dvd _ _ _ hfin
  simp only [Int.natCast_pow, Int.natCast_mul] at h
  exact h

theorem P_struct (q : Nat) [NonWieferich q] (K d u e eQ e' : Nat) (hd : 2 ^ d = 1 + q * u)
    (hu : Nat.Coprime q u) (he0 : 0 < e) (hee : e = eQ * e') (hKe : eQ ∣ q ^ K)
    (he'q : Nat.Coprime e' q) :
    ∃ uP : Nat, 2 ^ (Nat.lcm (d * q ^ K) e) = 1 + q ^ (K + 1) * uP ∧ Nat.Coprime q uP := by
  have hodd := NonWieferich.odd (q := q)
  obtain ⟨uK, huK, hexp⟩ := lift_exponent hodd (Nat.le_refl 1) hu K
  have h2a : 2 ^ (d * q ^ K) = 1 + q ^ (K + 1) * uK := by
    rw [Nat.pow_mul, hd]; simpa [Nat.pow_one, Nat.add_comm] using hexp
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd (d * q ^ K) e := ⟨_, rfl⟩
  have hge : g ∣ e := by rw [hg]; exact Nat.gcd_dvd_right _ _
  obtain ⟨f, hf⟩ : ∃ f, f = e / g := ⟨_, rfl⟩
  have hlcm : Nat.lcm (d * q ^ K) e = d * q ^ K * f := by
    show d * q ^ K * e / Nat.gcd (d * q ^ K) e = _
    rw [← hg, hf]; exact Nat.mul_div_assoc _ hge
  have hegf : e = g * f := by rw [hf]; exact (Nat.mul_div_cancel' hge).symm
  have heQa : eQ ∣ d * q ^ K := Nat.dvd_trans hKe (Nat.dvd_mul_left _ _)
  have heQe : eQ ∣ e := ⟨e', hee⟩
  have heQg : eQ ∣ g := by rw [hg]; exact Nat.dvd_gcd heQa heQe
  obtain ⟨g', hg'⟩ := heQg
  have heQ0 : 0 < eQ := by
    rcases Nat.eq_zero_or_pos eQ with h | h
    · rw [h, Nat.zero_mul] at hee; omega
    · exact h
  have he' : e' = f * g' := by
    have h1 : eQ * e' = eQ * (g' * f) := by
      rw [← hee, hegf, hg']; (first | nat_ring | int_ring)
    rw [Nat.eq_of_mul_eq_mul_left heQ0 h1, Nat.mul_comm]
  have hfq : Nat.Coprime f q := Nat.Coprime.coprime_dvd_left ⟨g', he'⟩ he'q
  obtain ⟨z, hz⟩ := binom_quadratic (q ^ (K + 1) * uK) f
  refine ⟨f * uK + q * (q ^ K * (uK ^ 2 * z)), ?_, ?_⟩
  · rw [hlcm, Nat.pow_mul, h2a, hz]
    have e1 : q ^ (K + 1) = q * q ^ K := by rw [Nat.pow_succ, Nat.mul_comm]
    simp only [Nat.pow_two]
    generalize q ^ K = A at e1 ⊢
    rw [e1]; (first | nat_ring | int_ring)
  · rw [Nat.Coprime, Nat.gcd_add_mul_left_right]
    exact Nat.Coprime.mul_right hfq.symm huK

theorem ipow2_ge_one (k : Nat) : (1 : Int) ≤ (2 : Int) ^ k := by
  induction k with
  | zero => rw [Int.pow_zero]; exact Int.le_refl _
  | succ k ih => rw [Int.pow_succ]; omega

theorem chain_pos (q : Nat) (hq : 1 ≤ q) (P : Nat) (y0 : Int) (b J : Nat → Nat) (n : Nat)
    (hI : Integral (q : Int) P y0 b J n) (hy0 : 1 ≤ y0) (hb : ∀ l, 1 ≤ l → l ≤ n → 1 ≤ b l) :
    ∀ i, i ≤ n → 1 ≤ chain (q : Int) P y0 b J i := by
  intro i
  induction i with
  | zero => intro _; exact hy0
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    have rel := chain_rel hI i (by omega)
    have hb1 := hb (i + 1) (by omega) hi
    obtain ⟨b', hb'⟩ : ∃ b', b (i + 1) = b' + 1 := ⟨b (i + 1) - 1, by omega⟩
    have h2b : (2 : Int) ≤ (2 : Int) ^ (b (i + 1)) := by
      rw [hb', Int.pow_succ]; have := ipow2_ge_one b'; omega
    have hJP := ipow2_ge_one (J (i + 1) * P)
    generalize (2 : Int) ^ (b (i + 1)) = A at *
    generalize (2 : Int) ^ (J (i + 1) * P) = B at *
    generalize chain (q : Int) P y0 b J i = y at *
    generalize chain (q : Int) P y0 b J (i + 1) = c1 at *
    have hAB : A ≤ A * B := by
      have := Int.mul_le_mul_of_nonneg_left hJP (show 0 ≤ A by omega)
      rw [Int.mul_one] at this; exact this
    have hABy : A * B ≤ A * B * y := by
      have := Int.mul_le_mul_of_nonneg_left ih' (show 0 ≤ A * B by omega)
      rw [Int.mul_one] at this; exact this
    have hq' : (0 : Int) ≤ (q : Int) := by omega
    match Int.lt_or_le c1 1 with
    | Or.inr hle => exact (by omega : 1 ≤ c1)
    | Or.inl hc =>
    have hc' : c1 ≤ 0 := by omega
    have := Int.mul_le_mul_of_nonneg_left hc' hq'
    rw [Int.mul_zero] at this
    omega

theorem chain_size (q : Nat) (hq : 1 ≤ q) (P : Nat) (y0 : Int) (b J : Nat → Nat) (n : Nat)
    (hI : Integral (q : Int) P y0 b J n) (hy0 : 1 ≤ y0) (hb : ∀ l, 1 ≤ l → l ≤ n → 1 ≤ b l) :
    ∀ i, i ≤ n → chain (q : Int) P y0 b J i ≤ (2 : Int) ^ (asum (fun l => b l + J l * P) i) * y0 := by
  intro i
  induction i with
  | zero => intro _; show y0 ≤ (2 : Int) ^ 0 * y0; rw [Int.pow_zero, Int.one_mul]; exact Int.le_refl _
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    have rel := chain_rel hI i (by omega)
    have hAs : (2 : Int) ^ (asum (fun l => b l + J l * P) (i + 1))
        = (2 : Int) ^ (asum (fun l => b l + J l * P) i) * ((2 : Int) ^ (b (i + 1)) * (2 : Int) ^ (J (i + 1) * P)) := by
      show (2 : Int) ^ (asum (fun l => b l + J l * P) i + (b (i + 1) + J (i + 1) * P)) = _
      rw [Int.pow_add, Int.pow_add]
    rw [hAs]
    have hA1 := ipow2_ge_one (b (i + 1))
    have hB1 := ipow2_ge_one (J (i + 1) * P)
    have hC1 := ipow2_ge_one (asum (fun l => b l + J l * P) i)
    have hc1pos := chain_pos q hq P y0 b J n hI hy0 hb (i + 1) hi
    generalize (2 : Int) ^ (b (i + 1)) = A at *
    generalize (2 : Int) ^ (J (i + 1) * P) = B at *
    generalize (2 : Int) ^ (asum (fun l => b l + J l * P) i) = C at *
    generalize chain (q : Int) P y0 b J i = y at *
    generalize chain (q : Int) P y0 b J (i + 1) = c1 at *
    have hq' : (0 : Int) ≤ (q : Int) := by omega
    have h1 : c1 ≤ (q : Int) * c1 := by
      have := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ (q : Int) by omega)
        (show 0 ≤ c1 by omega)
      rw [Int.one_mul] at this; exact this
    have hAB : 0 ≤ A * B := Int.mul_nonneg (by omega) (by omega)
    have h2 : A * B * y ≤ A * B * (C * y0) := Int.mul_le_mul_of_nonneg_left ih' hAB
    have e : A * B * (C * y0) = C * (A * B) * y0 := by int_ring
    rw [← e]
    omega

theorem chain_reaches (q : Nat) [NonWieferich q] (P : Nat) (y0 : Int) (b J : Nat → Nat) (n : Nat)
    (hI : Integral (q : Int) P y0 b J n) (hy0 : 1 ≤ y0) (hb : ∀ l, 1 ≤ l → l ≤ n → 1 ≤ b l)
    (Y0 : Nat) (hY0 : (Y0 : Int) = y0) :
    ∀ i, i ≤ n → ∃ yi : Nat, (yi : Int) = chain (q : Int) P y0 b J i ∧ Reaches q yi Y0 := by
  have hq1 : 1 ≤ q := by have := NonWieferich.three_le (q := q); omega
  intro i
  induction i with
  | zero => intro _; exact ⟨Y0, hY0, ⟨0, rfl⟩⟩
  | succ i ih =>
    intro hi
    obtain ⟨yi, hyi, hr⟩ := ih (by omega)
    have rel := chain_rel hI i (by omega)
    have hpos := chain_pos q hq1 P y0 b J n hI hy0 hb (i + 1) hi
    obtain ⟨yN, hyN⟩ : ∃ y : Nat, (y : Int) = chain (q : Int) P y0 b J (i + 1) :=
      ⟨(chain (q : Int) P y0 b J (i + 1)).toNat, Int.toNat_of_nonneg (by omega)⟩
    refine ⟨yN, hyN, ?_⟩
    have hb1 := hb (i + 1) (by omega) hi
    have hnat : q * yN + 1 = 2 ^ (b (i + 1) + J (i + 1) * P) * yi := by
      apply Int.ofNat_inj.1
      simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow, Int.natCast_one]
      rw [hyN, hyi, Int.pow_add]
      show (q : Int) * chain (q : Int) P y0 b J (i + 1) + 1 = _
      exact rel
    exact reaches_trans q (backstep_reaches (q := q) yN yi _ (by omega) hnat) hr

theorem asum_bound (f : Nat → Nat) (X : Nat) :
    ∀ n, (∀ l, 1 ≤ l → l ≤ n → f l ≤ X) → asum f (n + 1) ≤ n * X + f (n + 1)
  | 0, _ => by show asum f 0 + f (0 + 1) ≤ 0 * X + f (0 + 1); simp [asum]
  | n + 1, H => by
    have ih := asum_bound f X n (fun l h1 h2 => H l h1 (by omega))
    have hn := H (n + 1) (by omega) (Nat.le_refl _)
    show asum f (n + 1) + f (n + 1 + 1) ≤ (n + 1) * X + f (n + 1 + 1)
    rw [Nat.succ_mul]; omega

theorem setup_of (q K P uPn : Nat) [NonWieferich q] (c y0 : Int) (b : Nat → Nat)
    (hP : (2 : Int) ^ P = 1 + (q : Int) ^ (K + 1) * (uPn : Int))
    (huP : Nat.Coprime q uPn)
    (hc : (q : Int) ^ (K + 1) ∣ (2 - (q : Int)) * c - 1)
    (hy0 : (q : Int) ^ (K + 1) ∣ y0 - c)
    (hb1 : ∀ i, 1 ≤ i → i ≤ K + 1 → b i = 1) :
    Setup (q : Int) K P (uPn : Int) b y0 c := by
  have hq3 := NonWieferich.three_le (q := q)
  have hodd := NonWieferich.odd (q := q)
  have hp0 : (q : Int) ≠ 0 := by omega
  refine ⟨hp0, hP, ?_, ?_, hc, hy0, hb1⟩
  · refine ⟨((q + 1) / 2 : Nat), ⟨1, ?_⟩⟩
    have h2 : 2 * ((q + 1) / 2) = q + 1 := by omega
    have h3 : (2 : Int) * (((q + 1) / 2 : Nat) : Int) = (q : Int) + 1 := by
      have := congrArg (fun n : Nat => (n : Int)) h2
      simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one] at this
      exact this
    omega
  · obtain ⟨k, w, hkw⟩ := nat_bez uPn q (by omega) (Nat.Coprime.symm huP)
    refine ⟨(k : Int), ⟨(w : Int), ?_⟩⟩
    have h4 : (uPn : Int) * (k : Int) = (q : Int) * (w : Int) + 1 := by
      have := congrArg (fun n : Nat => (n : Int)) hkw
      simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one] at this
      exact this
    omega

theorem step_lower (q : Nat) [NonWieferich q] (P : Nat) (y0 : Int) (b J : Nat → Nat) (n : Nat)
    (hI : Integral (q : Int) P y0 b J n) (hy0 : 1 ≤ y0) (hb : ∀ l, 1 ≤ l → l ≤ n → 1 ≤ b l)
    (i : Nat) (hi : i < n) :
    (2 : Int) ^ (b (i + 1) + J (i + 1) * P) ≤ (q : Int) * chain (q : Int) P y0 b J (i + 1) + 1 := by
  have rel := chain_rel hI i hi
  have hprev := chain_pos q (by have := NonWieferich.three_le (q := q); omega) P y0 b J n hI hy0 hb i (by omega)
  have e : (2 : Int) ^ (b (i + 1) + J (i + 1) * P)
      = (2 : Int) ^ (b (i + 1)) * (2 : Int) ^ (J (i + 1) * P) := Int.pow_add _ _ _
  rw [e]
  have hA : (0 : Int) ≤ (2 : Int) ^ (b (i + 1)) * (2 : Int) ^ (J (i + 1) * P) := by
    have := ipow2_ge_one (b (i + 1)); have := ipow2_ge_one (J (i + 1) * P)
    exact Int.mul_nonneg (by omega) (by omega)
  have hmul : (2 : Int) ^ (b (i + 1)) * (2 : Int) ^ (J (i + 1) * P) ≤
      (2 : Int) ^ (b (i + 1)) * (2 : Int) ^ (J (i + 1) * P) * chain (q : Int) P y0 b J i := by
    have := Int.mul_le_mul_of_nonneg_left hprev hA
    rw [Int.mul_one] at this; exact this
  have hq : (0 : Int) ≤ (q : Int) := by omega
  omega

theorem ipow2_mono (a c : Nat) (h : a ≤ c) : (2 : Int) ^ a ≤ (2 : Int) ^ c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Int.pow_add]
  have h1 := ipow2_ge_one d
  have hA : (0 : Int) ≤ (2 : Int) ^ a := by have := ipow2_ge_one a; omega
  have := Int.mul_le_mul_of_nonneg_left h1 hA
  rw [Int.mul_one] at this
  exact this

theorem amin_exists (X : Nat) (hX : 1 ≤ X) : ∃ a : Nat, X < 2 ^ a ∧ 2 ^ a ≤ 2 * X := by
  refine ⟨Nat.log2 X + 1, Nat.lt_log2_self, ?_⟩
  have hX0 : X ≠ 0 := by omega
  have hlt : ¬ (X < 2 ^ Nat.log2 X) := by
    intro h
    have := (Nat.log2_lt hX0).2 h
    omega
  have hle : 2 ^ Nat.log2 X ≤ X := Nat.le_of_not_lt hlt
  rw [Nat.pow_succ]
  omega

theorem size_bound (q : Nat) [NonWieferich q] (P ν t s qP M D : Nat) (b J : Nat → Nat)
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hν : ν ≤ D)
    (hI : Integral (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J s)
    (hb : ∀ l, 1 ≤ l → l ≤ s → 1 ≤ b l)
    (hsmall : ∀ l, 1 ≤ l → l + 1 ≤ s → b l + J l * P ≤ qP)
    (hlast : b s + J s * P ≤ M) :
    chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J s
      ≤ (2 : Int) ^ (D + (s - 1) * qP + M) * (t : Int) := by
  have hq1 : 1 ≤ q := by have := NonWieferich.three_le (q := q); omega
  have hy0 : 1 ≤ (2 : Int) ^ ν * (t : Int) := by
    have h1 := ipow2_ge_one ν
    have := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ (t : Int) by omega)
      (show (0 : Int) ≤ (2 : Int) ^ ν by omega)
    rw [Int.mul_one] at this; omega
  have hc := chain_size q hq1 P ((2 : Int) ^ ν * (t : Int)) b J s hI hy0 hb s (Nat.le_refl s)
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hab := asum_bound (fun l => b l + J l * P) qP s' (fun l h1 h2 => hsmall l h1 (by omega))
  have hs' : s' + 1 - 1 = s' := by omega
  have hA : (2 : Int) ^ (asum (fun l => b l + J l * P) (s' + 1))
      ≤ (2 : Int) ^ (s' * qP + M) := ipow2_mono _ _ (by omega)
  have hB : (2 : Int) ^ ν ≤ (2 : Int) ^ D := ipow2_mono _ _ hν
  have hfin : chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J (s' + 1)
      ≤ (2 : Int) ^ (s' * qP + M) * ((2 : Int) ^ ν * (t : Int)) := by
    have hnn : (0 : Int) ≤ (2 : Int) ^ ν * (t : Int) :=
      Int.mul_nonneg (by have := ipow2_ge_one ν; omega) (by omega)
    have h := Int.mul_le_mul_of_nonneg_right hA hnn
    exact Int.le_trans hc h
  have hfin2 : (2 : Int) ^ (s' * qP + M) * ((2 : Int) ^ ν * (t : Int))
      ≤ (2 : Int) ^ (D + (s' + 1 - 1) * qP + M) * (t : Int) := by
    rw [hs']
    have eD : (2 : Int) ^ (D + s' * qP + M) = (2 : Int) ^ (s' * qP + M) * (2 : Int) ^ D := by
      rw [show D + s' * qP + M = (s' * qP + M) + D by omega, Int.pow_add]
    rw [eD]
    have e1 : (2 : Int) ^ (s' * qP + M) * (2 : Int) ^ ν * (t : Int)
        ≤ (2 : Int) ^ (s' * qP + M) * (2 : Int) ^ D * (t : Int) := by
      have hpos : (0 : Int) ≤ (2 : Int) ^ (s' * qP + M) := by
        have := ipow2_ge_one (s' * qP + M); omega
      have := Int.mul_le_mul_of_nonneg_left hB hpos
      have htn : (0 : Int) ≤ (t : Int) := by omega
      have h3 := Int.mul_le_mul_of_nonneg_right this htn
      exact h3
    have e2 : (2 : Int) ^ (s' * qP + M) * ((2 : Int) ^ ν * (t : Int))
        = (2 : Int) ^ (s' * qP + M) * (2 : Int) ^ ν * (t : Int) := by int_ring
    rw [e2]; exact e1
  exact Int.le_trans hfin hfin2

theorem chain_rel_mod (m : Int) (q : Nat) (P : Nat) (y0 : Int) (b J : Nat → Nat) (n : Nat)
    (hI : Integral (q : Int) P y0 b J n) (hP : m ∣ (2 : Int) ^ P - 1) :
    ∀ i, i < n → m ∣ (q : Int) * chain (q : Int) P y0 b J (i + 1) + 1
      - (2 : Int) ^ (b (i + 1)) * chain (q : Int) P y0 b J i := by
  intro i hi
  have rel := chain_rel hI i hi
  have hJ := pow_mod_one_int m P (J (i + 1)) hP
  obtain ⟨g, hg⟩ := hJ
  refine ⟨(2 : Int) ^ (b (i + 1)) * chain (q : Int) P y0 b J i * g, ?_⟩
  have hJ' : (2 : Int) ^ (J (i + 1) * P) = 1 + m * g := by omega
  have key : (q : Int) * chain (q : Int) P y0 b J (i + 1) + 1
      - (2 : Int) ^ (b (i + 1)) * chain (q : Int) P y0 b J i
      = (2 : Int) ^ (b (i + 1)) * chain (q : Int) P y0 b J i * (2 ^ (J (i + 1) * P) - 1) := by
    rw [rel]; int_ring
  rw [key, hJ']
  int_ring

theorem two_mul_succ_mul (a b : Nat) : 2 * (a + 1) * b = 2 * (a * b) + 2 * b := by
  rw [Nat.mul_assoc, Nat.add_mul, Nat.one_mul, Nat.mul_add]

theorem kappa_le (q : Nat) (hq : 3 ≤ q) : ∀ u : List Nat, (∀ e ∈ u, e ≤ 1) →
    kappa q u + q ^ ones u ≤ 2 ^ u.length * q ^ ones u
  | [], _ => by simp [kappa, ones]
  | e :: u, hu => by
    have ih := kappa_le q hq u (fun d hd => hu d (by simp [hd]))
    have he : e = 0 ∨ e = 1 := by
      have := hu e (by simp); omega
    simp only [kappa, ones, List.length_cons]
    have hT : 1 ≤ 2 ^ u.length := Nat.one_le_two_pow
    rcases he with rfl | rfl
    · rw [show (2 : Nat) ^ (u.length + 1) = 2 * 2 ^ u.length from Nat.pow_succ']
      obtain ⟨t1, ht1⟩ : ∃ t1, 2 ^ u.length = t1 + 1 := ⟨2 ^ u.length - 1, by omega⟩
      rw [ht1] at ih ⊢
      try simp only [Nat.add_zero]
      rw [two_mul_succ_mul, Nat.mul_zero, Nat.zero_add]
      have e2 : (t1 + 1) * q ^ ones u = t1 * q ^ ones u + q ^ ones u := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [e2] at ih
      omega
    · rw [show q ^ (ones u + 1) = q * q ^ ones u from Nat.pow_succ',
        show (2 : Nat) ^ (u.length + 1) = 2 * 2 ^ u.length from Nat.pow_succ']
      obtain ⟨t1, ht1⟩ : ∃ t1, 2 ^ u.length = t1 + 1 := ⟨2 ^ u.length - 1, by omega⟩
      rw [ht1] at ih ⊢
      have hY : q ^ ones u ≤ q * q ^ ones u := Nat.le_mul_of_pos_left _ (by omega)
      have hty : t1 * q ^ ones u ≤ t1 * (q * q ^ ones u) := Nat.mul_le_mul_left t1 hY
      have e2 : (t1 + 1) * q ^ ones u = t1 * q ^ ones u + q ^ ones u := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [e2] at ih
      rw [two_mul_succ_mul, Nat.mul_one]
      omega

theorem ones_le_length : ∀ u : List Nat, (∀ e ∈ u, e ≤ 1) → ones u ≤ u.length
  | [], _ => by simp [ones]
  | e :: u, hu => by
    have ih := ones_le_length u (fun d hd => hu d (by simp [hd]))
    have he : e ≤ 1 := hu e (by simp)
    simp only [ones, List.length_cons]
    omega

theorem theta_bound (q : Nat) (hq : 3 ≤ q) (m rb B ρ : Nat) (u : List Nat) (hu : ∀ e ∈ u, e ≤ 1)
    (hrb : rb < m)
    (hρ : 2 ^ u.length * ρ = q ^ ones u * rb + kappa q u) :
    ρ + q ^ ones u * (B + 1) ≤ q ^ u.length * ((m + 1) * (B + 1)) := by
  have hO := kappa_le q hq u hu
  have hA : 1 ≤ 2 ^ u.length := Nat.one_le_two_pow
  have hX : 1 ≤ q ^ ones u := Nat.one_le_pow _ _ (by omega)

  have hstep1 : 2 ^ u.length * ρ ≤ 2 ^ u.length * (q ^ ones u * (rb + 1)) := by
    have e1 : 2 ^ u.length * (q ^ ones u * (rb + 1))
        = 2 ^ u.length * (q ^ ones u * rb) + 2 ^ u.length * q ^ ones u := by
      simp only [Nat.mul_add, Nat.mul_one]
    have hXr : q ^ ones u * rb ≤ 2 ^ u.length * (q ^ ones u * rb) :=
      Nat.le_mul_of_pos_left _ (by omega)
    rw [e1]
    rw [hρ]
    omega
  have hrho : ρ ≤ q ^ ones u * (rb + 1) := Nat.le_of_mul_le_mul_left hstep1 (by omega)

  have hmB : rb + 1 ≤ m := hrb
  have hK : (rb + 1 + B + 1) ≤ (m + 1) * (B + 1) := by
    have e3 : (m + 1) * (B + 1) = m * B + m + B + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    rw [e3]; omega

  have hsum : ρ + q ^ ones u * (B + 1) ≤ q ^ ones u * ((m + 1) * (B + 1)) := by
    have e4 : q ^ ones u * ((m + 1) * (B + 1))
        = q ^ ones u * (rb + 1 + B + 1) + q ^ ones u * ((m + 1) * (B + 1) - (rb + 1 + B + 1)) := by
      rw [← Nat.mul_add]; congr 1; omega
    have hm1 : q ^ ones u * (rb + 1) + q ^ ones u * (B + 1)
        = q ^ ones u * (rb + 1 + B + 1) := by
      rw [← Nat.mul_add]; congr 1
    have := Nat.add_le_add hrho (Nat.le_refl (q ^ ones u * (B + 1)))
    rw [hm1] at this
    rw [e4]; omega
  have hpow : q ^ ones u ≤ q ^ u.length := Nat.pow_le_pow_right (by omega) (ones_le_length u hu)
  have hfin : q ^ ones u * ((m + 1) * (B + 1)) ≤ q ^ u.length * ((m + 1) * (B + 1)) :=
    Nat.mul_le_mul_right _ hpow
  omega

theorem class_indep_of_shifts (m q P : Nat) (hm0 : 0 < m) (hcop : Nat.Coprime m q)
    (hP : (m : Int) ∣ (2 : Int) ^ P - 1) (y0 y0' : Int) (b b' J J' : Nat → Nat) (n : Nat)
    (hI : Integral (q : Int) P y0 b J n) (hI' : Integral (q : Int) P y0' b' J' n)
    (hbb : ∀ i, 1 ≤ i → i ≤ n → b i = b' i)
    (h0 : (m : Int) ∣ y0 - y0') :
    ∀ i, i ≤ n → (m : Int) ∣ chain (q : Int) P y0 b J i - chain (q : Int) P y0' b' J' i := by
  intro i
  induction i with
  | zero => intro _; exact h0
  | succ i ih =>
    intro hi
    obtain ⟨k, hk⟩ := ih (by omega)
    obtain ⟨g1, hg1⟩ := chain_rel_mod (m : Int) q P y0 b J n hI hP i (by omega)
    obtain ⟨g2, hg2⟩ := chain_rel_mod (m : Int) q P y0' b' J' n hI' hP i (by omega)
    have hbe : b (i + 1) = b' (i + 1) := hbb (i + 1) (by omega) hi
    rw [hbe] at hg1
    have hid : (q : Int) * (chain (q : Int) P y0 b J (i + 1) - chain (q : Int) P y0' b' J' (i + 1))
        = ((q : Int) * chain (q : Int) P y0 b J (i + 1) + 1 - (2 : Int) ^ (b' (i + 1)) * chain (q : Int) P y0 b J i)
          - ((q : Int) * chain (q : Int) P y0' b' J' (i + 1) + 1 - (2 : Int) ^ (b' (i + 1)) * chain (q : Int) P y0' b' J' i)
          + (2 : Int) ^ (b' (i + 1)) * (chain (q : Int) P y0 b J i - chain (q : Int) P y0' b' J' i) := by
      int_ring
    rw [hg1, hg2, hk] at hid
    have hq : (m : Int) ∣ (q : Int) * (chain (q : Int) P y0 b J (i + 1) - chain (q : Int) P y0' b' J' (i + 1)) := by
      refine ⟨g1 - g2 + (2 : Int) ^ (b' (i + 1)) * k, ?_⟩
      rw [hid]; int_ring
    exact int_cancel m q hm0 hcop _ hq

theorem least_in_class (P Lam b j0 amin : Nat) (hP : 0 < P) (hL : 0 < Lam) (hbP : b ≤ P)
    (ha : 1 ≤ amin) :
    ∃ j : Nat, j % Lam = j0 % Lam ∧ amin ≤ b + j * P ∧ b + j * P < amin + P * Lam := by
  obtain ⟨E, hE1, hE2, hE3⟩ := exists_in_class (b + j0 * P) amin (P * Lam) (Nat.mul_pos hP hL)
  have hbE : b ≤ E := by
    rcases Nat.lt_or_ge E b with hlt | hge
    · exfalso
      have h1 : E % P = (b + j0 * P) % P := by
        have h2 : E % P = (E % (P * Lam)) % P := (Nat.mod_mod_of_dvd E (Nat.dvd_mul_right P Lam)).symm
        rw [h2, hE3, Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right P Lam)]
      have hb' : (b + j0 * P) % P = b % P := by
        rw [Nat.add_mod, Nat.mul_mod_left, Nat.add_zero, Nat.mod_mod]
      rw [hb'] at h1
      have hEP : E % P = E := Nat.mod_eq_of_lt (by omega)
      rw [hEP] at h1
      rcases Nat.lt_or_ge b P with hbl | hbe
      · rw [Nat.mod_eq_of_lt hbl] at h1; omega
      · have hbPe : b = P := by omega
        rw [hbPe, Nat.mod_self] at h1; omega
    · exact hge
  have hdvd : P ∣ E - b := by
    have e1 : E % P = (b + j0 * P) % P := by
      have h2 : E % P = (E % (P * Lam)) % P := (Nat.mod_mod_of_dvd E (Nat.dvd_mul_right P Lam)).symm
      rw [h2, hE3, Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right P Lam)]
    have hb' : (b + j0 * P) % P = b % P := by
      rw [Nat.add_mod, Nat.mul_mod_left, Nat.add_zero, Nat.mod_mod]
    have hsub := Nat.sub_mod_eq_zero_of_mod_eq (e1.trans hb')
    exact Nat.dvd_of_mod_eq_zero hsub
  obtain ⟨j, hj⟩ := hdvd
  have hj' : E - b = j * P := by rw [hj, Nat.mul_comm]
  have hEj : E = b + j * P := by omega
  refine ⟨j, ?_, ?_, ?_⟩
  · have hI := nat_mod_to_int_dvd E (b + j0 * P) (P * Lam) hE3
    have hPi : (P : Int) ≠ 0 := by omega
    have e2 : (E : Int) - ((b + j0 * P : Nat) : Int) = (P : Int) * ((j : Int) - (j0 : Int)) := by
      rw [hEj]; simp only [Int.natCast_add, Int.natCast_mul]; int_ring
    rw [e2, Int.natCast_mul] at hI
    obtain ⟨k, hk⟩ := hI
    have hk2 : (j : Int) - (j0 : Int) = (Lam : Int) * k := by
      apply Int.eq_of_mul_eq_mul_left hPi
      rw [hk]; int_ring
    have hmod : (j : Int) % (Lam : Int) = (j0 : Int) % (Lam : Int) := by
      apply Int.emod_eq_emod_iff_emod_sub_eq_zero.2
      rw [hk2]; exact Int.mul_emod_right _ _
    have hjn : ((j % Lam : Nat) : Int) = ((j0 % Lam : Nat) : Int) := by
      rw [Int.natCast_emod, Int.natCast_emod]; exact hmod
    exact Int.natCast_inj.1 hjn
  · omega
  · omega

theorem delay_line_witness (q K P uPn τ ν t N B amin : Nat) [NonWieferich q] (ρ c : Int)
    (hP : (2 : Int) ^ P = 1 + (q : Int) ^ (K + 1) * (uPn : Int))
    (huP : Nat.Coprime q uPn)
    (hc : (q : Int) ^ (K + 1) ∣ (2 - (q : Int)) * c - 1)
    (hνc : (q : Int) ^ (K + 1) ∣ (2 : Int) ^ ν * (t : Int) - c)
    (ht1 : 1 ≤ t) (hN : K ≤ N)
    (b : Nat → Nat) (hb1 : ∀ i, 1 ≤ i → i ≤ K + 1 → b i = 1)
    (hbpos : ∀ i, 1 ≤ i → i ≤ K + 1 + τ → 1 ≤ b i)
    (E0 : Nat) (hbE : ∀ i, 1 ≤ i → i ≤ K + 1 + τ → b i ≤ E0) (hE0P : E0 ≤ P)
    (hPpos : 0 < P) (hB : q * (B + 1) + 1 ≤ 2 ^ amin) :
    ∃ J : Nat → Nat, Integral (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J (K + 1 + τ) ∧
      ∃ y : Nat, Reaches q y t ∧ B < y ∧
      (q : Int) ^ N ∣ chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J (K + 1 + τ) - ρ ∧
      (y : Int) = chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J (K + 1 + τ) ∧
      chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J (K + 1 + τ)
        ≤ (2 : Int) ^ (ν + (K + τ) * ((q - 1) * P + E0) + (amin + P * q ^ (N - K))) * (t : Int) := by
  have hodd := NonWieferich.odd (q := q)
  have hq3 := NonWieferich.three_le (q := q)
  have hq0 : 0 < q := by omega
  have hcop : Nat.Coprime q uPn := huP
  have S := setup_of q K P uPn c ((2 : Int) ^ ν * (t : Int)) b hP huP hc hνc hb1
  obtain ⟨f, hfb, hf⟩ := choose_shifts (p := (q : Int)) q hq0 rfl S τ ρ
  obtain ⟨j0, hj0, hw⟩ := wide_step q hq3 hodd hcop rfl S τ ρ N hN f hf
  have hΛ : 0 < q ^ (N - K) := Nat.pow_pos (by omega)
  have ha1 : 1 ≤ amin := by
    rcases Nat.eq_zero_or_pos amin with h | h
    · subst h
      have : 0 < q * (B + 1) := Nat.mul_pos hq0 (Nat.succ_pos B)
      simp at hB; omega
    · exact h
  obtain ⟨j, hjmod, hjlo, hjhi⟩ := least_in_class P (q ^ (N - K)) (b (K + 1 + τ)) j0 amin hPpos hΛ
    (Nat.le_trans (hbE (K + 1 + τ) (by omega) (Nat.le_refl _)) hE0P) ha1
  have hJmod : j % q ^ (N - K) = j0 := by rw [hjmod]; exact Nat.mod_eq_of_lt hj0
  obtain ⟨J0, hJ0⟩ : ∃ J0 : Nat → Nat, J0 = fun l => if l ≤ K + τ then f l else if l = K + 1 + τ then j else 0 :=
    ⟨_, rfl⟩
  have hJa : ∀ l, 1 ≤ l → l ≤ K + τ → J0 l = f l := by
    intro l h1 h2; rw [hJ0]; simp [h2]
  have hJs : J0 (K + 1 + τ) = j := by
    have hn : ¬ (K + 1 + τ ≤ K + τ) := by omega
    rw [hJ0]; simp [hn]
  refine ⟨J0, ?_⟩
  obtain ⟨hI, _⟩ := hf J0 hJa
  have hdiv := hw J0 hJa (by rw [hJs]; exact hJmod)
  have hy0 : 1 ≤ (2 : Int) ^ ν * (t : Int) := by
    have h1 := ipow2_ge_one ν
    have := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ (t : Int) by omega)
      (show (0 : Int) ≤ (2 : Int) ^ ν by omega)
    rw [Int.mul_one] at this; omega
  have hY0 : ((2 ^ ν * t : Nat) : Int) = (2 : Int) ^ ν * (t : Int) := by
    simp only [Int.natCast_mul, Int.natCast_pow]; norm_cast
  obtain ⟨yi, hyi, hr⟩ := chain_reaches q P ((2 : Int) ^ ν * (t : Int)) b J0 (K + 1 + τ) hI hy0
    (fun l h1 h2 => hbpos l h1 h2) (2 ^ ν * t) hY0 (K + 1 + τ) (Nat.le_refl _)
  have hreach : Reaches q yi t := reaches_trans q hr (reaches_pow2 q t ν)

  have hstep := step_lower q P ((2 : Int) ^ ν * (t : Int)) b J0 (K + 1 + τ) hI hy0
    (fun l h1 h2 => hbpos l h1 h2) (K + τ) (by omega)
  have e1 : K + τ + 1 = K + 1 + τ := by omega
  rw [e1, hJs] at hstep
  have hpow : (2 : Int) ^ amin ≤ (2 : Int) ^ (b (K + 1 + τ) + j * P) :=
    ipow2_mono _ _ hjlo
  have hBi : (q : Int) * ((B : Int) + 1) + 1 ≤ (2 : Int) ^ amin := by
    have := hB; exact_mod_cast this
  have hyB : (B : Int) + 1 ≤ chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J0 (K + 1 + τ) := by
    have hq' : (0 : Int) < (q : Int) := by omega
    have h1 : (q : Int) * ((B : Int) + 1) ≤ (q : Int) * chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J0 (K + 1 + τ) := by
      have := Int.le_trans hBi (Int.le_trans hpow hstep); omega
    exact Int.le_of_mul_le_mul_left h1 hq'
  have hBy : B < yi := by
    have : (yi : Int) = chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b J0 (K + 1 + τ) := hyi
    omega
  refine ⟨hI, yi, hreach, hBy, hdiv, hyi, ?_⟩

  have hsmall : ∀ l, 1 ≤ l → l + 1 ≤ K + 1 + τ → b l + J0 l * P ≤ (q - 1) * P + E0 := by
    intro l h1 h2
    have hJl : J0 l = f l := hJa l h1 (by omega)
    have hfl : f l < q := hfb l h1 (by omega)
    have hbl := hbE l h1 (by omega)
    have hmul : J0 l * P ≤ (q - 1) * P := by
      apply Nat.mul_le_mul_right; rw [hJl]; omega
    omega
  have hlast : b (K + 1 + τ) + J0 (K + 1 + τ) * P ≤ amin + P * q ^ (N - K) := by
    rw [hJs]; have := hjhi; rw [Nat.mul_comm j P] at *; omega
  have hsz := size_bound q P ν t (K + 1 + τ) ((q - 1) * P + E0) (amin + P * q ^ (N - K)) ν b J0
    (by omega) ht1 (Nat.le_refl ν) hI (fun l h1 h2 => hbpos l h1 (by omega)) hsmall hlast
  have e2 : K + 1 + τ - 1 = K + τ := by omega
  rw [e2] at hsz
  exact hsz

def steps (K γ m' : Nat) : Nat := if m' = 1 then 1 else K + γ + 2

theorem chain_witness (q K P uPn e γ ν t N B amin m' : Nat) [NonWieferich q] (ρ c : Int)
    (hP : (2 : Int) ^ P = 1 + (q : Int) ^ (K + 1) * (uPn : Int))
    (huP : Nat.Coprime q uPn)
    (hc : (q : Int) ^ (K + 1) ∣ (2 - (q : Int)) * c - 1)
    (hνc : (q : Int) ^ (K + 1) ∣ (2 : Int) ^ ν * (t : Int) - c)
    (ht1 : 1 ≤ t) (hN : K ≤ N)
    (hPpos : 0 < P) (heP : e ∣ P) (he0 : 0 < e) (he : 2 ^ e % m' = 1 % m')
    (hcov : Covers q m' γ) (hqm : Nat.Coprime m' q) (hm0 : 0 < m') (hK1 : m' = 1 → K = 0)
    (hB : q * (B + 1) + 1 ≤ 2 ^ amin) :
    ∃ y : Nat, Reaches q y t ∧ B < y ∧ (q : Int) ^ N * (m' : Int) ∣ (y : Int) - ρ ∧
      (y : Int) ≤ (2 : Int) ^ (ν + (steps K γ m' - 1) * ((q - 1) * P + e) + (amin + P * q ^ (N - K)))
        * (t : Int) := by
  by_cases h1 : m' = 1
  · have hK := hK1 h1
    subst h1; subst hK
    obtain ⟨J, _, y, hr, hBy, hdiv, hyi, hsz⟩ := delay_line_witness q 0 P uPn 0 ν t N B amin ρ c hP huP hc hνc
      ht1 hN (fun _ => 1) (fun _ _ _ => rfl) (fun _ _ _ => Nat.le_refl 1)
      e (fun _ _ _ => he0) (Nat.le_of_dvd hPpos heP) hPpos hB
    refine ⟨y, hr, hBy, ?_, ?_⟩
    · rw [hyi]; simpa using hdiv
    · have hs : steps 0 γ 1 - 1 = 0 := by simp [steps]
      rw [hs, hyi]; simpa using hsz
  · have hs : steps K γ m' - 1 = K + (γ + 1) := by simp [steps, h1]; omega
    rw [hs]
    have hq0 : 0 < q := by have := NonWieferich.three_le (q := q); omega
    have hodd := NonWieferich.odd (q := q)
    have hqcop : Nat.Coprime m' q := hqm

    have hm2P : (m' : Int) ∣ (2 : Int) ^ P - 1 := by
      have h1 : 2 ^ P % m' = 1 % m' := by
        have := pow_two_mod_period m' e he P 0 (by rw [Nat.zero_mod]; exact Nat.mod_eq_zero_of_dvd heP)
        rw [Nat.pow_zero] at this; exact this
      have h2 := nat_mod_to_int_dvd (2 ^ P) 1 m' h1
      simp only [Int.natCast_pow, Int.natCast_one] at h2
      exact h2

    have S0 := setup_of q K P uPn c ((2 : Int) ^ ν * (t : Int)) (fun _ => 1) hP huP hc hνc (fun i _ _ => rfl)
    have hI0 : Integral (q : Int) P ((2 : Int) ^ ν * (t : Int)) (fun _ => 1) (fun _ => 0) (K + 1) := (primer_chain S0 (fun _ => 0)).2

    obtain ⟨β, hβb, hβs⟩ := steer q m' e γ hm0 he0 he hcov hqcop
      (chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) (fun _ => 1) (fun _ => 0) (K + 1)) ρ
    obtain ⟨b', hb'⟩ : ∃ b' : Nat → Nat, b' = fun i => if i ≤ K + 1 then 1 else β (i - (K + 1)) := ⟨_, rfl⟩
    have hb1 : ∀ i, 1 ≤ i → i ≤ K + 1 → b' i = 1 := by
      intro i h1 h2; rw [hb']; simp [h2]
    have hβle : ∀ l, 1 ≤ l → l ≤ γ + 1 → 1 ≤ β l ∧ β l ≤ e := hβb
    have hbpos : ∀ i, 1 ≤ i → i ≤ K + 1 + (γ + 1) → 1 ≤ b' i := by
      intro i h1 h2
      by_cases hi : i ≤ K + 1
      · rw [hb1 i h1 hi]; exact Nat.le_refl 1
      · rw [hb']; simp only [hi, ite_false]
        exact (hβle (i - (K + 1)) (by omega) (by omega)).1
    have hePle : e ≤ P := Nat.le_of_dvd hPpos heP
    have hbE : ∀ i, 1 ≤ i → i ≤ K + 1 + (γ + 1) → b' i ≤ e := by
      intro i h1 h2
      by_cases hi : i ≤ K + 1
      · rw [hb1 i h1 hi]; omega
      · rw [hb']; simp only [hi, ite_false]
        exact (hβle (i - (K + 1)) (by omega) (by omega)).2
    obtain ⟨J, hI, y, hreach, hBy, hdiv, hyi, hszb⟩ :=
      delay_line_witness q K P uPn (γ + 1) ν t N B amin ρ c hP huP hc hνc ht1 hN b' hb1 hbpos e hbE hePle hPpos hB
    refine ⟨y, hreach, hBy, ?_, ?_⟩

    have hIb' : Integral (q : Int) P ((2 : Int) ^ ν * (t : Int)) b' J (K + 1) :=
      (primer_chain (setup_of q K P uPn c ((2 : Int) ^ ν * (t : Int)) b' hP huP hc hνc hb1) J).2
    have hx0 : (m' : Int) ∣ chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b' J (K + 1)
        - chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) (fun _ => 1) (fun _ => 0) (K + 1) := by
      refine class_indep_of_shifts m' q P hm0 hqcop hm2P ((2 : Int) ^ ν * (t : Int)) ((2 : Int) ^ ν * (t : Int)) b' (fun _ => 1) J (fun _ => 0) (K + 1)
        hIb' hI0 ?_ (by simp) (K + 1) (Nat.le_refl _)
      intro i h1 h2; rw [hb1 i h1 h2]
    have hrel : ∀ l, 1 ≤ l → l ≤ γ + 1 →
        (m' : Int) ∣ (q : Int) * chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b' J (K + 1 + l) + 1
          - (2 : Int) ^ (β l) * chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b' J (K + 1 + (l - 1)) := by
      intro l h1 h2
      have hc' := chain_rel_mod (m' : Int) q P ((2 : Int) ^ ν * (t : Int)) b' J (K + 1 + (γ + 1)) hI hm2P
        (K + l) (by omega)
      have e1 : K + l + 1 = K + 1 + l := by omega
      have e2 : K + 1 + (l - 1) = K + l := by omega
      have eb : b' (K + 1 + l) = β l := by
        rw [hb']; simp only [show ¬ (K + 1 + l ≤ K + 1) by omega, ite_false]
        congr 1; omega
      rw [e2, ← eb]
      rw [e1] at hc'
      exact hc'
    have hfin := hβs (fun l => chain (q : Int) P ((2 : Int) ^ ν * (t : Int)) b' J (K + 1 + l)) hx0 hrel
    obtain ⟨g, hg⟩ := hdiv
    have hcopN : Nat.Coprime m' (q ^ N) := Nat.Coprime.pow_right N hqm
    have hm'g : (m' : Int) ∣ ((q ^ N : Nat) : Int) * g := by
      rw [Int.natCast_pow, ← hg]; exact hfin
    obtain ⟨k, hk⟩ := int_cancel m' (q ^ N) hm0 hcopN g hm'g
    · refine ⟨k, ?_⟩
      rw [hyi, hg, hk]
      int_ring
    · rw [hyi]; exact hszb

def ceilLog2 (n : Nat) : Nat := Nat.log2 (n - 1) + 1

theorem ceilLog2_spec (n : Nat) : n ≤ 2 ^ ceilLog2 n := by
  unfold ceilLog2
  have := @Nat.lt_log2_self (n - 1)
  omega

theorem final_budget (α ν S Q amin dK q m B t Θ y w : Nat)
    (hw : w ≤ 2 ^ α * y) (hy : y ≤ 2 ^ (ν + S + (amin + Q)) * t) (hν : ν + 1 ≤ dK)
    (ham : 2 ^ amin ≤ 2 * (q * Θ)) (hΘ : Θ ≤ q ^ α * ((m + 1) * (B + 1))) :
    w ≤ (B + 1) * t * 2 ^ (dK + S + Q + (α + 1) + ceilLog2 (q ^ (α + 1)) + (ceilLog2 (m + 1))) := by
  have hm1 : m + 1 ≤ 2 ^ (ceilLog2 (m + 1)) := ceilLog2_spec (m + 1)
  have hqa : q ^ (α + 1) ≤ 2 ^ (ceilLog2 (q ^ (α + 1))) := ceilLog2_spec _

  have h2a : 2 ^ amin ≤ 2 ^ (1 + ceilLog2 (q ^ (α + 1)) + (ceilLog2 (m + 1))) * (B + 1) := by
    have e1 : q * Θ ≤ q ^ (α + 1) * (m + 1) * (B + 1) := by
      have := Nat.mul_le_mul_left q hΘ
      calc q * Θ ≤ q * (q ^ α * ((m + 1) * (B + 1))) := this
        _ = q ^ (α + 1) * (m + 1) * (B + 1) := by rw [Nat.pow_succ]; ac_rfl
    have e2 : q ^ (α + 1) * (m + 1) * (B + 1) ≤ 2 ^ (ceilLog2 (q ^ (α + 1))) * 2 ^ (ceilLog2 (m + 1)) * (B + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hqa hm1)
    have e3 : 2 ^ (1 + ceilLog2 (q ^ (α + 1)) + (ceilLog2 (m + 1))) * (B + 1)
        = 2 * (2 ^ (ceilLog2 (q ^ (α + 1))) * 2 ^ (ceilLog2 (m + 1)) * (B + 1)) := by
      rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]; ac_rfl
    rw [e3]; omega
  have hexp : α + (ν + S + Q) + (1 + ceilLog2 (q ^ (α + 1)) + (ceilLog2 (m + 1)))
      ≤ dK + S + Q + (α + 1) + ceilLog2 (q ^ (α + 1)) + (ceilLog2 (m + 1)) := by
    omega
  calc w ≤ 2 ^ α * y := hw
    _ ≤ 2 ^ α * (2 ^ (ν + S + (amin + Q)) * t) := Nat.mul_le_mul_left _ hy
    _ = 2 ^ (α + (ν + S + Q)) * 2 ^ amin * t := by
        rw [show ν + S + (amin + Q) = (ν + S + Q) + amin by omega,
          show α + (ν + S + Q) = α + (ν + S + Q) from rfl, Nat.pow_add 2 (ν + S + Q) amin,
          Nat.pow_add 2 α (ν + S + Q)]; ac_rfl
    _ ≤ 2 ^ (α + (ν + S + Q)) * (2 ^ (1 + ceilLog2 (q ^ (α + 1)) + (ceilLog2 (m + 1))) * (B + 1)) * t :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2a)
    _ = (B + 1) * t * 2 ^ (α + (ν + S + Q) + (1 + ceilLog2 (q ^ (α + 1)) + (ceilLog2 (m + 1)))) := by
        rw [Nat.pow_add 2 (α + (ν + S + Q))]; ac_rfl
    _ ≤ (B + 1) * t * 2 ^ (dK + S + Q + (α + 1) + ceilLog2 (q ^ (α + 1)) + (ceilLog2 (m + 1))) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hexp)

def Pper (q d K e : Nat) : Nat := Nat.lcm (d * q ^ K) e

def Ebound (q m α β d K e γ m' : Nat) : Nat :=
  d * q ^ K + (steps K γ m' - 1) * ((q - 1) * Pper q d K e + e)
    + q ^ (α + β - K) * Pper q d K e + (α + 1) + ceilLog2 (q ^ (α + 1)) + (ceilLog2 (m + 1))

def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ a, a ∣ p → a = 1 ∨ a = p

def IsOrder2 (n d : Nat) : Prop :=
  0 < d ∧ 2 ^ d % n = 1 % n ∧ ∀ i, 0 < i → i < d → 2 ^ i % n ≠ 1 % n

theorem covers_of_phi (q m' e k : Nat) (hm : 1 < m') (hodd : m' % 2 = 1)
    (hM : Nat.Coprime m' q) (he : IsOrder2 m' e) (hk : m' ≤ k * TS.phi e + 1) :
    Covers q m' k :=
  covers_of_growth q m' e k hm hodd (by rw [Nat.gcd_comm]; exact hM) he.2.1 he.2.2 he.1
    (by omega)

def Decomp (q m α mq m' β d e eQ e' K : Nat) : Prop :=
  m = 2 ^ α * mq * m' ∧ Nat.Coprime m' (2 * q) ∧ (∀ p, IsPrime p → p ∣ mq → p ∣ q) ∧
  mq ∣ q ^ β ∧ (∀ j, mq ∣ q ^ j → β ≤ j) ∧
  IsOrder2 q d ∧ IsOrder2 m' e ∧ e = eQ * e' ∧
  (∀ p, IsPrime p → p ∣ eQ → p ∣ q) ∧ Nat.Coprime e' q ∧
  eQ ∣ q ^ K ∧ (∀ j, eQ ∣ q ^ j → K ≤ j)

theorem decomp_K1 (q m α mq m' β d e eQ e' K : Nat) (hD : Decomp q m α mq m' β d e eQ e' K) :
    m' = 1 → K = 0 := by
  intro h1
  obtain ⟨-, -, -, -, -, -, ⟨he0, -, hmin⟩, hee, -, -, -, hK⟩ := hD
  subst h1
  have he1 : e = 1 := by
    rcases Nat.lt_or_ge e 2 with h | h
    · omega
    · exact absurd (by simp [Nat.mod_one]) (hmin 1 (by omega) h)
  rw [he1] at hee
  have hQ : eQ = 1 := Nat.eq_one_of_mul_eq_one_right hee.symm
  have := hK 0 (by rw [hQ]; exact Nat.one_dvd _)
  omega

theorem isPrime_dvd_mul {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  rcases hp.2 _ (Nat.gcd_dvd_left p a) with h1 | h1
  · exact Or.inr (Nat.Coprime.dvd_of_dvd_mul_left h1 h)
  · exact Or.inl (h1 ▸ Nat.gcd_dvd_right p a)

theorem isPrime_dvd_pow {p q : Nat} (hp : IsPrime p) : ∀ k, p ∣ q ^ k → p ∣ q
  | 0, h => by rw [Nat.pow_zero] at h; have := Nat.eq_one_of_dvd_one h; have := hp.1; omega
  | k + 1, h => by
    rw [Nat.pow_succ] at h
    rcases isPrime_dvd_mul hp h with h1 | h1
    · exact isPrime_dvd_pow hp k h1
    · exact h1

theorem primes_of_dvd_pow {mq q k : Nat} (hA : mq ∣ q ^ k) : ∀ p, IsPrime p → p ∣ mq → p ∣ q :=
  fun _ hp h => isPrime_dvd_pow hp k (Nat.dvd_trans h hA)

theorem least_pow_dvd (mq q k : Nat) (hA : mq ∣ q ^ k) :
    ∃ β, mq ∣ q ^ β ∧ ∀ j, mq ∣ q ^ j → β ≤ j := by
  obtain ⟨β, hβ, hmin⟩ := exists_least (fun j => mq ∣ q ^ j) ⟨k, hA⟩
  exact ⟨β, hβ, fun j hj => Nat.le_of_not_lt (fun h => hmin j h hj)⟩

theorem least_order (n : Nat) (h : ∃ D, 0 < D ∧ 2 ^ D % n = 1 % n) : ∃ d, IsOrder2 n d := by
  obtain ⟨d, ⟨hd0, hd⟩, hmin⟩ := exists_least (fun D => 0 < D ∧ 2 ^ D % n = 1 % n) h
  exact ⟨d, hd0, hd, fun i hi hid hi' => hmin i hid ⟨hi, hi'⟩⟩

def cb_cands : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | k + 1, e => (List.range e).flatMap (fun a => (cb_cands k e).map (a :: ·))

theorem cb_mem_cands : ∀ k e I, I ∈ cb_cands k e ↔ I.length = k ∧ ∀ a ∈ I, a < e
  | 0, e, I => by
    cases I with
    | nil => exact ⟨fun _ => ⟨rfl, fun a ha => absurd ha (List.not_mem_nil)⟩, fun _ => List.mem_singleton_self []⟩
    | cons a J => exact ⟨fun h => absurd (List.mem_singleton.1 h) (List.cons_ne_nil a J),
        fun h => absurd h.1 (Nat.succ_ne_zero J.length)⟩
  | k + 1, e, I => by
    cases I with
    | nil => exact ⟨fun h => by
        have h' : [] ∈ (List.range e).flatMap (fun a => (cb_cands k e).map (a :: ·)) := h
        obtain ⟨a, -, hh⟩ := List.mem_flatMap.1 h'
        obtain ⟨J, -, hJ⟩ := List.mem_map.1 hh
        exact absurd hJ (List.cons_ne_nil a J),
      fun h => absurd h.1 (fun e => Nat.succ_ne_zero k e.symm)⟩
    | cons a J =>
      simp only [cb_cands, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
        List.length_cons]
      constructor
      · rintro ⟨b, hb, J', hJ', h⟩
        cases h
        have hJ := (cb_mem_cands k e J).1 hJ'
        refine ⟨by omega, ?_⟩
        intro c hc
        rcases hc with rfl | hc
        · exact hb
        · exact hJ.2 c hc
      · rintro ⟨hlen, hall⟩
        have ha : a < e := hall a (Or.inl rfl)
        have hJ : J.length = k ∧ ∀ c ∈ J, c < e :=
          ⟨by omega, fun c hc => hall c (Or.inr hc)⟩
        exact ⟨a, ha, J, (cb_mem_cands k e J).2 hJ, rfl⟩

def cb_bool (q m' γ e : Nat) : Bool :=
  (List.range m').all (fun x => (cb_cands γ e).any (fun I => wsum q I % m' == x % m'))

theorem cb_bool_iff (q m' γ e : Nat) : cb_bool q m' γ e = true ↔ CoversBounded q m' γ e := by
  unfold cb_bool CoversBounded
  simp only [List.all_eq_true, List.any_eq_true, List.mem_range, nat_beq_iff]
  constructor
  · intro h x hx
    obtain ⟨I, hI, heq⟩ := h x hx
    exact ⟨I, ((cb_mem_cands γ e I).1 hI).1, ((cb_mem_cands γ e I).1 hI).2, heq⟩
  · intro h x hx
    obtain ⟨I, hl, hb, heq⟩ := h x hx
    exact ⟨I, (cb_mem_cands γ e I).2 ⟨hl, hb⟩, heq⟩

instance (q m' γ e : Nat) : Decidable (CoversBounded q m' γ e) :=
  decidable_of_iff _ (cb_bool_iff q m' γ e)

def srch (p : Nat → Prop) [DecidablePred p] : Nat → Nat → Nat
  | 0, n => n
  | f + 1, n => if p n then n else srch p f (n + 1)

theorem srch_spec (p : Nat → Prop) [DecidablePred p] : ∀ f n, (∃ j, n ≤ j ∧ j ≤ n + f ∧ p j) →
    p (srch p f n) ∧ ∀ j, n ≤ j → j < srch p f n → ¬ p j
  | 0, n, ⟨j, hn, hj, hp⟩ => by
    have hjn : j = n := by omega
    subst hjn
    exact ⟨hp, fun k hk hlt => by simp only [srch] at hlt; omega⟩
  | f + 1, n, ⟨j, hn, hj, hp⟩ => by
    by_cases hpn : p n
    · have e1 : srch p (f + 1) n = n := by
        show (if p n then n else srch p f (n + 1)) = n
        exact ite_eq_left hpn
      rw [e1]
      exact ⟨hpn, fun k hk hlt => absurd hlt (by omega)⟩
    · have e1 : srch p (f + 1) n = srch p f (n + 1) := by
        show (if p n then n else srch p f (n + 1)) = srch p f (n + 1)
        exact ite_eq_right hpn
      have hjn : n + 1 ≤ j := by
        rcases Nat.eq_or_lt_of_le hn with h | h
        · exact absurd (h ▸ hp) hpn
        · omega
      obtain ⟨h1, h2⟩ := srch_spec p f (n + 1) ⟨j, hjn, by omega, hp⟩
      rw [e1]
      refine ⟨h1, fun k hk hlt => ?_⟩
      rcases Nat.eq_or_lt_of_le hk with h | h
      · exact h ▸ hpn
      · exact h2 k (by omega) hlt

theorem odd_of_coprime_two {n : Nat} (h : Nat.Coprime n 2) : n % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h0
  · have h2 : 2 ∣ Nat.gcd n 2 := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h0) (Nat.dvd_refl 2)
    rw [h] at h2
    exact absurd (Nat.le_of_dvd Nat.one_pos h2) (by decide)
  · exact h0

def gammaPhi (m' e : Nat) : Nat := (m' + TS.phi e - 2) / TS.phi e

theorem covers_phi_of_order (q m' e : Nat) (hM : Nat.Coprime m' (2 * q)) (he : IsOrder2 m' e) :
    Covers q m' (gammaPhi m' e) := by
  obtain ⟨he0, hee, hmin'⟩ := he
  have hM2 : m' % 2 = 1 := odd_of_coprime_two (coprime_two_of_coprime_two_mul hM)
  unfold gammaPhi
  rcases Nat.lt_or_ge 1 m' with h1 | h1
  · have he2 : 2 ≤ e := by
      rcases Nat.lt_or_ge e 2 with h | h
      · have : e = 1 := by omega
        subst this
        rw [Nat.pow_one, Nat.mod_eq_of_lt (by omega : 2 < m'), Nat.mod_eq_of_lt h1] at hee; omega
      · exact h
    have hφ : 0 < TS.phi e := by
      unfold TS.phi TS.card
      refine Nat.pos_of_ne_zero (fun h0 => ?_)
      have hx : (Nat.gcd 1 e == 1) = false :=
        (my_countP_eq_zero _ _).1 h0 1 (List.mem_range.mpr (by omega))
      rw [Nat.gcd_one_left] at hx
      exact absurd hx (by decide)
    apply covers_of_phi q m' e _ h1 hM2 (coprime_p_of_coprime_two_mul hM) ⟨he0, hee, hmin'⟩
    have h3 := Nat.div_add_mod (m' + TS.phi e - 2) (TS.phi e)
    have h4 := Nat.mod_lt (m' + TS.phi e - 2) hφ
    rw [Nat.mul_comm] at h3
    generalize (m' + TS.phi e - 2) / TS.phi e * TS.phi e = G at *
    generalize (m' + TS.phi e - 2) % TS.phi e = R at *
    omega
  · have hM0 : m' ≠ 0 := by intro h; rw [h] at hM2; exact absurd hM2 (by decide)
    have : m' = 1 := by omega
    subst this
    intro x hx
    exact ⟨List.replicate ((1 + TS.phi e - 2) / TS.phi e) 0, List.length_replicate, by simp [Nat.mod_one]⟩

def leastCover (q m' e : Nat) : Nat := srch (fun γ => CoversBounded q m' γ e) (gammaPhi m' e) 0

theorem leastCover_spec (q m' e : Nat) (hM : Nat.Coprime m' (2 * q)) (he : IsOrder2 m' e) :
    Covers q m' (leastCover q m' e) ∧ (∀ j, j < leastCover q m' e → ¬ Covers q m' j) := by
  have hb := (covers_iff_bounded q m' e he.1 he.2.1 _).1 (covers_phi_of_order q m' e hM he)
  obtain ⟨hsp, hmn⟩ := srch_spec (fun γ => CoversBounded q m' γ e) (gammaPhi m' e) 0
    ⟨gammaPhi m' e, Nat.zero_le _, by omega, hb⟩
  exact ⟨(covers_iff_bounded q m' e he.1 he.2.1 _).2 hsp, fun j hj hc =>
    hmn j (Nat.zero_le _) hj ((covers_iff_bounded q m' e he.1 he.2.1 j).1 hc)⟩

theorem exists_decomp (q : Nat) [NonWieferich q] (m : Nat) (hm : 1 ≤ m) :
    ∃ α mq m' β d e eQ e' K : Nat, Decomp q m α mq m' β d e eQ e' K := by
  have hq3 := NonWieferich.three_le (q := q)
  obtain ⟨α, O, hmO, hOodd⟩ := split_two_power m hm
  obtain ⟨mq, m', k, hOAM, hMq, hAk⟩ := split_coprime q O (by omega)
  have hmA : m = 2 ^ α * mq * m' := by rw [hmO, hOAM, Nat.mul_assoc]
  have hM2 : m' % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one m' with h | h
    · have := Nat.mul_mod mq m' 2; rw [h, ← hOAM] at this; simp at this; omega
    · exact h
  have hM : Nat.Coprime m' (2 * q) := Nat.Coprime.mul_right (coprime_two_of_odd hM2) hMq
  have hMpos : 0 < m' := by omega
  obtain ⟨β, hAβ, hβmin⟩ := least_pow_dvd mq q k hAk
  obtain ⟨D, u, hD0, hD, -⟩ := NonWieferich.gen (q := q)
  obtain ⟨d, hdo⟩ := least_order q ⟨D, hD0, by rw [hD, Nat.add_mul_mod_self_left]⟩
  obtain ⟨D1, hD1, -, hD1p⟩ := exists_pow2_period m' hMpos (coprime_two_of_coprime_two_mul hM)
  obtain ⟨e, he⟩ := least_order m' ⟨D1, hD1, hD1p⟩
  have he0 := he.1
  obtain ⟨eQ, e', k2, hee', he'q, hQk⟩ := split_coprime q e (by omega)
  obtain ⟨K, hQK, hKmin⟩ := least_pow_dvd eQ q k2 hQk
  exact ⟨α, mq, m', β, d, e, eQ, e', K, hmA, hM, primes_of_dvd_pow hAk, hAβ, hβmin, hdo, he, hee',
    primes_of_dvd_pow hQk, he'q, hQK, hKmin⟩

def OddNonWieferich (q : Nat) : Prop :=
  1 < q ∧ q % 2 = 1 ∧ ∀ d, IsOrder2 q d → Nat.Coprime q ((2 ^ d - 1) / q)

theorem pow_eq_of_order {q d : Nat} (hq : 1 < q) (hd : IsOrder2 q d) :
    2 ^ d = 1 + q * ((2 ^ d - 1) / q) := by
  have h1 : 2 ^ d % q = 1 := by rw [hd.2.1]; exact Nat.mod_eq_of_lt hq
  have h2 := Nat.div_add_mod (2 ^ d) q
  rw [h1] at h2
  have h3 : 2 ^ d - 1 = q * (2 ^ d / q) := by omega
  rw [h3, Nat.mul_div_cancel_left _ (by omega)]
  omega

theorem nonWieferich_of_odd {q : Nat} (hq : OddNonWieferich q) : NonWieferich q := by
  obtain ⟨hq1, hodd, hW⟩ := hq
  obtain ⟨D, hD0, -, hDp⟩ := exists_pow2_period q (Nat.lt_trans Nat.zero_lt_one hq1)
    (coprime_two_of_odd hodd)
  obtain ⟨d0, hd0⟩ := least_order q ⟨D, hD0, hDp⟩
  exact ⟨hq1, d0, (2 ^ d0 - 1) / q, pow_eq_of_order hq1 hd0, hW d0 hd0⟩

theorem params_exist (q : Nat) (hq : OddNonWieferich q) (m : Nat) (hm : 1 ≤ m) :
    ∃ α mq m' β d e eQ e' K γ : Nat, Decomp q m α mq m' β d e eQ e' K ∧ Covers q m' γ ∧
      ∀ j, j < γ → ¬ Covers q m' j := by
  haveI := nonWieferich_of_odd hq
  obtain ⟨α, mq, m', β, d, e, eQ, e', K, hD⟩ := exists_decomp q m hm
  have hD2 := hD
  obtain ⟨-, hM, -, -, -, -, he, -⟩ := hD2
  have hs := leastCover_spec q m' e hM he
  exact ⟨α, mq, m', β, d, e, eQ, e', K, leastCover q m' e, hD, hs.1, hs.2⟩

theorem theorem_A (q : Nat) (hq : OddNonWieferich q) (m : Nat) (hm : 1 ≤ m)
    (α mq m' β d e eQ e' K γ : Nat) (hD : Decomp q m α mq m' β d e eQ e' K)
    (hγ : Covers q m' γ) (_ : ∀ j, j < γ → ¬ Covers q m' j)
    (t : Nat) (ht0 : 1 ≤ t) (ht : ∃ i, t % q = 2 ^ i % q) (r B : Nat) :
    ∃ w : Nat, B < w ∧ Reaches q w t ∧ w % m = r % m ∧
      w ≤ (B + 1) * t * 2 ^ (Ebound q m α β d K e γ m') := by
  obtain ⟨i, hi⟩ := ht
  haveI := nonWieferich_of_odd hq
  have hK1 := decomp_K1 q m α mq m' β d e eQ e' K hD
  obtain ⟨hmA, hM, -, hA, -, hdo, ⟨he0, he, -⟩, hee, -, he'q, hKe, -⟩ := hD
  obtain ⟨u, hd, hu⟩ : ∃ u, 2 ^ d = 1 + q * u ∧ Nat.Coprime q u :=
    ⟨(2 ^ d - 1) / q, pow_eq_of_order hq.1 hdo, hq.2.2 d hdo⟩
  have hcov := hγ
  have hq3 := NonWieferich.three_le (q := q)
  have hm0 : 0 < m' := by
    rcases Nat.eq_zero_or_pos m' with h | h
    · rw [h, Nat.mul_zero] at hmA; omega
    · exact h
  have hqm : Nat.Coprime m' q := Nat.Coprime.coprime_mul_left_right hM

  obtain ⟨uP, hPs, huP⟩ := P_struct q K d u e eQ e' hd hu he0 hee hKe he'q
  have hPpos : 0 < Nat.lcm (d * q ^ K) e := by
    have hd0 : 0 < d := hdo.1
    exact Nat.lcm_pos (Nat.mul_pos hd0 (Nat.pow_pos (by omega))) he0
  have hPI : (2 : Int) ^ (Nat.lcm (d * q ^ K) e) = 1 + (q : Int) ^ (K + 1) * (uP : Int) := by
    exact_mod_cast hPs
  obtain ⟨c, hc⟩ := fixed_point_int q K hq3 (coprime_p_two q)
  obtain ⟨ν, hν, hνc⟩ := exists_nu q K d u hd hu t i hi c hc

  obtain ⟨uw, huw, hlen, hdiv⟩ := parity_prefix q α (r % m)
  obtain ⟨ρ, hρ⟩ := hdiv
  have hρ' : 2 ^ α * ρ = q ^ ones uw * (r % m) + kappa q uw := hρ.symm
  have hn : ones uw ≤ α := hlen ▸ ones_le_length uw huw
  have hΘ := theta_bound q hq3 m (r % m) B ρ uw huw (Nat.mod_lt _ (by omega)) (by rw [hlen]; exact hρ')
  rw [hlen] at hΘ

  have hX : 1 ≤ q * (ρ + q ^ ones uw * (B + 1)) := by
    exact Nat.mul_pos (by omega) (Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.succ_pos B)) (Nat.le_add_left _ _))
  obtain ⟨amin, ha1, ha2⟩ := amin_exists _ hX

  have hN : K ≤ K + (α + β - K) := by omega
  obtain ⟨y, hry, hBy, hdy, hsz⟩ := chain_witness q K (Nat.lcm (d * q ^ K) e) uP e γ ν t
    (K + (α + β - K)) (ρ + q ^ ones uw * (B + 1) - 1) amin m' (ρ : Int) (c : Int)
    hPI huP hc hνc ht0 hN hPpos (Nat.dvd_lcm_right _ _) he0 he hcov hqm hm0 hK1
    (by have : ρ + q ^ ones uw * (B + 1) - 1 + 1 = ρ + q ^ ones uw * (B + 1) := by
          have : 0 < q ^ ones uw * (B + 1) :=
            Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.succ_pos B)
          omega
        rw [this]; omega)

  have hρy : ρ + q ^ ones uw * (B + 1) ≤ y := by omega
  have hyc : q ^ (ones uw + β) * m' ∣ y - ρ := by
    have h1 : ((q ^ (K + (α + β - K)) * m' : Nat) : Int) ∣ ((y - ρ : Nat) : Int) := by
      rw [Int.natCast_sub (by omega)]; push_cast; exact hdy
    have h2 := Int.ofNat_dvd.1 h1
    exact Nat.dvd_trans (Nat.mul_dvd_mul_right (Nat.pow_dvd_pow q (by omega)) m') h2
  obtain ⟨w, hBw, hrw, hwm, hwy⟩ := tail_lemma q uw huw α hlen (r % m) ρ hρ' mq m' β B y hA hρy hyc
  refine ⟨w, hBw, reaches_trans q hrw hry, ?_, ?_⟩
  · rw [← hmA] at hwm; rw [hwm, Nat.mod_mod]
  · have hyN : y ≤ 2 ^ (ν + (steps K γ m' - 1) * ((q - 1) * Nat.lcm (d * q ^ K) e + e)
        + (amin + Nat.lcm (d * q ^ K) e * q ^ (K + (α + β - K) - K))) * t := by
      have : ((2 ^ (ν + (steps K γ m' - 1) * ((q - 1) * Nat.lcm (d * q ^ K) e + e)
        + (amin + Nat.lcm (d * q ^ K) e * q ^ (K + (α + β - K) - K))) * t : Nat) : Int)
          = (2 : Int) ^ (ν + (steps K γ m' - 1) * ((q - 1) * Nat.lcm (d * q ^ K) e + e)
        + (amin + Nat.lcm (d * q ^ K) e * q ^ (K + (α + β - K) - K))) * (t : Int) := by push_cast; rfl
      exact_mod_cast (this ▸ hsz)
    have hKK : K + (α + β - K) - K = α + β - K := by omega
    rw [hKK] at hyN
    have hfb := final_budget α ν ((steps K γ m' - 1) * ((q - 1) * Nat.lcm (d * q ^ K) e + e))
      (Nat.lcm (d * q ^ K) e * q ^ (α + β - K)) amin (d * q ^ K) q m B t
      (ρ + q ^ ones uw * (B + 1)) y w hwy hyN (by omega) ha2 hΘ
    unfold Ebound Pper
    have e2 : q ^ (α + β - K) * Nat.lcm (d * q ^ K) e = Nat.lcm (d * q ^ K) e * q ^ (α + β - K) :=
      Nat.mul_comm _ _
    rw [e2]; exact hfb

def Trapped (qg g x : Nat) : Prop := (∃ k, x % qg = 2 ^ k % qg) ∨ x % g = 0

theorem trapped_step (q g D x : Nat) (ha : 0 < q) (hg : 1 < g) (hga : g ∣ q)
    (hQ : 2 ^ D % (q * g) = 1 % (q * g))
    (hmin : ∀ k, 2 ^ k % q = 1 % q → D ∣ k)
    (h : Trapped (q * g) g (collatz q x)) : Trapped (q * g) g x := by
  unfold collatz at h
  by_cases hx : x % 2 = 0
  · simp only [hx, ite_true] at h
    have e : x = 2 * (x / 2) := by omega
    rcases h with ⟨k, hk⟩ | h
    · left; refine ⟨k + 1, ?_⟩
      rw [e, Nat.mul_mod, hk, ← Nat.mul_mod, Nat.pow_succ, Nat.mul_comm]
    · right; rw [e, Nat.mul_mod, h]; simp
  · simp only [hx, ite_false] at h
    rcases h with ⟨k, hk⟩ | h
    · have hka : 2 ^ k % q = 1 % q := by
        have := mod_of_dvd_mod (Nat.dvd_mul_right q g) hk
        rw [← this, Nat.add_mod, Nat.mul_mod_right]; simp
      obtain ⟨c, hc⟩ := hmin k hka
      have h1 : 2 ^ k % (q * g) = 1 % (q * g) := by
        rw [hc, Nat.pow_mul, Nat.pow_mod, hQ, ← Nat.pow_mod, Nat.one_pow]
      rw [h1] at hk
      have h2 : (q * g) ∣ q * x := by
        have h4 : (q * x + 1 - 1) % (q * g) = 0 := Nat.sub_mod_eq_zero_of_mod_eq hk
        rw [Nat.add_sub_cancel] at h4
        exact Nat.dvd_of_mod_eq_zero h4
      right
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mul_dvd_mul_left ha h2)
    · exfalso
      obtain ⟨t, ht⟩ := hga
      rw [ht, Nat.add_mod, Nat.mul_assoc, Nat.mul_mod_right] at h
      simp at h <;> omega

theorem trapped_of_iter (q g d t : Nat) (hq : 0 < q) (hg : 1 < g) (hgq : g ∣ q)
    (hQ : 2 ^ d % (q * g) = 1 % (q * g))
    (hmin : ∀ k, 2 ^ k % q = 1 % q → d ∣ k)
    (ht : Trapped (q * g) g t) : ∀ k x, iter (collatz q) k x = t → Trapped (q * g) g x := by
  intro k
  induction k with
  | zero => intro x h; simp [iter] at h; subst h; exact ht
  | succ k ih =>
    intro x h
    exact trapped_step q g d x hq hg hgq hQ hmin (ih _ h)

theorem order_dvd {n d k : Nat} (hd : IsOrder2 n d) (hk : 2 ^ k % n = 1 % n) : d ∣ k := by
  obtain ⟨hd0, hdm, hmin⟩ := hd
  have h := pow_mod_period hdm (k % d) (k / d)
  rw [Nat.mod_add_div] at h
  rcases Nat.eq_zero_or_pos (k % d) with h0 | h0
  · exact Nat.dvd_of_mod_eq_zero h0
  · exact absurd (h.symm.trans hk) (hmin _ h0 (Nat.mod_lt _ hd0))

theorem theorem_B (q g d t : Nat) (hq : 1 < q) (hg : 1 < g) (hgq : g ∣ q)
    (hd : IsOrder2 q d) (hdg : IsOrder2 (q * g) d) (ht : Trapped (q * g) g t) :
    ∀ x, Reaches q x t → Trapped (q * g) g x := by
  intro x hx
  obtain ⟨k, hk⟩ := hx
  exact trapped_of_iter q g d t (Nat.lt_trans Nat.zero_lt_one hq) hg hgq hdg.2.1
    (fun k' hk' => order_dvd hd hk') ht k x hk

theorem two_pow_mul_unique {a b x y : Nat} (hx : x % 2 = 1) (hy : y % 2 = 1)
    (h : 2 ^ a * x = 2 ^ b * y) : a = b ∧ x = y := by
  have key : ∀ a b x y : Nat, x % 2 = 1 → 2 ^ a * x = 2 ^ (a + b + 1) * y → False := by
    intro a b x y hx h
    have h1 : 2 ^ (a + b + 1) * y = 2 ^ a * (2 ^ (b + 1) * y) := by
      rw [Nat.add_assoc, Nat.pow_add, Nat.mul_assoc]
    rw [h1] at h
    have h2 : x = 2 ^ (b + 1) * y := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a) h
    have h3 : x = 2 * (2 ^ b * y) := by
      rw [h2, Nat.pow_succ, Nat.mul_comm (2 ^ b) 2, Nat.mul_assoc]
    rw [h3, Nat.mul_mod_right] at hx
    exact absurd hx (by decide)
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · obtain ⟨c, hc⟩ : ∃ c, b = a + c + 1 := ⟨b - a - 1, by omega⟩
    subst hc
    exact (key a c x y hx h).elim
  · subst hab
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a) h⟩
  · obtain ⟨c, hc⟩ : ∃ c, a = b + c + 1 := ⟨a - b - 1, by omega⟩
    subst hc
    exact (key b c y x hy h.symm).elim

theorem odd_of_dvd_pow {q a k : Nat} (hq : q % 2 = 1) (h : a ∣ q ^ k) : a % 2 = 1 := by
  have hqk : q ^ k % 2 = 1 := by rw [Nat.pow_mod, hq, Nat.one_pow]
  rcases Nat.mod_two_eq_zero_or_one a with h0 | h0
  · have h2 : 2 ∣ a := Nat.dvd_of_mod_eq_zero h0
    have h3 : 2 ∣ q ^ k := Nat.dvd_trans h2 h
    have h4 := Nat.mod_eq_zero_of_dvd h3
    rw [hqk] at h4
    exact absurd h4 (by decide)
  · exact h0

theorem smooth_part_unique {q a a' b b' k k' : Nat} (hq : 0 < q) (ha : a ∣ q ^ k)
    (ha' : a' ∣ q ^ k') (hb : Nat.Coprime b q) (hb' : Nat.Coprime b' q)
    (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have hapos : 0 < a := Nat.pos_of_dvd_of_pos ha (Nat.pow_pos hq)
  have hcop1 : Nat.Coprime a b' :=
    (Nat.Coprime.coprime_dvd_right ha (Nat.Coprime.pow_right k hb')).symm
  have hcop2 : Nat.Coprime a' b :=
    (Nat.Coprime.coprime_dvd_right ha' (Nat.Coprime.pow_right k' hb)).symm
  have hd1 : a ∣ a' := Nat.Coprime.dvd_of_dvd_mul_right hcop1 (h ▸ Nat.dvd_mul_right a b)
  have hd2 : a' ∣ a := Nat.Coprime.dvd_of_dvd_mul_right hcop2 (h.symm ▸ Nat.dvd_mul_right a' b')
  have hEq : a = a' := Nat.dvd_antisymm hd1 hd2
  subst hEq
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hapos h⟩

theorem order2_unique {n d d' : Nat} (h : IsOrder2 n d) (h' : IsOrder2 n d') : d = d' := by
  rcases Nat.lt_trichotomy d d' with hlt | heq | hgt
  · exact absurd h.2.1 (h'.2.2 d h.1 hlt)
  · exact heq
  · exact absurd h'.2.1 (h.2.2 d' h'.1 hgt)

theorem covering_length_unique {q m' γ γ' : Nat} (h : Covers q m' γ)
    (hmin : ∀ j, j < γ → ¬ Covers q m' j) (h' : Covers q m' γ')
    (hmin' : ∀ j, j < γ' → ¬ Covers q m' j) : γ = γ' := by
  rcases Nat.lt_trichotomy γ γ' with hlt | heq | hgt
  · exact absurd h (hmin' γ hlt)
  · exact heq
  · exact absurd h' (hmin γ' hgt)

theorem decomp_unique {q m α mq m' β d e eQ e' K α2 mq2 mp2 β2 d2 e2 eQ2 ep2 K2 : Nat}
    (hq : OddNonWieferich q) (hD : Decomp q m α mq m' β d e eQ e' K)
    (hD2 : Decomp q m α2 mq2 mp2 β2 d2 e2 eQ2 ep2 K2) :
    α = α2 ∧ mq = mq2 ∧ m' = mp2 ∧ β = β2 ∧ d = d2 ∧ e = e2 ∧ eQ = eQ2 ∧ e' = ep2 ∧ K = K2 := by
  obtain ⟨hq1, hodd, -⟩ := hq
  have hq0 : 0 < q := Nat.lt_trans Nat.zero_lt_one hq1
  obtain ⟨hm, hM, -, hA, hAmin, hdo, heo, hee, -, he'q, hKe, hKmin⟩ := hD
  obtain ⟨hm2, hM2, -, hA2, hAmin2, hdo2, heo2, hee2, -, he'q2, hKe2, hKmin2⟩ := hD2
  have hmq : mq % 2 = 1 := odd_of_dvd_pow hodd hA
  have hmq2 : mq2 % 2 = 1 := odd_of_dvd_pow hodd hA2
  have hm'2 : m' % 2 = 1 := odd_of_coprime_two (coprime_two_of_coprime_two_mul hM)
  have hmp2 : mp2 % 2 = 1 := odd_of_coprime_two (coprime_two_of_coprime_two_mul hM2)
  have hx : (mq * m') % 2 = 1 := by rw [Nat.mul_mod, hmq, hm'2]
  have hy : (mq2 * mp2) % 2 = 1 := by rw [Nat.mul_mod, hmq2, hmp2]
  have e1 : 2 ^ α * (mq * m') = 2 ^ α2 * (mq2 * mp2) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← hm, ← hm2]
  obtain ⟨hα, hprod⟩ := two_pow_mul_unique hx hy e1
  obtain ⟨hmqe, hm'e⟩ := smooth_part_unique hq0 hA hA2 (coprime_p_of_coprime_two_mul hM)
    (coprime_p_of_coprime_two_mul hM2) hprod
  subst hmqe
  subst hm'e
  have hβ : β = β2 := Nat.le_antisymm (hAmin β2 hA2) (hAmin2 β hA)
  have hd : d = d2 := order2_unique hdo hdo2
  have he : e = e2 := order2_unique heo heo2
  have hee3 : eQ * e' = eQ2 * ep2 := hee.symm.trans (he.trans hee2)
  obtain ⟨heQ, hep⟩ := smooth_part_unique hq0 hKe hKe2 he'q he'q2 hee3
  subst heQ
  subst hep
  have hK : K = K2 := Nat.le_antisymm (hKmin K2 hKe2) (hKmin2 K hKe)
  exact ⟨hα, rfl, rfl, hβ, hd, he, rfl, rfl, hK⟩

theorem params_unique {q m α mq m' β d e eQ e' K γ α2 mq2 mp2 β2 d2 e2 eQ2 ep2 K2 γ2 : Nat}
    (hq : OddNonWieferich q) (hD : Decomp q m α mq m' β d e eQ e' K) (hγ : Covers q m' γ)
    (hmin : ∀ j, j < γ → ¬ Covers q m' j)
    (hD2 : Decomp q m α2 mq2 mp2 β2 d2 e2 eQ2 ep2 K2) (hγ2 : Covers q mp2 γ2)
    (hmin2 : ∀ j, j < γ2 → ¬ Covers q mp2 j) :
    α = α2 ∧ mq = mq2 ∧ m' = mp2 ∧ β = β2 ∧ d = d2 ∧ e = e2 ∧ eQ = eQ2 ∧ e' = ep2 ∧ K = K2 ∧
      γ = γ2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := decomp_unique hq hD hD2
  subst h3
  exact ⟨h1, h2, rfl, h4, h5, h6, h7, h8, h9, covering_length_unique hγ hmin hγ2 hmin2⟩

end Collatz
#print axioms Collatz.theorem_A
#print axioms Collatz.theorem_B
