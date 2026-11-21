import Collatz.Header

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



end Collatz
