import Collatz.Words

namespace Collatz

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


end Collatz
