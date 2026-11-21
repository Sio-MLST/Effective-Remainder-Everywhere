import Collatz.GeneralLift

/-! Theorem B of generalAB.md (Section 5), from Proposition 1 and the chain decomposition.
    Choice-free. -/

namespace Collatz

theorem chain_restrict {q t m m' : Nat} {w k : Nat → Nat} (h : Chain q t m w k) (hm : m' ≤ m) :
    Chain q t m' w k :=
  ⟨fun l h1 h2 => h.1 l h1 (Nat.le_trans h2 hm), h.2.1,
    fun l h1 h2 => h.2.2 l h1 (Nat.lt_of_lt_of_le h2 hm)⟩

/-- A chain of length m ≥ n + 1 yields a 𝒢_q-path of length n from t. -/
theorem gpath_of_chain {q t m : Nat} {w k : Nat → Nat} (hq : 1 < q) (hodd : q % 2 = 1)
    (ht : 1 ≤ t) (hch : Chain q t m w k) : ∀ n, n + 1 ≤ m → ∃ z, GPath q n t z
  | 0, _ => ⟨t, Vq_of_rel hq hodd hch.2.1, rfl⟩
  | n + 1, hn =>
    ⟨w (n + 1), chain_gpath hq hodd n t w k ht (chain_restrict hch (Nat.le_of_succ_le hn))
      (Vq_of_rel hq hodd (hch.2.2 (n + 1) (Nat.succ_le_succ (Nat.zero_le _)) hn).1)⟩

/-- Theorem B (1): under NoH, every backward chain has length ≤ κ. -/
theorem depth_bound {q t m : Nat} {w k : Nat → Nat} (hq : 1 < q) (hodd : q % 2 = 1)
    (ht : 1 ≤ t) (hNoH : NoH q t) (hch : Chain q t m w k) : m ≤ κq q := by
  match Nat.lt_or_ge (κq q) m with
  | Or.inr h => exact h
  | Or.inl h =>
    exfalso
    obtain ⟨x, hR, hH, _⟩ := prop1_three_to_one hq hodd ht (gpath_of_chain hq hodd ht hch (κq q) h)
    exact hNoH x hR hH

/-- Re-anchor a chain at y when t = 2^c·y with y odd; the first exponent becomes ≥ 1. -/
theorem chain_reanchor {q t y c n : Nat} {w k : Nat → Nat} (hodd : q % 2 = 1) (hn : 1 ≤ n)
    (hch : Chain q t n w k) (hty : t = 2 ^ c * y) (hy : y % 2 = 1) :
    Chain q y n w (fun l => if l = 1 then k 1 + c else k l) ∧ 1 ≤ k 1 + c := by
  have hw1 := hch.1 1 (Nat.le_refl 1) hn
  have h1 : q * w 1 + 1 = 2 ^ (k 1 + c) * y := by
    rw [hch.2.1, hty, Nat.pow_add, Nat.mul_assoc]
  refine ⟨⟨hch.1, by simp only [↓reduceIte]; exact h1, fun l hl1 hl2 => ?_⟩, ?_⟩
  · have hne : ¬ (l + 1 = 1) := by omega
    simp only [hne, ↓reduceIte]
    exact hch.2.2 l hl1 hl2
  · rcases Nat.eq_zero_or_pos (k 1 + c) with h0 | h0
    · exfalso
      rw [h0, Nat.pow_zero, Nat.one_mul] at h1
      have hqw : (q * w 1) % 2 = 1 := by rw [Nat.mul_mod, hodd, hw1.1]
      omega
    · exact h0

/-- Concatenate a chain anchored at t with one anchored at its far end. -/
theorem chain_append {q t m n : Nat} {w k w' k' : Nat → Nat} (hm : 1 ≤ m)
    (h1 : Chain q t m w k) (h2 : Chain q (w m) n w' k') (hk1 : 1 ≤ k' 1) :
    Chain q t (m + n) (fun l => if l ≤ m then w l else w' (l - m))
      (fun l => if l ≤ m then k l else k' (l - m)) := by
  refine ⟨fun l hl1 hl2 => ?_, ?_, fun l hl1 hl2 => ?_⟩
  · by_cases hl : l ≤ m
    · simp only [hl, ↓reduceIte]; exact h1.1 l hl1 hl
    · simp only [hl, ↓reduceIte]; exact h2.1 (l - m) (by omega) (by omega)
  · simp only [hm, ↓reduceIte]; exact h1.2.1
  · by_cases hl : l + 1 ≤ m
    · have hl' : l ≤ m := by omega
      simp only [hl, hl', ↓reduceIte]; exact h1.2.2 l hl1 (by omega)
    · by_cases hlm : l = m
      · subst hlm
        have e : l + 1 - l = 1 := by omega
        simp only [hl, Nat.le_refl, ↓reduceIte, e]
        exact ⟨h2.2.1, hk1⟩
      · have hl' : ¬ l ≤ m := by omega
        have e : l + 1 - m = (l - m) + 1 := by omega
        simp only [hl, hl', ↓reduceIte, e]
        exact h2.2.2 (l - m) (by omega) (by omega)

/-- A loop chain (t = 2^{k₀} w_m) gives chains of every length n·m. -/
theorem chain_pump {q t m k0 : Nat} {w k : Nat → Nat} (hodd : q % 2 = 1) (hm : 1 ≤ m)
    (hch : Chain q t m w k) (hloop : t = 2 ^ k0 * w m) :
    ∀ n, ∃ W K, Chain q t ((n + 1) * m) W K
  | 0 => ⟨w, k, by rw [Nat.zero_add, Nat.one_mul]; exact hch⟩
  | n + 1 => by
    obtain ⟨W, K, hC⟩ := chain_pump hodd hm hch hloop n
    have hnm : 1 ≤ (n + 1) * m := Nat.le_trans hm (Nat.le_mul_of_pos_left m (Nat.succ_pos n))
    have hwm := hch.1 m hm (Nat.le_refl m)
    obtain ⟨hC', hK1⟩ := chain_reanchor hodd hnm hC hloop hwm.1
    have hA := chain_append hm hch hC' (by simp only [↓reduceIte]; exact hK1)
    have e : m + (n + 1) * m = (n + 1 + 1) * m := by
      rw [Nat.add_mul (n + 1) 1 m, Nat.one_mul, Nat.add_comm]
    rw [e] at hA
    exact ⟨_, _, hA⟩

/-- Theorem B (3a): under NoH no element of R_q(t) is periodic. -/
theorem no_periodic {q t x : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (ht : 1 ≤ t)
    (hNoH : NoH q t) (hR : Reaches q x t) : ¬ Periodic q x := by
  intro ⟨L, hL, hper⟩
  obtain ⟨N, hN⟩ := hR
  have htL : iter (collatz q) L t = t := by
    rw [← hN, ← iter_add, Nat.add_comm, iter_add, hper]
  rcases reaches_decomp hq hodd t ht L t htL with h | ⟨m, w, k, k0, hm, hch, hloop⟩
  · have h2 : 2 ≤ 2 ^ L := by
      have := Nat.pow_le_pow_right (show 0 < 2 by omega) hL
      rwa [Nat.pow_one] at this
    have : 2 * t ≤ 2 ^ L * t := Nat.mul_le_mul_right t h2
    omega
  · obtain ⟨W, K, hC⟩ := chain_pump hodd hm hch hloop (κq q)
    have hb := depth_bound hq hodd ht hNoH hC
    have : κq q + 1 ≤ (κq q + 1) * m := Nat.le_mul_of_pos_right _ hm
    omega

/-! ### Counting utilities (choice-free) -/

/-- expand c g [a₁, a₂, …] = [g 0 a₁, …, g (c−1) a₁, g 0 a₂, …]. -/
def expand (c : Nat) (g : Nat → Nat → Nat) : List Nat → List Nat
  | [] => []
  | a :: l => (List.range c).map (fun j => g j a) ++ expand c g l

theorem length_expand (c : Nat) (g : Nat → Nat → Nat) :
    ∀ l : List Nat, (expand c g l).length = c * l.length
  | [] => rfl
  | a :: l => by
    unfold expand
    rw [List.length_append, List.length_map, List.length_range, length_expand c g l,
      List.length_cons, Nat.mul_succ, Nat.add_comm]

theorem mem_expand {c : Nat} {g : Nat → Nat → Nat} {a j : Nat} (hj : j < c) :
    ∀ {l : List Nat}, a ∈ l → g j a ∈ expand c g l
  | [], h => absurd h List.not_mem_nil
  | b :: l, h => by
    unfold expand
    rcases List.mem_cons.mp h with h1 | h1
    · subst h1
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
    · exact List.mem_append.mpr (Or.inr (mem_expand hj h1))

/-! ### Theorem B (2): residues mod 2^n -/

/-- One backward odd step, read mod M = 2^n (qi = q⁻¹ mod M). -/
theorem res_step {q n qi w y j : Nat} (hqi : q * qi % 2 ^ n = 1 % 2 ^ n)
    (h : q * w + 1 = 2 ^ j * y) :
    (j < n → w % 2 ^ n = ((2 ^ j * (y % 2 ^ n) + (2 ^ n - 1)) * qi) % 2 ^ n) ∧
    (n ≤ j → w % 2 ^ n = ((2 ^ n - 1) * qi) % 2 ^ n) := by
  have hM : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hA : w % 2 ^ n = (q * w * qi) % 2 ^ n := by
    rw [Nat.mul_comm q w, Nat.mul_assoc, Nat.mul_mod, hqi, ← Nat.mul_mod, Nat.mul_one]
  have hB : (q * w * qi) % 2 ^ n = ((q * w + 2 ^ n) * qi) % 2 ^ n := by
    rw [Nat.add_mul, Nat.add_mul_mod_self_left]
  have hC : q * w + 2 ^ n = 2 ^ j * y + (2 ^ n - 1) := by omega
  have hW : w % 2 ^ n = ((2 ^ j * y + (2 ^ n - 1)) * qi) % 2 ^ n := by rw [hA, hB, hC]
  have hcong : ∀ X X' c, X % 2 ^ n = X' % 2 ^ n → ((X + c) * qi) % 2 ^ n = ((X' + c) * qi) % 2 ^ n :=
    fun X X' c hX => by rw [Nat.mul_mod, Nat.add_mod, hX, ← Nat.add_mod, ← Nat.mul_mod]
  refine ⟨fun _ => ?_, fun hj => ?_⟩
  · rw [hW]
    exact hcong _ _ _ (by rw [Nat.mul_mod_mod])
  · rw [hW]
    have h0 : 2 ^ j * y % 2 ^ n = 0 % 2 ^ n := by
      rw [Nat.zero_mod]
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow 2 hj) (Nat.dvd_mul_right _ _))
    have := hcong _ _ (2 ^ n - 1) h0
    rw [Nat.zero_add] at this
    exact this

/-- Residues mod M of the far ends of chains of r odd steps. -/
def Sres (n qi t : Nat) : Nat → List Nat
  | 0 => [t % 2 ^ n]
  | r + 1 => expand n (fun j y => ((2 ^ j * y + (2 ^ n - 1)) * qi) % 2 ^ n) (Sres n qi t r) ++
      [((2 ^ n - 1) * qi) % 2 ^ n]

def Ures (n qi t : Nat) : Nat → List Nat
  | 0 => Sres n qi t 0
  | r + 1 => Ures n qi t r ++ Sres n qi t (r + 1)

theorem len_Sres (n qi t : Nat) : ∀ r, (Sres n qi t r).length ≤ (n + 1) ^ r
  | 0 => by simp [Sres]
  | r + 1 => by
    unfold Sres
    rw [List.length_append, length_expand, List.length_singleton, Nat.pow_succ, Nat.mul_add,
      Nat.mul_one]
    have h1 := Nat.mul_le_mul_left n (len_Sres n qi t r)
    have h2 : 1 ≤ (n + 1) ^ r := Nat.pow_pos (Nat.succ_pos n)
    rw [Nat.mul_comm ((n + 1) ^ r) n]
    omega

theorem len_Ures (n qi t : Nat) : ∀ r, n * (Ures n qi t r).length + 1 ≤ (n + 1) ^ (r + 1)
  | 0 => by simp [Ures, Sres]
  | r + 1 => by
    unfold Ures
    rw [List.length_append, Nat.mul_add]
    have h1 := len_Ures n qi t r
    have h2 := Nat.mul_le_mul_left n (len_Sres n qi t (r + 1))
    have e : (n + 1) ^ (r + 1 + 1) = n * (n + 1) ^ (r + 1) + (n + 1) ^ (r + 1) := by
      rw [Nat.pow_succ, Nat.mul_add, Nat.mul_one, Nat.mul_comm]
    omega

theorem Sres_sub_Ures {n qi t x : Nat} : ∀ R r, r ≤ R → x ∈ Sres n qi t r → x ∈ Ures n qi t R
  | 0, r, hr, hx => by
    have : r = 0 := by omega
    subst this; exact hx
  | R + 1, r, hr, hx => by
    unfold Ures
    match Nat.lt_or_ge r (R + 1) with
    | Or.inl hlt => exact List.mem_append.mpr (Or.inl (Sres_sub_Ures R r (by omega) hx))
    | Or.inr hge =>
      have : r = R + 1 := by omega
      subst this
      exact List.mem_append.mpr (Or.inr hx)

/-- Node l of a chain anchored at t (node 0 = t). -/
def node (t : Nat) (w : Nat → Nat) (l : Nat) : Nat := if l = 0 then t else w l

theorem node_rel {q t m : Nat} {w k : Nat → Nat} (hch : Chain q t m w k) :
    ∀ r, r < m → q * w (r + 1) + 1 = 2 ^ k (r + 1) * node t w r
  | 0, _ => by simp only [node, ↓reduceIte]; exact hch.2.1
  | r + 1, h => by
    have hne : ¬ (r + 1 = 0) := by omega
    simp only [node, hne, ↓reduceIte]
    exact (hch.2.2 (r + 1) (by omega) h).1

theorem chain_res {q t m n qi : Nat} {w k : Nat → Nat} (hqi : q * qi % 2 ^ n = 1 % 2 ^ n)
    (hch : Chain q t m w k) : ∀ r, r ≤ m → node t w r % 2 ^ n ∈ Sres n qi t r
  | 0, _ => by simp [node, Sres]
  | r + 1, h => by
    have hrel := node_rel hch r (by omega)
    have ih := chain_res hqi hch r (by omega)
    have hne : ¬ (r + 1 = 0) := by omega
    have hnode : node t w (r + 1) = w (r + 1) := by simp only [node, hne, ↓reduceIte]
    rw [hnode]
    unfold Sres
    obtain ⟨hlt, hge⟩ := res_step hqi hrel
    match Nat.lt_or_ge (k (r + 1)) n with
    | Or.inl hl =>
      rw [hlt hl]
      exact List.mem_append.mpr (Or.inl (mem_expand (g := fun j y =>
        ((2 ^ j * y + (2 ^ n - 1)) * qi) % 2 ^ n) hl ih))
    | Or.inr hg =>
      rw [hge hg]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))

/-- Theorem B (2): |R_q(t) mod 2^n| ≤ (n+1)^{κ+1}. -/
theorem sparsity {q t : Nat} (hq : 1 < q) (hodd : q % 2 = 1) (ht : 1 ≤ t) (hNoH : NoH q t)
    (n : Nat) (hn : 1 ≤ n) (L : List Nat) (hnd : L.Nodup)
    (hL : ∀ r ∈ L, r < 2 ^ n ∧ ∃ x, Reaches q x t ∧ x % 2 ^ n = r) :
    L.length ≤ (n + 1) ^ (κq q + 1) := by
  have h2n : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  have hcop : Nat.gcd q (2 ^ n) = 1 :=
    Nat.Coprime.pow_right n (coprime_two_of_odd hodd)
  obtain ⟨qi, w0, hqw⟩ := nat_bez q (2 ^ n) h2n hcop
  have hqi : q * qi % 2 ^ n = 1 % 2 ^ n := by rw [hqw, Nat.mul_add_mod]
  -- final candidate list
  have hfin : ∀ b e, b % 2 ^ n ∈ Ures n qi t (κq q) →
      (2 ^ e * b) % 2 ^ n ∈ expand n (fun e w => (2 ^ e * w) % 2 ^ n) (Ures n qi t (κq q)) ++ [0] := by
    intro b e hb
    match Nat.lt_or_ge e n with
    | Or.inl he =>
      have h := mem_expand (g := fun e w => (2 ^ e * w) % 2 ^ n) he hb
      have e1 : (2 ^ e * (b % 2 ^ n)) % 2 ^ n = (2 ^ e * b) % 2 ^ n := by
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      rw [← e1]
      exact List.mem_append.mpr (Or.inl h)
    | Or.inr he =>
      have h0 : (2 ^ e * b) % 2 ^ n = 0 :=
        Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow 2 he) (Nat.dvd_mul_right _ _))
      rw [h0]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  have hsub : ∀ r ∈ L, r ∈ expand n (fun e w => (2 ^ e * w) % 2 ^ n) (Ures n qi t (κq q)) ++ [0] := by
    intro r hr
    obtain ⟨_, x, ⟨N, hN⟩, hxr⟩ := hL r hr
    rw [← hxr]
    rcases reaches_decomp hq hodd t ht N x hN with hx | ⟨m, w, k, k0, hm, hch, hx⟩
    · rw [hx]
      exact hfin t N (Sres_sub_Ures (κq q) 0 (Nat.zero_le _) (by simp [Sres]))
    · have hmk := depth_bound hq hodd ht hNoH hch
      have hres := chain_res hqi hch m (Nat.le_refl m)
      have hne : ¬ (m = 0) := by omega
      simp only [node, hne, ↓reduceIte] at hres
      rw [hx]
      exact hfin (w m) k0 (Sres_sub_Ures (κq q) m hmk hres)
  have hle := nodup_length_le _ hnd hsub
  rw [List.length_append, length_expand, List.length_singleton] at hle
  exact Nat.le_trans hle (len_Ures n qi t (κq q))

/-! ### Theorem B (3b): polylogarithmic growth -/

/-- Values of far ends of chains of r odd steps with all exponents ≤ B. -/
def Gval (q B t : Nat) : Nat → List Nat
  | 0 => [t]
  | r + 1 => expand (B + 1) (fun j w => (2 ^ j * w - 1) / q) (Gval q B t r)

def Vval (q B t : Nat) : Nat → List Nat
  | 0 => Gval q B t 0
  | r + 1 => Vval q B t r ++ Gval q B t (r + 1)

theorem len_Gval (q B t : Nat) : ∀ r, (Gval q B t r).length = (B + 1) ^ r
  | 0 => rfl
  | r + 1 => by
    unfold Gval
    rw [length_expand, len_Gval q B t r, Nat.pow_succ, Nat.mul_comm]

theorem len_Vval (q B t : Nat) : ∀ r, (Vval q B t r).length ≤ (r + 1) * (B + 1) ^ r
  | 0 => by simp [Vval, Gval]
  | r + 1 => by
    unfold Vval
    rw [List.length_append, len_Gval]
    have h1 := len_Vval q B t r
    have h2 : (B + 1) ^ r ≤ (B + 1) ^ (r + 1) := Nat.pow_le_pow_right (Nat.succ_pos B) (by omega)
    have h3 := Nat.mul_le_mul_left (r + 1) h2
    rw [Nat.add_mul (r + 1) 1, Nat.one_mul]
    omega

theorem Gval_sub_Vval {q B t x : Nat} : ∀ R r, r ≤ R → x ∈ Gval q B t r → x ∈ Vval q B t R
  | 0, r, hr, hx => by
    have : r = 0 := by omega
    subst this; exact hx
  | R + 1, r, hr, hx => by
    unfold Vval
    match Nat.lt_or_ge r (R + 1) with
    | Or.inl hlt => exact List.mem_append.mpr (Or.inl (Gval_sub_Vval R r (by omega) hx))
    | Or.inr hge =>
      have : r = R + 1 := by omega
      subst this
      exact List.mem_append.mpr (Or.inr hx)

theorem node_pos {t : Nat} {w : Nat → Nat} {q m : Nat} {k : Nat → Nat} (ht : 1 ≤ t)
    (hch : Chain q t m w k) : ∀ l, l ≤ m → 1 ≤ node t w l
  | 0, _ => by simp only [node, ↓reduceIte]; exact ht
  | l + 1, h => by
    have hne : ¬ (l + 1 = 0) := by omega
    simp only [node, hne, ↓reduceIte]
    exact (hch.1 (l + 1) (by omega) h).2

theorem chain_val {q t m B : Nat} {w k : Nat → Nat} (hq0 : 0 < q) (hch : Chain q t m w k)
    (hB : ∀ l, 1 ≤ l → l ≤ m → k l ≤ B) : ∀ r, r ≤ m → node t w r ∈ Gval q B t r
  | 0, _ => by simp [node, Gval]
  | r + 1, h => by
    have hrel := node_rel hch r (by omega)
    have ih := chain_val hq0 hch hB r (by omega)
    have hne : ¬ (r + 1 = 0) := by omega
    have hnode : node t w (r + 1) = w (r + 1) := by simp only [node, hne, ↓reduceIte]
    rw [hnode]
    unfold Gval
    have e : w (r + 1) = (2 ^ k (r + 1) * node t w r - 1) / q := by
      have e1 : 2 ^ k (r + 1) * node t w r - 1 = q * w (r + 1) := by omega
      rw [e1, Nat.mul_div_cancel_left _ hq0]
    rw [e]
    exact mem_expand (g := fun j w => (2 ^ j * w - 1) / q) (Nat.lt_succ_of_le (hB (r + 1) (by omega) h)) ih

/-- One odd step: 2^j ≤ 2q·w and y ≤ 2q·w when q·w + 1 = 2^j·y with w, y ≥ 1. -/
theorem step_le {q w y j : Nat} (hw : 1 ≤ w) (hy : 1 ≤ y) (hq : 1 ≤ q) (h : q * w + 1 = 2 ^ j * y) :
    2 ^ j ≤ 2 * q * w ∧ y ≤ 2 * q * w := by
  have hqw : 1 ≤ q * w := Nat.mul_pos hq hw
  have e : 2 * q * w = q * w + q * w := by rw [Nat.mul_assoc, Nat.two_mul]
  have h1 : 2 ^ j ≤ 2 ^ j * y := Nat.le_mul_of_pos_right _ hy
  have h2 : y ≤ 2 ^ j * y := Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.succ_pos 1))
  have hb : q * w + 1 ≤ 2 * q * w := by rw [e]; exact Nat.add_le_add_left hqw _
  rw [← h] at h1 h2
  exact ⟨Nat.le_trans h1 hb, Nat.le_trans h2 hb⟩

theorem node_le {q t m : Nat} {w k : Nat → Nat} (hq : 1 ≤ q) (ht : 1 ≤ t)
    (hch : Chain q t m w k) : ∀ d l, l + d = m → node t w l ≤ (2 * q) ^ d * node t w m
  | 0, l, h => by rw [Nat.add_zero] at h; subst h; rw [Nat.pow_zero, Nat.one_mul]; exact Nat.le_refl _
  | d + 1, l, h => by
    have hrel := node_rel hch l (by omega)
    have hne : ¬ (l + 1 = 0) := by omega
    have hn1 : node t w (l + 1) = w (l + 1) := by simp only [node, hne, ↓reduceIte]
    have hw := (hch.1 (l + 1) (by omega) (by omega)).2
    have hs := (step_le hw (node_pos ht hch l (by omega)) hq hrel).2
    have ih := node_le hq ht hch d (l + 1) (by omega)
    rw [hn1] at ih
    calc node t w l ≤ 2 * q * w (l + 1) := hs
      _ ≤ 2 * q * ((2 * q) ^ d * node t w m) := Nat.mul_le_mul_left _ ih
      _ = (2 * q) ^ (d + 1) * node t w m := by
        rw [Nat.pow_succ]; simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Theorem B (3b): |R_q(t) ∩ [1, X]| ≤ C (log₂ X + 1)^{κ+1}, uniformly in t. -/
theorem growth {q : Nat} (hq : 1 < q) (hodd : q % 2 = 1) :
    ∃ C, ∀ t, 1 ≤ t → NoH q t → ∀ X, 2 ≤ X → ∀ L : List Nat, L.Nodup →
      (∀ x ∈ L, 1 ≤ x ∧ x ≤ X ∧ Reaches q x t) →
      L.length ≤ C * (Nat.log2 X + 1) ^ (κq q + 1) := by
  refine ⟨(κq q + 1) * (Nat.log2 ((2 * q) ^ (κq q + 1)) + 2) ^ (κq q + 1), ?_⟩
  intro t ht hNoH X hX L hnd hL
  have hP1 : 1 ≤ (2 * q) ^ (κq q + 1) := Nat.pow_pos (by omega)
  have hPX : (2 * q) ^ (κq q + 1) * X ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hP1 (by omega))
  have hXle : X ≤ (2 * q) ^ (κq q + 1) * X := Nat.le_mul_of_pos_left _ hP1
  have hexp : ∀ j, 2 ^ j ≤ (2 * q) ^ (κq q + 1) * X → j ≤ Nat.log2 ((2 * q) ^ (κq q + 1) * X) :=
    fun j hj => (Nat.le_log2 hPX).mpr hj
  have hsub : ∀ y ∈ L, y ∈ expand (Nat.log2 ((2 * q) ^ (κq q + 1) * X) + 1) (fun e w => 2 ^ e * w)
      (Vval q (Nat.log2 ((2 * q) ^ (κq q + 1) * X)) t (κq q)) := by
    intro y hy
    obtain ⟨hy1, hyX, N, hN⟩ := hL y hy
    rcases reaches_decomp hq hodd t ht N y hN with hx | ⟨m, w, k, k0, hm, hch, hx⟩
    · have h2 : 2 ^ N ≤ y := by rw [hx]; exact Nat.le_mul_of_pos_right _ ht
      rw [hx]
      exact mem_expand (Nat.lt_succ_of_le (hexp N (by omega)))
        (Gval_sub_Vval (κq q) 0 (Nat.zero_le _) (by simp [Gval]))
    · have hmk := depth_bound hq hodd ht hNoH hch
      have hwm := (hch.1 m hm (Nat.le_refl m)).2
      have hne : ¬ (m = 0) := by omega
      have hnm : node t w m = w m := by simp only [node, hne, ↓reduceIte]
      have hwy : w m ≤ y := by rw [hx]; exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))
      have hB : ∀ l, 1 ≤ l → l ≤ m → k l ≤ Nat.log2 ((2 * q) ^ (κq q + 1) * X) := by
        intro l hl1 hlm
        apply hexp
        have hrel := node_rel hch (l - 1) (by omega)
        have e : l - 1 + 1 = l := by omega
        rw [e] at hrel
        have hwl := (hch.1 l hl1 hlm).2
        have hs := (step_le hwl (node_pos ht hch (l - 1) (by omega)) (by omega) hrel).1
        have hnl := node_le (by omega) ht hch (m - l) l (by omega)
        have hne' : ¬ (l = 0) := by omega
        simp only [node, hne', hne, ↓reduceIte] at hnl
        have hpow : (2 * q) ^ (m - l + 1) ≤ (2 * q) ^ (κq q + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        calc 2 ^ k l ≤ 2 * q * w l := hs
          _ ≤ 2 * q * ((2 * q) ^ (m - l) * w m) := Nat.mul_le_mul_left _ hnl
          _ = (2 * q) ^ (m - l + 1) * w m := by
            rw [Nat.pow_succ]; simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          _ ≤ (2 * q) ^ (κq q + 1) * X := Nat.mul_le_mul hpow (Nat.le_trans hwy hyX)
      have hval := chain_val (by omega) hch hB m (Nat.le_refl m)
      rw [hnm] at hval
      have hk0 : 2 ^ k0 ≤ y := by rw [hx]; exact Nat.le_mul_of_pos_right _ hwm
      rw [hx]
      exact mem_expand (Nat.lt_succ_of_le (hexp k0 (by omega))) (Gval_sub_Vval (κq q) m hmk hval)
  have hle := nodup_length_le _ hnd hsub
  rw [length_expand] at hle
  generalize hBdef : Nat.log2 ((2 * q) ^ (κq q + 1) * X) = B at hle
  have hV := len_Vval q B t (κq q)
  -- B + 1 ≤ (log₂ P + 2)(log₂ X + 1)
  have hBle : B + 1 ≤ (Nat.log2 ((2 * q) ^ (κq q + 1)) + 2) * (Nat.log2 X + 1) := by
    have hlt : Nat.log2 ((2 * q) ^ (κq q + 1) * X) <
        Nat.log2 ((2 * q) ^ (κq q + 1)) + Nat.log2 X + 2 := by
      apply (Nat.log2_lt hPX).mpr
      have h1 := @Nat.lt_log2_self ((2 * q) ^ (κq q + 1))
      have h2 := @Nat.lt_log2_self X
      have e : 2 ^ (Nat.log2 ((2 * q) ^ (κq q + 1)) + Nat.log2 X + 2) =
          2 ^ (Nat.log2 ((2 * q) ^ (κq q + 1)) + 1) * 2 ^ (Nat.log2 X + 1) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [e]
      exact Nat.mul_lt_mul_of_lt_of_lt h1 h2
    rw [hBdef] at hlt
    generalize Nat.log2 ((2 * q) ^ (κq q + 1)) = a at hlt ⊢
    generalize Nat.log2 X = b at hlt ⊢
    have e : (a + 2) * (b + 1) = a * b + a + 2 * b + 2 := by nat_ring
    omega
  calc L.length ≤ (B + 1) * ((κq q + 1) * (B + 1) ^ κq q) := Nat.le_trans hle (Nat.mul_le_mul_left _ hV)
    _ = (κq q + 1) * (B + 1) ^ (κq q + 1) := by
      rw [Nat.pow_succ]; simp only [Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (κq q + 1) * ((Nat.log2 ((2 * q) ^ (κq q + 1)) + 2) * (Nat.log2 X + 1)) ^ (κq q + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hBle _)
    _ = (κq q + 1) * (Nat.log2 ((2 * q) ^ (κq q + 1)) + 2) ^ (κq q + 1) * (Nat.log2 X + 1) ^ (κq q + 1) := by
      rw [Nat.mul_pow, Nat.mul_assoc]

/-- Theorem B. -/
theorem general_theorem_B {q : Nat} (hq : 1 < q) (hodd : q % 2 = 1) : TheoremB q :=
  ⟨fun _ ht hNoH =>
    ⟨fun _ _ _ _ hch => depth_bound hq hodd ht hNoH hch,
     fun n hn L hnd hL => sparsity hq hodd ht hNoH n hn L hnd hL,
     fun _ hR => no_periodic hq hodd ht hNoH hR⟩,
   growth hq hodd⟩

end Collatz
