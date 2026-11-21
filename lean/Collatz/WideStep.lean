import Collatz.IntegerLifting

namespace Collatz

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


end Collatz
