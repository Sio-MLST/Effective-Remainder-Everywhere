import Collatz.DelayChain

namespace Collatz

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


end Collatz
