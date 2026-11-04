# Handoff: Universal Coverage for px+1

Nov 4, 2026 · @André

The goal is one theorem covering px+1 for every non-Wieferich odd prime p, proved on paper first and then formalised in Lean 4.35.0 with the core library only. It should subsume the existing 3x+1 and 5x+1 files as corollaries.

## Goal and target theorem

**Map.** For an odd prime p, let C\_p(n) = n/2 for even n and C\_p(n) = pn + 1 for odd n. Write n ⇝ w if C\_p^k(n) = w for some k ≥ 0.

**Target (universal coverage).** Let p be an odd prime with 2^(p−1) ≢ 1 (mod p²). Let w ≥ 1 with p ∤ w and (w mod p) ∈ ⟨2⟩ ⊆ (ℤ/p)^×. Then for every N ≥ 1, every r and every B, there is n with B < n, n ≡ r (mod N), n ⇝ w, and n ≤ w·2^(2^(F\_p(N,B))) for an explicit F\_p.

Each hypothesis is justified:

- **Non-Wieferich** is exactly the generation step of the period argument (Theorem 1 below). Dropping it is false for some w (see Ruled out).
- **w mod p ∈ ⟨2⟩** is necessary (Theorem 2 below).
- **p ∤ w** is implied by the previous hypothesis. It is stated separately because the Lean files phrase it that way.
- **No primitive-root hypothesis.** Part A shows it is unnecessary at the residue level. Whether Part B needs it is open.

**Corollaries to recover:** p = 3 (current 3x+1 file, 48N⁴ exponent) and p = 5 (`ERE5.lean`, 105N⁵ exponent). New cases include p = 7, 11, 13, 31, 73.

**Success** means a single Lean file parametrised by p whose paper proof was complete before any Lean was written, with standard axioms only.

## Methodology rules

Mathematics comes first; Lean is a verification tool, not the place where the argument is found.

1. **Paper before Lean.** A lemma is formalised only when its natural-language proof is complete, with every hypothesis named. A Lean step that fails sends us back to the paper argument, not into code patching.
2. **Status tags.** Every claim carries one tag: *formalised* (with Lean name), *proved on paper*, *gap*, *conjecture*, or *ruled out*. Conjectures are never used as hypotheses.
3. **Test against the obstruction.** Before believing a general statement, test it against the coset obstruction and the Wieferich case. The 7x+1 slip and the false C2 both came from natural-looking templates.
4. **Check before asserting.** Read the code or the source before describing it. Do not infer what a lemma does from its name.
5. **Statement audit.** After compiling, compare the formal statement with the informal one, definition by definition (map, reachability, bound). A compiling proof of a subtly different statement is the main residual risk.
6. **Modular and elementary.** Keep the `Gen` layer p-generic with a plain interface: congruence as Int divisibility, Nat bridges. Avoid fragile automation on ring goals.
7. **Explicit constants.** Bounds are finite closed formulas, tracked as functions of p, so the exponent's dependence on p becomes visible.

## Environment

Lean 4.35.0, core library only, no Mathlib.

- **Obtaining Lean.** Sandboxes may have `elan` but no toolchain, and `release.lean-lang.org` may be unreachable. Download `lean-4.35.0-linux.tar.zst` from GitHub releases and unpack it with Python `zstandard`, because the system `tar` lacks zstd. Install only when the user asks.
- **Known failures.** `grind` has panicked on some CommRing goals. Prefer `omega`, explicit rewrites and small lemmas.
- **Axioms.** Each file ends with `#print axioms` on its main theorems. Only standard axioms are acceptable.
- **Checking happens on a phone.** Keep files modular and outputs short.

## Established (formalised)

Two maps are fully formalised; the period lemma is already p-generic.

| Result | File · Lean name | Statement |
| --- | --- | --- |
| 5x+1 coverage | `ERE5.lean` · `remainder_bounded` | N ≥ 1, 5 ∤ w, any r, B: some n with B < n ≤ w·2^(2^(21·5N⁵(B+1))), n ≡ r (mod N), n ⇝ w |
| 5x+1 infinitude | `ERE5.lean` · `remainder_infinitely_often` | One-line corollary of the B-form |
| 3x+1 coverage | 3x+1 file · `remainder_bounded` | 3 ∤ w: B < n ≤ w·2^(2^(48N⁴(B+1))). Not yet ported to `Gen` |
| Period lemma | `Gen.period_general` | Odd p, q > 1 coprime to p, a period T, a base loop i₀, generation (hGen) and the loop identity (hB) together give a contradiction |
| LTE order | `Gen.order_iff` | Odd p, p ∤ u: (1+pu)^m ≡ 1 (mod p^(K+1)) iff p^K ∣ m |
| LTE step | `Gen.lte_step`, `Gen.lte` | (1+p^j u)^p = 1 + p^(j+1)w′ with p ∤ w′ |

The 5x+1 proof has three layers: the 2-adic part (`parity_word`), the residue closure mod 5^(K+1)·M (`Closure`, fibres, stabiliser, `translationPeriod_one`, `closure_all`), and the lift to integers with the bound (`closure_word`, `hasWord_all_short`, `exponent_class`, `pow2_period_lift`, `bound_arith`, `hit_residue`).

## Proved on paper (not yet formalised)

The residue-level core holds for every non-Wieferich odd prime and never uses primitivity of 2.

**Notation.** p odd prime, K ≥ 0, P = p^(K+1), M ≥ 1 with gcd(M, 2p) = 1, Q = PM. G = ⟨2⟩ ⊆ (ℤ/P)^×, d = ord\_p(2), U\_j = {u ≡ 1 (mod p^j)} ⊆ (ℤ/P)^×.

### Theorem 1 (generation ⇔ non-Wieferich)

For K ≥ 1 and every m ≥ 0: 1 + p·2^m ∈ G iff 2^(p−1) ≢ 1 (mod p²).

*Proof.* Put x = 1 + p·2^m, so x ∈ U\_1 \\ U\_2. Also G ∩ U\_1 = ⟨2^d⟩. With e = (p−1)/d coprime to p, u ↦ u^e is injective on U\_1/U\_2, so 2^d ∈ U\_2 iff 2^(p−1) ∈ U\_2. U\_1 is cyclic of order p^K with unique index-p subgroup U\_2, and any element outside U\_2 generates it. (⇐) 2^d ∉ U\_2 gives ⟨2^d⟩ = U\_1 ∋ x. (⇒) 2^d ∈ U\_2 gives G ∩ U\_1 ⊆ U\_2, so x ∉ G. ∎

**Fact 0.** Under non-Wieferich, U\_1 ⊆ G. (For K = 0, U\_1 = {1}.)

### Theorem 2 (root condition necessary)

If p ∤ w and (w mod p) ∉ ⟨2⟩, the predecessor set of w under C\_p is {2^k w}, so no predecessor is ≡ 0 (mod p).

*Proof.* The second predecessor of t needs t ≡ 1 (mod p). Each w·2^k lies in the coset w⟨2⟩ ≠ ⟨2⟩, which misses 1. Induct on k. ∎ Example: p = 7, w = 3.

### Part A (residue closure is everything)

**Closure.** X ⊆ ℤ/Q is the least set containing every 2^k w, closed under z ↦ 2z, and containing x whenever z ∈ X and px + 1 = 2z in ℤ/Q (undo). Fibres: F\_a = {t ∈ ℤ/M : (a, t) ∈ X} for a ∈ ℤ/P. Put φ(t) = p^(−1)(2t − 1) on ℤ/M; it is injective.

1. **Doubling.** 2F\_a ⊆ F\_(2a).
2. **Undo.** If pa′ + 1 = 2g in ℤ/P, then φ(F\_g) ⊆ F\_(a′). *Proof:* take x ∈ X over (g, t); by CRT pick y over (a′, φ(t)); then py + 1 = 2x in ℤ/Q.
3. **Rigidity.** F\_(2^m a) = 2^m F\_a for all a, m. *Proof:* with T = ord\_P(2), the injective chain |F\_a| ≤ |F\_(2a)| ≤ … ≤ |F\_(2^T a)| = |F\_a| forces equality.
4. **Exact undo in a coset.** If pa′ + 1 = 2g and g ∈ a′G, then F\_(a′) = φ(F\_g), by equal sizes and Lemma 2.
5. **Non-empty.** F\_1 ≠ ∅: w ≡ 2^j u with u ∈ U\_1 ⊆ G (Fact 0), so 2^k w ≡ 1 (mod P) for some k.
6. **Stabiliser generators.** Stab = bijections h of ℤ/M with h(F\_1) = F\_1, a group. (a) If 2^m ≡ 1 (mod P), then t ↦ 2^m t is in Stab. (b) For every m there is i with 2^(i+1) ≡ p·2^m + 1 (mod P), by Fact 0; then k\_(i,m)(t) = 2^(−m)φ(2^i t) is in Stab, via Lemma 4 with g = 2^i, a′ = 2^m. Fix i₀ for m = 0 and set ℓ = k\_(i₀,0) = ct − v with c = 2^(i₀+1)p^(−1), v = p^(−1).
7. **Commutator.** For k(t) = λt + μ in Stab, the translation by τ = (1 − c)μ + (1 − λ)v is in Stab, since k∘ℓ − ℓ∘k = τ.
8. **Periods.** The translations in Stab form qℤ/M with q ∣ M and gcd(q, 2p) = 1; F\_1 is a union of their cosets.
9. **q = 1.** Suppose q > 1. (A) From 6(a) and 7: 2^m ≡ 1 (mod P) implies 2^m ≡ 1 (mod q). (B) From 6(b) and 7: 2^(i+1) ≡ p·2^m + 1 (mod P) implies p·2^m + 2^(i₀+1) ≡ p + 2^(i+1) (mod q). Descend on j = K+1, …, 0: if 2^m ≡ 1 (mod p^j), then 2^m ≡ 1 (mod q). The base j = K+1 is (A). For the step, pick i from 6(b); then 2^(i+1) ≡ 2^(i₀+1) (mod p^j). With m′ = i + (T−1)i₀, the hypothesis gives 2^i ≡ 2^(i₀) (mod q), and (B) gives 2^m ≡ 1 (mod q). At j = 0, m = 1: q ∣ 1, a contradiction. This is `Gen.period_general` with its hypotheses discharged.

**Theorem A.** X = ℤ/Q. *Proof:* F\_1 = ℤ/M by Lemmas 5, 8 and 9. For a ∈ G, F\_a = 2^m F\_1 = ℤ/M. For any a′, g = (pa′+1)/2 lies in G because pa′ + 1 ∈ U\_1 ⊆ G, so F\_(a′) ⊇ φ(ℤ/M) = ℤ/M by Lemma 2. ∎

Fact 0 is the only use of non-Wieferich. Classes outside G, such as 3 mod 7, are filled by undo moves into G; they are dead-end branches, consistent with Theorem 2.

## Gaps (to work out on paper next)

Part B is the open piece; Part C looks routine but is unwritten.

**Part B: from residue closure to actual integers, with the bound.** In `ERE5.lean` this is `closure_word`, `hasWord_all_short`, `integrality`, `exponent_class`, `pow2_period_lift`, `bound_arith` and `hit_residue`. None of it has been audited for general p. The questions to settle:

- Does any step use more than "2 is a unit mod p^j·M" and Part A? In particular, does any step use primitivity of 2?
- Each undo divides by p, so the p-adic precision K must cover the number of odd steps, while the short-word bound depends on Q = p^(K+1)M. How does the file break this circularity? Read `exponent_class` before writing anything.
- Where does the 5^(K+jv) factor enter `bound_arith`, and what is its p-analogue? Write F\_p(N, B) as a function of p. This answers whether N⁴ versus N⁵ tracks p.

**Part C: the 2-adic prefix.** For odd p, the odd step sends 2y + 1 to 2(py + (p+1)/2), and halving gives py + (p+1)/2. So a parity word of length α fixes n mod 2^α, as `parity_word` does for p = 5. Write this out explicitly.

**Assembly.** Split N = 2^α p^b M with gcd(M, 2p) = 1, take K ≥ b, combine Parts A–C by CRT, and carry the threshold B as in `remainder_bounded`.

## Ruled out

These are settled; do not revisit them without a new argument.

| Claim or route | Status | Reason |
| --- | --- | --- |
| "p ∤ w suffices" | False | p = 7, w = 3: the tree is {3·2^k} (Theorem 2) |
| Coverage at Wieferich primes (old C2) | False for w ∈ ⟨2⟩ mod p² | 2^k w ≡ 1 (mod p) forces ≡ 1 (mod p²), so every odd predecessor is ≡ 0 (mod p) and dead. p = 1093, w = 1 hits 365 of 1093 classes mod p. Checked: ord\_1093(2) = 364 and 2^364 ≡ 1 (mod 1093²); 3511 behaves the same with index 2 |
| "2 must be a primitive root" | Unnecessary in Part A | Only Fact 0 (non-Wieferich) is used |
| Separate q = 3 corner, α-branch | Abandoned | Both are levels of the one descending induction |
| Order-of-16 theory, quintic expansions | Deleted | Replaced by `Gen.order_iff` |
| Mazur's mixing replacing the M-part pigeonhole | Does not apply | His estimate is 3-adic only and says nothing about ℤ/M with gcd(M, 6) = 1 |
| Hallqvist's coverage improving Mazur's 0.90 | Not by itself | Coverage holds for 5x+1, where trees are thin, so it carries no counting information |
| Name-based pruning scripts | Broke the build twice | They missed namespaced and dot-notation uses |

## Reuse map from ERE5.lean

The period core is already generic; the fibre layer needs 5 replaced by p and one hypothesis swapped.

| ERE5 piece | Paper lemma | For general p |
| --- | --- | --- |
| `Gen.*` (`lte`, `order_iff`, `period_general`, `Cong`) | Thm 1 tools, Lemma 9 | Reuse unchanged |
| `Closure`, `Fibre`, `fibre_dbl`, `fibre_undo_iff` | Lemmas 1, 2, 4 | Replace 5 by p and `TwoFiveInvertible` by "2, p invertible mod M" |
| `fibre_cardinality_const` (all live classes) | Lemma 3 | Weaken to cosets of G; it currently relies on 2 generating every unit mod 5^(K+1) |
| `two_generates_live`, `two_pow_mod_eq_one_iff`, `two_pow_inj` | Fact 0 | Replace by Fact 0 from non-Wieferich via `Gen.order_iff` |
| `stabilizer_loop`, `stabilizer_mul`, `stabilizer_affine_translation`, `translationPeriod_*` | Lemmas 6–8 | Replace 5 by p; the special loop uses i₀ with 2^(i₀+1) ≡ p + 1 |
| `translationPeriod_one`, `fibre_full`, `closure_all` | Lemma 9, Theorem A | `fibre_full` must use the new argument for classes outside G |
| `parity_word`, `integrality` | Part C | Replace 10y + 6 → 5y + 3 by its p-version |
| `exponent_class` … `hit_residue` | Part B | Audit on paper first |

## Next steps in order

The first two are paper work; Lean starts only at step 3.

1. **Audit Part B on paper.** Read `exponent_class`, `bound_arith` and `hit_residue`, and rewrite them in natural language for general p. Record exactly which p-facts they use.
2. **Write Part C and the assembly on paper.** Then do a full read-through for gaps against the methodology rules.
3. **Formalise Fact 0** from `Gen.order_iff`, as the general replacement for `two_generates_live`.
4. **Parametrise the fibre and stabiliser layer** by p (Lemmas 1–9), then Theorem A.
5. **Parametrise Part B and Part C**, and assemble the general `remainder_bounded`.
6. **Derive p = 3 and p = 5 as corollaries,** and delete the duplicated 3x+1 machinery.
7. **Audit the formal statement** against the target, and track F\_p(N, B) as a function of p.

A smaller unit of work is available before step 3 if wanted: port `Gen` into the 3x+1 file and make its `remainder_infinitely_often` a one-line corollary of the B-form.

## Inspiration, not hypotheses

These guide choices but are never assumed in a proof.

**Conjectures (corrected):**

- **C2′ (Wieferich, reformulated).** At a Wieferich prime, coverage may hold when w ∉ ⟨2⟩ mod p², because then the first undo lands in a nonzero class. A candidate hypothesis is that w⟨2⟩ mod p^e meets U\_1 \\ U\_2, where e is the level at which ⟨2⟩ ∩ U\_1 stabilises. Low confidence; a residue-level computation for p = 1093 with small M would test it.
- **C3 (shape of the bound).** For fixed p the least witness is polynomial, n ≤ w·N^(c\_p). Singly exponential, w·2^(poly N), is a plausible provable target. Evidence: for N = 3^q, Mazur-style LTE gives n < w·2^(2·3^(q+1)).
- **C4.** c\_p grows roughly like log p / log 2. Speculation.
- **C5 (composite multipliers).** For odd composite a, the statement should split by CRT components of a. Low confidence.
- **C6 (hybrid digits).** Every predecessor tree contains numbers with any prescribed leading and trailing digit blocks at once, via Kronecker equidistribution and 2^(t·ord). Likely and within reach.

**From Mazur (Sept 2026 manuscript, distilled):**

- **Lemma 4.1 (LTE witness).** (4^j − 1)/3 runs through every class mod 3^q. The p-analogue gives singly exponential witnesses for the pure p^b factor of N, but not for M.
- **Lemma 2.1 (injective transfer).** Affine word maps on ℤ/3^t are injective, and weighted transfer conserves mean exactly. This is a template for uniform fibre-size bounds (Wirsching's (⋆3)).
- **Mixing (2.3)** is 3-adic only. A p-adic analogue for Y ↦ 2^(−A)(pY + 1) is plausible, but it would give equidistribution, not the covering in ℤ/M.

**Frontier (dragons):** the pigeonhole loss is structural. Improving the bound means controlling the number of odd steps, which is a sums-of-⟨2⟩ problem in ℤ/M; it is open uniformly in M, for example for M = 2^k − 1. Primes with tiny ord\_p(2), such as 7, 31, 73 and 127, are the stress tests.

## Files to bring

Bring this doc plus two Lean files; leave everything else out.

- **Bring:** this handoff, `ERE5.lean` (the template), and the current 3x+1 Lean file. Add `Period.lean` if it differs from `Gen.period_general`.
- **Leave out:** the older Lean copies (verify by diff first), the survey and its script, the Mazur PDF (distilled above), the people list, and the self-criticism log apart from the mathematical items already in Ruled out.
- **Triage before deciding:** `overview.pdf`, `SpectralDecay_lean.txt` and the simultaneous-primitive-roots PDF, which have not been read. The primitive-roots paper is probably irrelevant now that primitivity is not needed.
