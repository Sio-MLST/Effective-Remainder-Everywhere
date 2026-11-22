# Research notes for `qx1-density-dichotomy`

Companion to `paper.md`, `SUPPLEMENTS_A.md` and `SUPPLEMENTS_B.md`. This file collects four things the other files lack: the completed algorithm for $\kappa_{\mathrm{trap}}$, a correction to Theorem B10, the results of checking [Mon06] and [MMMM13] against `SUPPLEMENTS_B.md`, and working notes for later sessions. Nothing here is formalized in Lean 4.35, and `paper.md` depends on none of it. Labels **[P]**, **[P\*]**, **[C]**, **[L]**, **[R]** are as in `SUPPLEMENTS_B.md`.

**Provenance.** A draft of this file was written by another model (Gemini). It was then checked against both PDFs and the repository files, and the computations were re-run with `scripts/kappa_trap.py`. The review confirmed most of the draft. It also found that Theorem B10 is wrong and that [MMMM13, Theorem 3.1] has a misprint or error, both missed by the draft. A few of the draft's claims could not be checked; they are labelled **[L]** below, and §6 lists what was changed.

---

## 1. Computing $\kappa_{\mathrm{trap}}$ and $\delta_{\mathrm{dense}}$ with $e_0 \cdot u_q^*$ evaluations per step

This completes `SUPPLEMENTS_B.md` §5.2 and L11.

### 1.1 Closed form modulo $u_q^*$ [P]

Write $q = q_* q'$ with $q_* = \prod_{p \mid u_q^*} p^{\alpha_p}$ and $\gcd(q', u_q^*) = 1$, and put $u'_q = \prod_{p \mid u_q^*} p^{\nu_p} = q_* u_q^*$.
- **Only $a \bmod e_0$ matters.** A prime $p \mid u_q$ with $p \nmid u_q^*$ has $\nu_p \le \alpha_p$, so $p^{\nu_p} \mid g_0$. Hence $\mathrm{lcm}(g_0, u'_q) = u_q$. Since $u_q \mid 2^d - 1$, the number $e_0 := \mathrm{ord}_{u_q}(2)$ equals the $\mathrm{ord}_{\mathrm{lcm}(g_0,u_q)}(2)$ of B7 and divides $d$. So the conditions in B7 depend only on $a \bmod e_0$.
- **One formula for all $p \mid u_q^*$.** Fix $a$ and a residue $b \in \mathbb{Z}/u_q$ with $2^a b \equiv 1 \pmod{g_0}$. Then $q_* \mid g_0 \mid 2^a b - 1$. B7(2) at every $p \mid u_q^*$ at once says that the successors' $c_0$ lie over the single class
$$r^*(a, b) = \frac{(2^a b - 1) \bmod u'_q}{q_*} \cdot (q')^{-1} \pmod{u_q^*}.$$

### 1.2 Fixed-point iteration [P]

Let $R_k \subseteq \mathbb{Z}/u_q$ be the set of values $c_0(z)$ of vertices $z$ that have a path of length $\ge k$. By B7 this set is well defined.
1. $R_0 = \mathbb{Z}/u_q$.
2. Let $S_{k-1} = R_{k-1} \bmod u_q^*$. Then $b \in R_k$ iff $b \in R_{k-1}$ and some $a \in \{0, \dots, e_0 - 1\}$ has $b \equiv 2^{-a} \pmod{g_0}$ and $r^*(a, b) \in S_{k-1}$. This uses B7(1): the successors realize *all* $g_0$ lifts of $r^*$.
3. For each $a$, the compatible $b$ are the $u_q^*$ lifts $2^{-a} + j g_0$. So a step costs at most $e_0 \cdot u_q^*$ evaluations.
4. Readout. Each residue mod $u_q$ is $c_0$ of exactly $d$ vertices (B4(2)), so $|V_q| = d u_q$. When $\kappa \ge 1$,
$$\kappa_{\mathrm{trap}}(q) = 1 + \max\bigl(\{0\} \cup \{k \in [1, \kappa - 1] : R_k \setminus R_{k+1} \ne \varnothing\}\bigr), \qquad \delta_{\mathrm{dense}}(q) = \frac{d}{q} \cdot \frac{|R_\kappa|}{u_q}.$$

### 1.3 Results [C]

The table was computed with `scripts/kappa_trap.py`. In the rows marked "yes", the iteration agrees set-for-set with an independent brute-force residue graph, built from explicit CRT lifts and $c_0 = (2^a z' - 1)/q$ without the closed form.

| $q$ | $d$ | $u_q$ | $g_0$ | $\kappa$ | $\lvert R_0\rvert, \dots, \lvert R_\kappa\rvert$ | $e_0 u_q^*$ | $\kappa_{\mathrm{trap}}$ | $\delta_{\mathrm{dense}}$ | brute force agrees |
|---|---|---|---|---|---|---|---|---|---|
| 21 | 6 | 3 | 3 | 1 | 3, 2 | 2 | 1 | 4/21 | yes |
| 57 | 18 | 9 | 3 | 2 | 9, 6, 6 | 18 | 1 | 4/19 | yes |
| 7959 | 378 | 189 | 21 | 3 | 189, 54, 36, 36 | 162 | 2 | 24/2653 | yes |
| 10533 | 3510 | 94797 | 10533 | 3 | 94797, 31590, 21060, 21060 | 31590 | 2 | 912600/12327121 | not run (too large) |
| 10887 | 1710 | 171 | 57 | 2 | 171, 54, 36 | 54 | 2 | 120/3629 | yes |
| 11571 | 252 | 63 | 21 | 2 | 63, 18, 12 | 18 | 2 | 16/3857 | yes |

These numbers settle several items in `SUPPLEMENTS_B.md`:
- **L11's counts.** $18$ for 11571 and $54$ for 10887 are confirmed.
- **The 11571 vertex counts in §5.5.** $252 \cdot 18 = 4536$ vertices have out-degree $\ge 1$, $252 \cdot 6 = 1512$ are trapped at depth exactly 2, and $\delta_{\mathrm{dense}} = 16/3857$.
- **$\delta_{\mathrm{dense}}(57) = 4/19$** (B6) is confirmed.

*Do not form $2^d - 1$.* Compute $\nu_p$ by raising $k$ while `pow(2, d, p**(k+1)) == 1`, or by Lemma 1(2).

---

## 2. Theorem B10 is wrong: $10533 = 3 \cdot 3511$ has $\kappa_{\mathrm{trap}} = 2$ [R]

**Uncapped scan [C].** §7 of `SUPPLEMENTS_B.md` lists this scan as not done. It covers all odd $q \le 12000$ with $\kappa \ge 2$ (280 values) and does not assume Rule 2. It finds $\kappa_{\mathrm{trap}} \ge 2$ for exactly
$$7959,\ 10533,\ 10887,\ 11571,$$
each with $\kappa_{\mathrm{trap}} = 2$. So 7959 is still the smallest, but B10's list omits $10533$. To reproduce: `python3 scripts/kappa_trap.py --scan 12000`.

**Proof by hand that $\kappa_{\mathrm{trap}}(10533) \ge 2$ [P].** The argument is the one of L3.
- *Parameters.* $3511$ is a Wieferich prime with $\mathrm{ord}_{3511}(2) = 1755 = 3^3 \cdot 5 \cdot 13$, so $d = 3510$. The order of 2 mod 3 is 2, so $v_3(2^{3510} - 1) = 1 + v_3(1755) = 4$ and $\nu_3 = 3$. Also $v_{3511}(2^{3510} - 1) = 2$, so $\nu_{3511} = 1$. Hence $u_q = 27 \cdot 3511$, $g_0 = q$, $u_q^* = 9$ and $\kappa = 3$.
- *A suitable vertex exists.* By B4(2) some $t \in V_q$ has $c_0(t) \equiv 1 \pmod{u_q}$.
- *It has a successor.* A successor $z'$ needs $2^{-a} \equiv 1 \pmod{g_0}$, that is $3510 \mid a$, which is possible.
- *Every successor is a dead end.* For any successor, $a = d$ and $z' \equiv 1 \pmod{27}$, while $2^d \equiv 1 \pmod{81}$. So $27 \mid 2^d z' - 1$, and since $3 \parallel q$, $c_0(z') \equiv 0 \pmod 9$. A non-unit has out-degree $0$ by B4(1).
- Hence $m(t) = 2 < \kappa$. The computation of §1.3 gives equality, $\kappa_{\mathrm{trap}} = 2$, within the bound $1 + \lceil M_1/\alpha \rceil = 3$ of B9 ($\delta_3 = 3$, $\nu_3 - \alpha_3 = 2$).

**Where the proof of B10 fails.** In its "Case $p$ non-Wieferich", the proof says "$p_1 \mid g_0$ forces $p_1 \mid d$". That is false when $p_1$ is itself a Wieferich prime: then $\nu_{p_1} \ge 1$ holds automatically and $p_1 \nmid d$. Here $p = 3$, $p_1 = 3511$, and $3 \mid \mathrm{ord}_{3511}(2)$ supplies the locking. The "Case $p$ Wieferich" covers only a Wieferich $p \mid u_q^*$, not a Wieferich locking prime.

**Surviving form.** *7959 is the smallest odd $q$ with $\kappa_{\mathrm{trap}} \ge 2$, and below $12000$ the multipliers with $\kappa_{\mathrm{trap}} \ge 2$ are exactly $7959, 10533, 10887, 11571$.* This is **[C]**: it rests on the scan, and the iteration was cross-checked by brute force on the five rows marked "yes" above. To make it a hand proof, the enumeration must add a case for a Wieferich locking prime $p_1 \in \{1093, 3511\}$. ($1093$ has $\mathrm{ord}_{1093}(2) = 364 = 2^2 \cdot 7 \cdot 13$, so $3 \nmid 364$; it could lock $p = 7$ or $p = 13$, but not $p = 3$.)

---

## 3. What [Mon06] and [MMMM13] actually say

### 3.1 Bibliography (the entries in `SUPPLEMENTS_B.md` are wrong)
- **[Mon06]** K. M. Monks, *The sufficiency of arithmetic progressions for the $3x+1$ conjecture*, Proc. Amer. Math. Soc. **134** (10) (2006) 2861–2872. (The repository gave the title as "Sufficient sets for the $3x+1$ problem".)
- **[MMMM13]** Keenan Monks, Kenneth G. Monks, Kenneth M. Monks, Maria Monks, *Strongly sufficient sets and the distribution of arithmetic sequences in the $3x+1$ graph*, Discrete Math. **313** (2013) 468–489. (The repository's author list was garbled.)

### 3.2 The citation checks
- **B1(3) and [Mon06]: they match [P].** [Mon06] §1 defines *merges* and *sufficient for $f$ on $X$*. Theorem 1.1 says every $A + B\mathbb{N}$ with $B \ne 0$ is sufficient for the compressed map $T$. B1(3) uses the same notion for $\mathrm{Col}_q$ (merging is unaffected by compressing). [Mon06] Corollaries 1.2–1.3 (Divergent Orbits, Nontrivial Cycles) follow from sufficiency by a three-line merge argument, so they hold for every odd $q$ given B1(3).
- **Strong sufficiency: the paraphrase matches, but $\widetilde V_q$ should not be called that.** [MMMM13] §6 (p. 478) defines $S$ as *strongly sufficient* if it is
  - *forward sufficient*: it meets every divergent $T$-orbit;
  - *cycle sufficient*: it meets every nontrivial cycle;
  - *backward sufficient*: for every $x$ with $3 \nmid x$, every element of $\widetilde{\mathcal I}_x$ with an irrational back-tracing parity vector meets $S$.

  So `SUPPLEMENTS_B.md` §2's paraphrase is accurate, and B2(2) proves the analogous three properties for $\widetilde V_q$. In [MMMM13], however, $\{x : 3 \nmid x\}$ is the *ambient* pruned graph, and the term is used for residue sets such as $2 \bmod 9$ and $20 \bmod 27$ that are thinner than it. The faithful wording is: *$\widetilde V_q$ is the $q$-analogue of [MMMM13]'s pruned graph, and it has the three properties.*

### 3.3 L10: transferring Proposition 6.5 needs three corrections
[MMMM13] Proposition 6.5 (pp. 482–483) works on a finite quotient: $\Gamma''_d$, the graph mod $d$ with the residues $a_i$ deleted, then pruned to edges that lie on cycles. Its parts are: (a) if every simple cycle has red fraction $< \ln 2/\ln 3$, the set is forward sufficient; (b) if every simple cycle has red fraction $> \ln 2/\ln 3$, it is backward sufficient; (c) if each component has all fractions $> \ln 2/\ln 3$ or all $< \ln 2/\ln(3 + 2^{-60})$, it is cycle sufficient. Moving this to $q > 3$ needs three corrections:
1. **Threshold depends on the map [P].** Red arrows in [MMMM13] are compressed steps $(3x+1)/2$. For $T_q(x) = (qx+1)/2$ the threshold is $\ln 2/\ln q$. In the uncompressed $\mathrm{Col}_q$ convention of B2, a red fraction $r$ becomes an odd-step fraction $r/(1+r)$, so the threshold is $\ln 2/\ln(2q)$. L10's "$\ln 2/\ln q$" is right only for the compressed graph.
2. **Domain.** For $q > 3$, the analogue of $\Gamma''_d$ needs $N_q \mid d$, with the classes projecting to $\mathcal T_q$ removed.
3. **Part (c) does not transfer as stated [P]/[C].** Its proof uses the verification of $3x+1$ below $2^{60}$, so that a cycle's minimal element is huge (via Proposition 6.3(b)). For $q = 5$ small cycles exist. Under $T_5$:
   - $\{1, 3, 8, 4, 2\}$ has red fraction $2/5$;
   - $\{13, 33, 83, 208, 104, 52, 26\}$ has red fraction $3/7 \approx 0.4286$, between $\ln 2/\ln(5 + 1/13) \approx 0.4266$ and $\ln 2/\ln 5 \approx 0.4307$, as Proposition 6.3(b) requires.

   So for $q \ge 5$ the lower threshold must be $\ln 2/\ln(q + 1/m_0)$, where $m_0$ is a verified lower bound for minimal elements of cycles not yet listed. Every known cycle must also be listed and checked against $S$ separately.
- **[L] What remains for (a) and (b).** Their proofs are the mediant argument, which is independent of $q$, together with Proposition 6.3(a),(c): odd fractions of divergent orbits and of aperiodic back-tracing sequences. The $q$-analogues of 6.3(a),(c), with $\ln 2/\ln q$, are plausible but have not been proved here. Until they are, (a) and (b) do not "transfer cleanly".

### 3.4 Other results of [MMMM13] for general odd $q$
1. **The translation identity holds for every odd $q$ [P].** Let $T_0(x) = x/2$ and $T_{1,q}(x) = (qx+1)/2$ act on $\mathbb{Z}/b$ with $\gcd(b, 2q) = 1$. Then
$$T_0^{-2}\, T_{1,q}\, T_0\, T_{1,q}^{-1}\, T_0(x) = x + 1,$$
because $T_{1,q}^{-1}(x/2) = (x-1)/q$, then $(x-1)/(2q)$, then $(x+1)/4$, then $x + 1$. This is [MMMM13] (3.1) with $3$ replaced by $q$. Hence $G_{q,b} = \langle x \mapsto x+1,\ 2x,\ qx \rangle \cong C_b \rtimes M_{q,b}$, where $M_{q,b}$ is the subgroup of $(\mathbb{Z}/b)^\times$ generated by $2$ and $q$.
2. **[MMMM13] Theorem 3.1 is wrong as printed [C].** The theorem says $M = C_{a_1} \times \dots \times C_{a_n}$, with $a_i = \mathrm{lcm}(\mathrm{ord}_{p_i^{e_i}}(2), \mathrm{ord}_{p_i^{e_i}}(3))$. Its proof computes $\langle 2, 3 \rangle$ separately in each CRT component and then takes the direct product. But the subgroup generated by the diagonal elements can be smaller. For $b = 95$, $\lvert\langle 2, 3 \rangle\rvert = 36$ while $\prod a_i = 4 \cdot 18 = 72$. Other failures: $b = 119, 143, 145, 215, \dots$ The correct statement is $M$ = the subgroup of $(\mathbb{Z}/b)^\times$ generated by $2$ and $3$. Cite this form, not "Theorem 3.1 verbatim". Whether Theorem 4.1 depends on the product form has not been checked.
3. **Density-zero sufficient sets [P].** [MMMM13] Theorem 2.1 and Corollary 2.2 use only sufficiency of arithmetic progressions and the fact that $y$ merges with $2^k y$. With B1(3) they hold for every odd $q$: $\{(a + dn) 2^{f(n)}\}$ is sufficient, and has density $0$ for $f(n) = n$.
4. **Theorem 4.4 compared with S4.** [MMMM13] Theorem 4.4 achieves at most one $T_1^{-1}$ step when 2 is a primitive root mod $p^r$, but only for targets $a$ prime to $p$. Its second case uses a mod-9 adjustment specific to $q = 3$. `SUPPLEMENTS_A.md` S4 maps any $z$ to any $y$ mod $p^r$, including $p \mid y$, where halvings alone cannot help. This plausibly explains the two odd steps, but it is not a proof that two are needed.
5. **[L] Self-color-duality and folding (§7).** For $q = 3$ the proofs go through the 2-adic conjugacy $\Phi$ with the shift. For odd $q$, $T_q$ is also conjugate to the shift on $\mathbb{Z}_2$, so the "if" direction of Theorem 7.1 and the folding of Theorem 7.3 may carry over. Neither has been checked, and the "only if" direction ($k = 2^n$) is not addressed.

### 3.5 Terminology
Keep `paper.md`'s notation everywhere. Use Monks's words (*merges*, *sufficient*, *forward/cycle/backward/strongly sufficient*, *back-tracing parity vector*) only in B1, B2 and L10. Watch for clashes: in [Mon06]/[MMMM13], $d$ is a modulus ($\Gamma_d$, $a + dn$), $q$ is a cycle length (Theorem 7.3), $m$ is a cycle's minimal element, and $T$ is the compressed map. In this project, $d = \mathrm{ord}_q(2)$, $q$ is the multiplier, and $\mathrm{Col}_q$ is uncompressed.

---

## 4. Leads for the next session [L]

1. **L2 against B9.** Build $q = 57 \cdot r_1 \cdots$ with $27 \mid d$ (so $\nu_3 \ge 3$), $19 \mid d$ and $\nu_{19} = 1$, so $g_0 = 57$ and $\delta_3 = 2$. Then run §1.2. If $\kappa_{\mathrm{trap}} = 3$, L2 is refuted. If it is $2$, the "free lift mod $p_1$" mechanism should be made into a proof. (10887 has $g_0 = 57$ but $\nu_3 - \alpha_3 = 1$, so it does not decide this.)
2. **L1 chain $3 \leftarrow 19 \leftarrow p_2$.** We have $\mathrm{lcm}(\mathrm{ord}_{27}(2), \mathrm{ord}_{361}(2)) = \mathrm{lcm}(18, 342) = 342$, and any primitive prime divisor of $\Phi_{342}(2)$ has order exactly $342$. Add auxiliary primes giving $27 \mid d$, $361 \mid d$ and $p_2 \mid d$, then run §1.2. The values of $u_q$ may be large; the cost is $e_0 u_q^*$ per step and $\lvert R_k\rvert \le u_q$ in memory.
3. **Wieferich locking primes.** 10533 shows that a Wieferich $p_1$ enters $g_0$ without dividing $d$, which makes locking cheap. Test $q = 3^\alpha \cdot 3511 \cdots$ and $7 \cdot 1093 \cdots$, $13 \cdot 1093 \cdots$ for depth $\ge 3$. This bears on L6: the locking graph must allow $p_1 \mid g_0$ through $\nu_{p_1} \ge 1$ as well as through $p_1 \mid d$.
4. **L5 (several primes in $u_q^*$).** The scan code handles this case directly; extend `--scan` beyond $12000$ while filtering for $\omega(u_q^*) \ge 2$.
5. **`SUPPLEMENTS_A.md` Q4 ($\kappa \ge 1$).** S1's one-odd-step witnesses fail when $\kappa \ge 1$, because $c_0 \bmod u_q$ is fixed in one step (Lemma 2(2)). A plausible route has two stages. First, a primer stage: Proposition 1, then Lemma 6, to reach (H) and a congruence modulo $q^{K+1} u_q$. Second, the $\kappa = 0$ constructions, entered through Lemma 13. `paper.md` Lemma 3 already states the bound $\gamma \le \lambda_H \lceil \log_2(m'+1) \rceil$, unformalized, which is S5's mechanism. None of this has been carried out.
6. **Lean 4.35 (Q5).** Core only, no Mathlib, axioms `[propext, Quot.sound]`. Reuse `paper.md`'s ways of avoiding CRT: the single modulus $D_m$ in Proposition 1, and the weights $E_p^*$ (`GeneralAOp`, `GeneralAStage`, `GeneralASelect`). Check `#print axioms` for every new top-level theorem, and keep hypotheses out of structure fields.
7. **Still unchecked.** OEIS A182297 and Franco–Pomerance against the Wieferich-type family; $21$ fails $q^2 \mid 2^{\varphi(q)} - 1$.

---

## 5. Working practice

- Before a scan, name its possible outcomes. Run it only if they lead to different next steps. The scan of §2 passed this test: it could, and did, refute B10.
- A capped search proves nothing about what the cap excludes. Scan 1 ($N_q \le 4 \cdot 10^5$) hid all the depth-2 cases. B10's hand enumeration was "checked once" and still missed 10533.
- Check a hand derivation with a small script, and check a script against the algebra. Index slips such as $p^{\alpha+1}$ versus $p^{2\alpha}$, and confusing exponents with Lemma 2's index $j$, have occurred before.
- Read the primary sources when they are available. Reading them here caught L10's map convention, the role of $2^{60}$ in Proposition 6.5(c), the bibliography errors, and the error in [MMMM13] Theorem 3.1.
- Keep refuted claims in the ledger, with the counterexample and any surviving weaker form.

---

## 6. Changes from the Gemini draft

- **Added:** the counterexample $10533$ and the correction to B10 (§2); the brute-force cross-check (§1.3); the error in [MMMM13] Theorem 3.1 (§3.4.2); the bibliography corrections (§3.1).
- **Weakened:** "Proposition 6.5(a),(b) transfer cleanly" is now [L], since it depends on unproved analogues of Proposition 6.3. "Theorems 3.1 and 4.1 generalize verbatim" is replaced by the corrected statement. "§7 carries over" is now [L]. "S4 needs two steps precisely to cover $p \mid a$" is now "plausibly explains".
- **Not reproduced:** the draft's account of a `2026-11-21` session log (`scan.py`, `timeout 300`, and the reason the scan stalled). That log is not in this repository, so it could not be checked.
