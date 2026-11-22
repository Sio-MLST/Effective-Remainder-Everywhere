# Research notes for `qx1-density-dichotomy`

Companion to `paper.md`, `SUPPLEMENTS_A.md` and `SUPPLEMENTS_B.md`. This file collects four things the other files lack: the completed algorithm for $\kappa_{\mathrm{trap}}$, a correction to Theorem B10, the results of checking [Mon06] and [MMMM13] against `SUPPLEMENTS_B.md`, and working notes for later sessions. Nothing here is formalized in Lean 4.35, and `paper.md` depends on none of it. Labels **[P]**, **[P\*]**, **[C]**, **[L]**, **[R]** are as in `SUPPLEMENTS_B.md`.

**To verify:** `VERIFY.md` lists every claim here with its scope, status, proof inputs and a check ID; `python3 scripts/verify_claims.py [--scan] [--big]` runs all the checks in under 30 s.

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

## 2a. A multiplier with $\kappa_{\mathrm{trap}} = 3$: $q = 3 \cdot 3511 \cdot 21067$ (refutes L2)

Proposed by Gemini after §2, checked here by hand and by computation.

**Parameters [C].** $r = 21067 = 6 \cdot 3511 + 1$ is the least prime $r \equiv 1 \pmod{3511}$ with $3511 \mid \mathrm{ord}_r(2)$. Here $\mathrm{ord}_r(2) = 21066 = 2 \cdot 3 \cdot 3511$, and $r$ is not Wieferich. For $q = 3 \cdot 3511 \cdot 21067 = 221898711$:
- $d = 12323610 = 2 \cdot 3^3 \cdot 5 \cdot 13 \cdot 3511$;
- $\nu_3 = 3$, $\nu_{3511} = 2$ (since 3511 is Wieferich and $3511 \parallel d$), and $\nu_{21067} = 0$;
- so $u_q = 3^3 \cdot 3511^2$, $g_0 = 3 \cdot 3511$ (two primes), $u_q^* = 3^2 \cdot 3511$ and $\kappa = 3$.

**Computation [C].** `python3 scripts/kappa_trap.py --np 221898711` takes 17 s. It gives $\lvert R_k\rvert = 332832267,\ 110912490,\ 36960300,\ 24640200$ for $k = 0, \dots, 3$. Hence $\kappa_{\mathrm{trap}} = 3$ and $\delta_{\mathrm{dense}} = 1067742000/259695458107$. The numpy path reproduces every row of §1.3.

**Proof by hand that $\kappa_{\mathrm{trap}} \ge 3$ [P].** Use only $27 \mid d$, $\nu_{3511} = 2$, $g_0 = 3 \cdot 3511$ and $\kappa \ge 3$.
- *Two facts.* Every exponent $a$ compatible with a residue $\equiv 1 \pmod{g_0}$ is a multiple of $\mathrm{ord}_{g_0}(2) = 3510$. For such $a$, $v_3(2^a - 1) = 1 + v_3(a) \ge 4$ and $v_{3511}(2^a - 1) \ge 2$ (Wieferich).
- *A suitable vertex.* By B4(2) there is $t \in V_q$ with $c_0(t) \equiv 1 + q \pmod{u_q}$.
- *Step 1.* Its successors $z_1$ satisfy $z_1 \equiv 1 + q \pmod{3^3 \cdot 3511^2}$. Their exponents are multiples of 3510, so $2^a z_1 - 1 \equiv q \pmod{3^3 \cdot 3511^2}$. Hence $c_0(z_1) \equiv 1 \pmod{3^2 \cdot 3511}$. In particular $c_0(z_1) \equiv 1 \pmod{g_0}$, so every $z_1$ has out-degree $\ge 1$.
- *Step 2.* The successors $z_2$ of any $z_1$ satisfy $z_2 \equiv 1 \pmod{3^2 \cdot 3511}$. So their exponents are again multiples of 3510, and $2^a \equiv 1 \pmod{81}$. Then $9 \mid 2^a z_2 - 1$, so $c_0(z_2) \equiv 0 \pmod 3$, and $z_2$ has out-degree $0$ by B4(1).
- Hence $L(t) = 2 < \kappa$ and $m(t) = 3$. $\square$

**Why it works.** Without $r$ (that is, $q = 10533$), $\nu_{3511} = 1$. Then $c_0(z_1) \bmod 3511$ is free across the lifts, the second step is not forced, and $\kappa_{\mathrm{trap}} = 2$. Adding $r$ puts $3511 \mid d$, which raises $\nu_{3511}$ to 2 and locks one more step.

**Consequences.**
- **L2 ("two primes in $g_0$ cannot reach depth 3") is refuted** [R]. L2's own argument assumed $\nu_{p_1} = 1$. *Open weaker form:* when $g_0 = p_0 p_1$ and $\nu_{p_1} \le \alpha_{p_1}$, is $\kappa_{\mathrm{trap}} \le 2$? Both 10533 and 10887 are consistent with this.
- **L5 is consistent.** $u_q^* = 3^2 \cdot 3511$ has two primes, so B9 does not apply. L5's conjectured bound is $1 + \max_p \lceil M_1(p)/\alpha_p \rceil$. Here $M_1(3) = \min(\delta_3 = 3,\ 2) = 2$ and $M_1(3511) = \min(1, 1) = 1$, so the bound is $3$, which equals the true value.
- **B9 is not always tight.** At $q = 10533$, B9 gives $3$ but $\kappa_{\mathrm{trap}} = 2$. This qualifies the "tightness" table in `SUPPLEMENTS_B.md` §5.4.
- **Not known:** whether 221898711 is the smallest $q$ with $\kappa_{\mathrm{trap}} \ge 3$. A cheaper construction might use $7 \cdot 1093$ or $13 \cdot 1093$, or other auxiliary primes.

## 2b. Closed form for $\kappa_{\mathrm{trap}}$ when $g_0 = p_0 p_1$ (Gemini; superseded by §2c)

**Status.**
- Formula: **[C]** on every computable case.
- Lower bound: **[P\*]** (read once, by Claude).
- Upper bound: **[L+]**, a complete-looking argument with one step to scrutinize (marked ⚠ below).
- The $\omega_{\mathrm{hi}} \ge 1$ branch: **untested**.

This partly answers L6.

**Definitions.** Assume $\kappa \ge 1$ and $g_0 = p_0 p_1$ with distinct primes, so $\min(\alpha_i, \nu_i) = 1$. Let $o = \mathrm{ord}_{g_0}(2)$, and for $i \in \{0, 1\}$:
- $\sigma_i = \max(0, \nu_i - \alpha_i)$. When $\sigma_i > 0$, this forces $\alpha_i = 1$.
- $\delta_i = v_{p_i}(2^o - 1) - 1$.
- $\omega_i = v_{p_i}(2^{\mathrm{ord}_{p_i}(2)} - 1) - 1$. This is the Wieferich excess: $1$ for $1093$ and $3511$, else $0$.
- $s_i = 0$ if $\sigma_i = 0$, else $\min(\delta_i, \sigma_i)$.

*Locking:* $p_{1-i}$ locks $p_i$ iff $p_i \mid \mathrm{ord}_{p_{1-i}}(2)$, and then $\delta_i = \omega_i + v_{p_i}(\mathrm{ord}_{p_{1-i}}(2))$.

**Formula.**
$$\kappa_{\mathrm{trap}}(q) = L^* := 1 + \min(s_0, s_1) + \begin{cases} 0 & s_0 = s_1,\\ 1 + \min(\omega_{\mathrm{hi}},\ \lvert s_0 - s_1\rvert - 1) & s_0 \ne s_1,\end{cases}$$
where $\mathrm{hi}$ is the index with the larger $s$. In words: the spare digits of the more-locked prime beyond $s_{\mathrm{lo}} + 1$ are wasted once the other prime unlocks, unless $p_{\mathrm{hi}}$ is Wieferich.

**Evidence [C].** Code: `formula_two_prime` in `scripts/kappa_trap.py`.
- *All* 1880 odd $q \le 200000$ with $g_0 = p_0 p_1$ and $\kappa \ge 1$ agree with the algorithm: 1734 have $\kappa_{\mathrm{trap}} = 1$ and 146 have $\kappa_{\mathrm{trap}} = 2$. Check C8 covers $q \le 40000$; the full range takes about 90 s by looping C8's code.
- Constructed cases:

| $q$ | $(s_{\mathrm{hi}}, s_{\mathrm{lo}})$ | formula | algorithm | $1 + \max_p \lceil M_1/\alpha\rceil$ (L5's bound) |
|---|---|---|---|---|
| $10533$ | $(2, 0)$ | 2 | 2 | 3 |
| $3 \cdot 3511 \cdot 21067$ | $(2, 1)$ | 3 | 3 | 3 |
| $3 \cdot 3511 \cdot 21067 \cdot 163 = 36169489893$ | $(3, 1)$ | 3 | 3 (C9, `--huge`) | 4 |

**Coverage, honestly.**
- The natural range exercises only the patterns $(0,0)$, $(1,0)$, $(2,0)$, all with $\omega_{\mathrm{hi}} = 0$. The constructed cases add $(2,1)$ and $(3,1)$.
- *Never tested:*
  - $s_0 = s_1 \ge 1$. This branch is not distinctive anyway: there $1 + \min = 1 + \max$.
  - $\omega_{\mathrm{hi}} = 1$ with $\lvert s_0 - s_1\rvert \ge 2$. This needs $p_{\mathrm{hi}} \in \{1093, 3511\}$ with $\sigma \ge 2$, so $u_q \ge p_{\mathrm{hi}}^3 \ge 1.3 \cdot 10^9$ times more, which is beyond the numpy path on 15 GB. This branch is the formula's least-supported claim.
- **L5's bound is not tight:** it gives 4, the truth is 3.

**Proof sketch** (Gemini's full text is in the session record; what follows keeps every step a reader must check). Define a locking profile with $M_0(i) = \nu_i$, $m_i(l) = \min(M_l(i), 1)$, $o_l = \mathrm{ord}_{p_0^{m_0(l)} p_1^{m_1(l)}}(2)$ and $\lambda_l(i) = v_{p_i}(2^{o_l} - 1)$. Set $M_{l+1}(i) = 0$ if $\sigma_i = 0$, else $\max(0, \min(\lambda_l(i) - 1, M_l(i) - 1))$.
1. *$L^*$ is the first $l \ge 1$ with $M_l = (0, 0)$.*
   - $M_1 = (s_0, s_1)$.
   - While both are $\ge 1$, each loses 1 per step, since $\lambda - 1 = \delta \ge s$.
   - After the smaller hits 0, $o_l = \mathrm{ord}_{p_{\mathrm{hi}}}(2)$ and $\lambda - 1 = \omega_{\mathrm{hi}}$. So $M(\mathrm{hi})$ drops to $\min(\omega_{\mathrm{hi}}, \lvert\Delta\rvert - 1)$, then by 1 per step.
2. *Upper bound (B9 style).* Claim: from a vertex with a path of length $L^*$, the values of $c_0$ reachable in $l$ steps fill the coset $\{r \equiv c_0(z_l) \pmod{p_0^{M_l(0)} p_1^{M_l(1)}}\}$. At $l = L^*$ this coset is everything, so the vertex is untrapped. The step uses two mechanisms:
   - *B: vary the exponent* $a(s) = a + s\, o_l$. This uses $v_{p_i}(d/o_l) = 1 + \nu_i - \lambda_l(i)$ (Lemma 1(2)).
   - *A: vary the residue* within the coset by $t_i p_i^{M_l(i)}$. This shifts $c_0$ by $(q'_{p_i})^{-1} 2^{a} t_i p_i^{M_l(i) - 1}$.
   - At each prime, use B if $\lambda - 1 \le M - 1$, else A.
   - ⚠ *To check:* when both primes want B at the same step, one shared $s$ must sweep both cosets at once. That needs $s$ free modulo $p_0^{\sigma_0 - (\lambda_0 - 1)} p_1^{\sigma_1 - (\lambda_1 - 1)}$ (CRT plus the valuation of $d/o_l$ at each prime). It is asserted, not written out.
   - Also check that "replace $r_l \bmod p_{\mathrm{lo}}$ freely" is licensed by the induction hypothesis (the coset is reachable) and not merely by membership in $S_l$.
3. *Lower bound [P\*].*
   - If $L^* = 1$, use $t = 1$.
   - Otherwise take $t$ with $c_0(t) \equiv \sum_{j=0}^{L^*-2} q^j \pmod{u_q}$. This generalizes $1 + q$ of §2a.
   - The exponent $a = d$ gives a path of length $L^* - 1$, peeling one power of $q$ per step.
   - By induction, every vertex reachable in $l$ steps has $c_0 \equiv r_l^* \pmod{p_0^{M_l(0)} p_1^{M_l(1)}}$. Compatibility forces $o_l \mid a$, so $2^a \equiv 1 \pmod{p_i^{\lambda_l(i)}}$; then divide by $q$.
   - At $l = L^* - 1$, $r^* = 0$ and $M(\mathrm{hi}) \ge 1$, so $c_0 \equiv 0 \pmod{p_{\mathrm{hi}}}$, which means out-degree $0$.

**Non-squarefree $g_0$ [L].** Gemini expects the recurrence to survive with $m_i(l) = \min(M_l(i), \alpha_i)$ and $\alpha_i$ in place of $1$, but not the closed form. Untested.

**Leads that follow.**
- Make ⚠ rigorous, or find the case where a shared $s$ cannot serve both primes.
- Find a cheaper test of the $\omega_{\mathrm{hi}}$ branch, perhaps a smarter state space than $\mathbb{Z}/u_q$: by step 1 only $(M_l)$ matters, so the iteration could be run on cosets.
- Generalize to $\omega(g_0) \ge 3$, where L1's chains live.

## 2c. General locking recurrence, exact truncation, and a depth-4 multiplier (Gemini, second round)

**Status at a glance.**

| claim | status | evidence |
|---|---|---|
| T1: the truncation theorem ($R_k = \pi^{-1}(\tilde R_k)$ modulo $\tilde u_q$) | [C] + Gemini proof, unread in detail | 29395 nontrivial truncations ($q \le 10^6$), all exact (C10 covers $q \le 10^5$) |
| G1: $\kappa_{\mathrm{trap}} = L^*$ of the general recurrence, any $g_0$ | lower bound [P\*]; upper bound [P\*] after the ⚠ fix; formula [C] | 121292 cases $q \le 10^6$ with $\kappa \ge 1$ ($\omega(g_0)$ up to 4), plus 4 constructed cases; no mismatch |
| D4: $\kappa_{\mathrm{trap}}(Q_4) \ge 4$ for $Q_4 = 3 \cdot 3511 \cdot 21067 \cdot 210671 \cdot 591701809 \cdot 163$ | [P\*] + definition-level check | explicit path of length 3 computed; 1000 random walks, none longer than 3 (`walk_check.py`) |
| §2b's two-prime formula | superseded by G1, which reduces to it | — |

**T1. Exact truncation.**
- *Statement.* Let $o = \mathrm{ord}_{g_0}(2)$ and $\delta_p = v_p(2^o - 1) - \alpha_p$. Put $\tilde\nu_p = \min(\nu_p, \alpha_p + \delta_p)$ for $\nu_p > \alpha_p$, else $\nu_p$, and $\tilde u_q = \prod p^{\tilde\nu_p}$. Running §1.2 modulo $\tilde u_q$ gives $R_k$ exactly, by pulling back.
- *Proof idea (Gemini).* Varying the exponent $a = a_0 + s\,o$ sweeps the digits of $c_0$ above $p^{\tilde\nu_p - \alpha_p}$, so successor sets are unions of cosets modulo $\tilde u_q$.
- *Effect.* $q = 3 \cdot 3511 \cdot 591701809$ (the least prime with $3511^2 \mid \mathrm{ord}_r(2)$) has $u_q = 27 \cdot 3511^3 \approx 1.2 \cdot 10^{12}$, but $\tilde u_q = 27 \cdot 3511^2$. It gives $\kappa_{\mathrm{trap}} = 3$ in 16 s, as Gemini predicted (C11, `--big`).
- *Code.* `truncated_modulus`, and `depth_sets_np(q, truncate=True)`.

**G1. General recurrence** (`recurrence_L` in `scripts/kappa_trap.py`). Let $p_i$ run over the primes of $g_0$, with $\gamma_i = \min(\alpha_i, \nu_i)$ and $M_0(i) = \nu_i$. Then
$$m_l(i) = \min(M_l(i), \gamma_i), \qquad o_l = \mathrm{ord}_{\prod p_i^{m_l(i)}}(2), \qquad \lambda_l(i) = v_{p_i}(2^{o_l} - 1)\ \ (0 \text{ if } m_l(i) = 0),$$
$$M_{l+1}(i) = \max\bigl(0, \min(\lambda_l(i) - \alpha_i,\ M_l(i) - \alpha_i)\bigr), \qquad L^* = \min\{l \ge 1 : M_l = 0\}.$$
- *Upper bound (⚠ fixed).* At each step, split the primes with $M_l \ge 1$ into two sets:
  - $\mathcal B_l$ ($M_l > \lambda_l$): steered by one shared $s$. By CRT, $s$ only needs to be free modulo $\prod_{\mathcal B_l} p_i^{N_i}$ with $N_i = \sigma_i - (\lambda_l(i) - \alpha_i)$, and $v_{p_i}(d/o_l) \ge \alpha_i + N_i > N_i$ by Lemma 1(2).
  - $\mathcal A_l$: steered by residue shifts $t_i p_i^{M_l(i)}$ at the fixed exponent $a^*$, which does not disturb $\mathcal A_l$ modulo $p^{M_l}$ because $o_l \mid a^* - a$.

  Read once by Claude; no gap found. Recheck the case $1 \le M_l(i) < \alpha_i$, which needs $\alpha_i \ge 2$ and has never been tested by computation.
- *Lower bound.* The witness is $c_0(t) \equiv \sum_{j \le L^*-2} q^j$, as in §2b.
- *Structure (Gemini, [P] given G1).* $v_{p_i}(\mathrm{ord}_{p_j}(2)) > 0$ implies $p_i < p_j$, so locking only goes from larger primes to smaller ones. In the squarefree case $\lambda_l(i) - 1 = \omega_i + \max_{j \text{ active}} v_{p_i}(\mathrm{ord}_{p_j}(2))$. Hence, for squarefree $g_0$ with $r$ primes, all non-Wieferich, $\kappa_{\mathrm{trap}} \le r$. Wieferich primes add $\omega_i$. This is consistent with the data (natural $q \le 10^6$ never exceed depth 2), but no case with $r = 3$ reaching depth 3 has been computed.

**D4. Depth 4 with three primes in $g_0$.**
- *Gemini's first candidate fails because of $\kappa$.* $3 \cdot 3511 \cdot 21067 \cdot r^*$ ($r^* = 210671$, so that $21067 \mid d$) has $\kappa = 3$. Even with $163$ added ($\nu_3 = 4$, $\kappa = 4$), $\nu_{3511} = 2$ and the profile is $(4,2,1) \to (3,1,0) \to (2,0,0) \to (0,0,0)$, so $L^* = 3$.
- *Depth 4 needs $\nu_{3511} = 3$ as well.* Adding $591701809$ gives $Q_4 = 4508686487856814609099227$, with $g_0 = 3 \cdot 3511 \cdot 21067$, $u_q = 3^4 \cdot 3511^3 \cdot 21067$ and $\kappa = 4$. The profile is $(4,3,1) \to (3,2,0) \to (2,1,0) \to (1,0,0) \to (0,0,0)$, so $L^* = 4$.
- *Checked at the level of definitions* (`python3 scripts/walk_check.py 4508686487856814609099227 1000`, about 1 min):
  - the explicit witness path $t \to \sum_{j<3} q^j \to 1 + q \to 1$ has length 3 and ends at vertex $1$, which has out-degree 0;
  - 1000 random backward walks from the witness class died at lengths $\{1: 853,\ 2: 123,\ 3: 24\}$, and none survived to length 4.
- So $\kappa_{\mathrm{trap}}(Q_4) \ge 4$ rests on the G1 lower-bound proof together with this check. $\tilde u_q \approx 7 \cdot 10^{16}$ is out of reach for the exact iteration.

**Blind spots.**
- Natural $q$ only exercise depth $\le 2$. Every claim about depth $\ge 3$ rests on five constructed $q$.
- $\alpha_i \ge 2$ with $\nu_i > \alpha_i$ (non-squarefree $g_0$ with spare digits) is untested.
- The $\omega_{\mathrm{hi}}$ branch of §2b ($s_{\mathrm{hi}} \ge s_{\mathrm{lo}} + 2$ at a Wieferich prime) is still uncomputed. With T1, it may now be within reach for a pair like $g_0 = 3511 \cdot 21067$; that is worth trying.

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
2. **[MMMM13] Theorem 3.1 is wrong as printed [C].** The theorem says $M = C_{a_1} \times \dots \times C_{a_n}$, with $a_i = \mathrm{lcm}(\mathrm{ord}_{p_i^{e_i}}(2), \mathrm{ord}_{p_i^{e_i}}(3))$. Its proof computes $\langle 2, 3 \rangle$ separately in each CRT component and then takes the direct product. But the subgroup generated by the diagonal elements can be smaller. For $b = 95$, $\lvert\langle 2, 3 \rangle\rvert = 36$ while $\prod a_i = 4 \cdot 18 = 72$. The reason is quadratic characters: $2$ and $3$ are non-squares both mod $5$ and mod $19$, so every $2^u 3^v$ has the same character at the two primes, which cuts out a subgroup of index $2$. Below $95$ there is no counterexample, and later ones are $b = 119, 143, 145, 215, 217, \dots$ There is also a counting obstruction: for $b = 5 \cdot 7 \cdot 13$ the product $C_4 \times C_6 \times C_{12}$ needs three generators, but $\langle 2, 3 \rangle$ has two (observed by Gemini). The correct statement is $M$ = the subgroup of $(\mathbb{Z}/b)^\times$ generated by $2$ and $3$. Cite this form, not "Theorem 3.1 verbatim". Whether Theorem 4.1 depends on the product form has not been checked.
3. **Density-zero sufficient sets [P].** [MMMM13] Theorem 2.1 and Corollary 2.2 use only sufficiency of arithmetic progressions and the fact that $y$ merges with $2^k y$. With B1(3) they hold for every odd $q$: $\{(a + dn) 2^{f(n)}\}$ is sufficient, and has density $0$ for $f(n) = n$.
4. **Theorem 4.4 compared with S4.** [MMMM13] Theorem 4.4 achieves at most one $T_1^{-1}$ step when 2 is a primitive root mod $p^r$, but only for targets $a$ prime to $p$. Its second case uses a mod-9 adjustment specific to $q = 3$. `SUPPLEMENTS_A.md` S4 maps any $z$ to any $y$ mod $p^r$, including $p \mid y$, where halvings alone cannot help. This plausibly explains the two odd steps, but it is not a proof that two are needed.
5. **[L] Self-color-duality and folding (§7).** For $q = 3$ the proofs go through the 2-adic conjugacy $\Phi$ with the shift. For odd $q$, $T_q$ is also conjugate to the shift on $\mathbb{Z}_2$, so the "if" direction of Theorem 7.1 and the folding of Theorem 7.3 may carry over. Neither has been checked, and the "only if" direction ($k = 2^n$) is not addressed.

### 3.5 Terminology
Keep `paper.md`'s notation everywhere. Use Monks's words (*merges*, *sufficient*, *forward/cycle/backward/strongly sufficient*, *back-tracing parity vector*) only in B1, B2 and L10. Watch for clashes: in [Mon06]/[MMMM13], $d$ is a modulus ($\Gamma_d$, $a + dn$), $q$ is a cycle length (Theorem 7.3), $m$ is a cycle's minimal element, and $T$ is the compressed map. In this project, $d = \mathrm{ord}_q(2)$, $q$ is the multiplier, and $\mathrm{Col}_q$ is uncompressed.

---

## 4. Leads for the next session [L]

1. **L2's weaker form.** L2 is refuted (§2a). Test the weaker form ($\nu_{p_1} \le \alpha_{p_1}$) on $q = 57 \cdot r_1 \cdots$ with $27 \mid d$, $19 \mid d$ and $\nu_{19} = 1$, so $g_0 = 57$ and $\delta_3 = 2$. Then run §1.2 (`--np` if $u_q$ is large).
2. **L1 chain $3 \leftarrow 19 \leftarrow p_2$.** We have $\mathrm{lcm}(\mathrm{ord}_{27}(2), \mathrm{ord}_{361}(2)) = \mathrm{lcm}(18, 342) = 342$, and any primitive prime divisor of $\Phi_{342}(2)$ has order exactly $342$. Add auxiliary primes giving $27 \mid d$, $361 \mid d$ and $p_2 \mid d$, then run §1.2. The values of $u_q$ may be large; the cost is $e_0 u_q^*$ per step and $\lvert R_k\rvert \le u_q$ in memory.
3. **Wieferich locking primes.** 10533 shows that a Wieferich $p_1$ enters $g_0$ without dividing $d$, which makes locking cheap. Test $q = 3^\alpha \cdot 3511 \cdots$ and $7 \cdot 1093 \cdots$, $13 \cdot 1093 \cdots$ for depth $\ge 3$. This bears on L6: the locking graph must allow $p_1 \mid g_0$ through $\nu_{p_1} \ge 1$ as well as through $p_1 \mid d$.
4. **L5 (several primes in $u_q^*$).** The scan code handles this case directly; extend `--scan` beyond $12000$ while filtering for $\omega(u_q^*) \ge 2$.
5. **`SUPPLEMENTS_A.md` Q4 ($\kappa \ge 1$).** S1's one-odd-step witnesses fail when $\kappa \ge 1$, because $c_0 \bmod u_q$ is fixed in one step (Lemma 2(2)). A plausible route has two stages. First, a primer stage: Proposition 1, then Lemma 6, to reach (H) and a congruence modulo $q^{K+1} u_q$. Second, the $\kappa = 0$ constructions, entered through Lemma 13. `paper.md` Lemma 3 already states the bound $\gamma \le \lambda_H \lceil \log_2(m'+1) \rceil$, unformalized, which is S5's mechanism. None of this has been carried out.
6. **Lean 4.35 (Q5).** Core only, no Mathlib, axioms `[propext, Quot.sound]`. Reuse `paper.md`'s ways of avoiding CRT: the single modulus $D_m$ in Proposition 1, and the weights $E_p^*$ (`GeneralAOp`, `GeneralAStage`, `GeneralASelect`). Check `#print axioms` for every new top-level theorem, and keep hypotheses out of structure fields.
7. **Still unchecked.** OEIS A182297 and Franco–Pomerance against the Wieferich-type family; $21$ fails $q^2 \mid 2^{\varphi(q)} - 1$.

---

## 5. Working practice

**Two-model work (from the user, 2026-11-22).**
- Pass content, not procedure or praise.
- Gemini proposes mechanisms and proofs under strict rigor. Claude tests the one case that could break them, and states the coverage.
- A wrong claim is a lead. Record what it got right and the exact break, then hand the break back. Don't just write [R].
- No re-verification loops, and no scripts whose outcome would not change the next step.

- Before a scan, name its possible outcomes. Run it only if they lead to different next steps. The scan of §2 passed this test: it could, and did, refute B10.
- A capped search proves nothing about what the cap excludes. Scan 1 ($N_q \le 4 \cdot 10^5$) hid all the depth-2 cases. B10's hand enumeration was "checked once" and still missed 10533.
- Check a hand derivation with a small script, and check a script against the algebra. Index slips such as $p^{\alpha+1}$ versus $p^{2\alpha}$, and confusing exponents with Lemma 2's index $j$, have occurred before.
- Read the primary sources when they are available. Reading them here caught L10's map convention, the role of $2^{60}$ in Proposition 6.5(c), the bibliography errors, and the error in [MMMM13] Theorem 3.1.
- Keep refuted claims in the ledger, with the counterexample and any surviving weaker form.

---

## 6. Changes from the Gemini draft

- **Added (second round):** §2a, the depth-3 multiplier proposed by Gemini, checked by hand and by computation. Gemini's claim that it runs "in milliseconds" was off: $u_q \approx 3.3 \cdot 10^8$, which needed the numpy path (17 s).
- **Added:** the counterexample $10533$ and the correction to B10 (§2); the brute-force cross-check (§1.3); the error in [MMMM13] Theorem 3.1 (§3.4.2); the bibliography corrections (§3.1).
- **Weakened:** "Proposition 6.5(a),(b) transfer cleanly" is now [L], since it depends on unproved analogues of Proposition 6.3. "Theorems 3.1 and 4.1 generalize verbatim" is replaced by the corrected statement. "§7 carries over" is now [L]. "S4 needs two steps precisely to cover $p \mid a$" is now "plausibly explains".
- **Not reproduced:** the draft's account of a `2026-11-21` session log (`scan.py`, `timeout 300`, and the reason the scan stalled). That log is not in this repository, so it could not be checked.
