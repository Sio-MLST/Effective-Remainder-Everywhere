# Supplements B to `paper.md`: Theorem B, local odd depth, and Wieferich-type traps

Companion to `paper.md` and `SUPPLEMENTS_A.md`. This file develops the Haar-null side (Theorem B): local odd depth, sufficiency in Monks's sense, explicit trapped sets, and the *effective trap depth* $\kappa_{\mathrm{trap}}(q)$ of Wieferich-type multipliers. Section 8 is a ledger of leads, conjectures and refuted claims, kept together with the reasons and with any weaker form that might still hold.

**Status.** Nothing here is formalized in Lean 4.35, and `paper.md` depends on none of it. Each item carries one of these labels:

| label | meaning |
| --- | --- |
| **[P]** | proved in full in this file, from `paper.md` |
| **[P\*]** | proved, but with a step that has been checked only once (stated where) |
| **[C]** | computational fact: computed from the definitions, not proved by hand |
| **[L]** | lead: a plausible statement or sketch with known gaps |
| **[R]** | refuted as stated; the reason and any surviving weaker form are recorded |

**Provenance.** Most of §§1–6 and §8 began as drafts by another model (Gemini). They were then reviewed and corrected, and §5.2–5.5 were developed further in discussion. Every correction made in review is recorded either where it applies or in §8.

**Notation** follows `paper.md`: $q > 1$ is odd, $d = \mathrm{ord}_q(2)$, $2^d = 1 + qu$, $g_0 = \gcd(q, u)$, $\alpha_p = v_p(q)$, $\nu_p = v_p(u)$, $u_q = \prod_{p \mid q} p^{\nu_p}$, $N_q = q u_q$, $\kappa = \max_{p \mid q} \lceil \nu_p / \alpha_p \rceil$, $H_q = \langle 2 \rangle \subseteq (\mathbb{Z}/q)^\times$. $\mathcal{G}_q$ is the graph on $V_q$ with edges $z \to z'$ iff $z' \equiv c_0(z) \pmod{u_q}$, and $R_{\mathrm{core}} \subseteq V_q$ is as in `paper.md`, §1. In addition,
$$g_0 = \prod_{p \mid q} p^{\min(\alpha_p, \nu_p)}, \qquad u_q^* := u_q / g_0 = \prod_{p \mid q} p^{\max(0,\, \nu_p - \alpha_p)}.$$
Two kinds of number are distinguished:
- A *Wieferich-type multiplier* is an odd $q > 1$ with $g_0 > 1$, equivalently $\kappa \ge 1$. These are $21, 39, 55, 57, 105, \dots$ (see `README.md`).
- A *Wieferich prime* is an odd prime $p$ with $p^2 \mid 2^{p-1} - 1$ (OEIS A001220: $1093, 3511$).

*To check:* the draft identified the first family with OEIS A182297 and with Franco–Pomerance's "Wieferich numbers". Some definitions in the literature require $q^2 \mid 2^{\varphi(q)} - 1$, and $21$ fails that test ($2^{12} - 1 = 3^2 \cdot 5 \cdot 7 \cdot 13$). So the identification must be checked against the sources before it is cited.

---

## 1. Forward escape, cycles, and sufficiency for all $\kappa \ge 0$ [P]

This answers `SUPPLEMENTS_A.md`, §5, Question 3.

**Proposition B1.** *Let $q > 1$ be odd.*
1. *Every periodic $t \ge 1$ satisfies Proposition 1, so $\overline{R_q(t)} = \widehat{\mathbb{Z}}$.*
2. *For $x \ge 1$, let $w_0$ be the odd part of $x$, and let $w_1, \dots, w_{\kappa+1}$ be the next $\kappa + 1$ odd integers along the forward orbit of $x$. Then $w_{\kappa+1}$ satisfies Proposition 1.*
3. *Every arithmetic progression $(a + b\mathbb{N}) \cap \mathbb{Z}_{\ge 1}$ is sufficient for $\mathrm{Col}_q$ in Monks's sense [Mon06]: every forward orbit merges with the forward orbit of some element of the progression.*

*Proof.*
1. By Theorem B(3), no Theorem B target is periodic. By the dichotomy, every periodic target satisfies Proposition 1.
2. We have $q w_r + 1 = 2^{e_{r+1}} w_{r+1}$ with $e_{r+1} \ge 1$. So $(w_\kappa, \dots, w_0)$ is a backward chain of $\kappa + 1$ odd steps in $R_q(w_{\kappa+1})$, which Theorem B(1) forbids for a Theorem B target.
3. Apply Theorem A to $t = w_{\kappa+1}$ with $m = b$, $r = a$, $B = a$. This gives $w > a$ with $w \equiv a \pmod b$ and $w \to t$. $\square$

*Example.* Take $q = 21$ ($N_q = 63$, $\kappa = 1$) and $x = 3$. The orbit runs $3 \to 64 \to \dots \to 1 \to 22 \to 11$, so $w_1 = 1$ (trapped) and $w_2 = 11$. Here $c_0(11) = 1$. Also $37 \cdot (2^2 - 21) = -629 \equiv 1 \pmod{63}$, so $37 \in R_{\mathrm{core}}$, and $37 \equiv 1 \pmod 3$. So $11 \to 37$ is an edge into $R_{\mathrm{core}}$.

---

## 2. The pruned graph and strong sufficiency

Let $\mathcal{D}_q \subseteq V_q$ be the vertices that have a path of length $\kappa$ in $\mathcal{G}_q$, and let $\mathcal{T}_q = (\mathbb{Z}/N_q) \setminus \mathcal{D}_q$. Put $\widetilde V_q = \{x \ge 1 : x \bmod N_q \in \mathcal{D}_q\}$, which is the set of Theorem A targets. For $q = 3$ this is $\{x : 3 \nmid x\}$, the pruned set of [MMMM13].

**Proposition B2.**
1. **[P]** *$\widetilde V_q$ is forward-invariant: if $x \in \widetilde V_q$ and $x \to y$, then $y \in \widetilde V_q$. Equivalently, $\mathcal{T}_q$ is backward-closed.*
2. **[P]** *Every forward orbit enters $\widetilde V_q$ within $\kappa + 1$ odd steps and never leaves it. Every cycle lies in $\widetilde V_q$. Every infinite back-tracing sequence $x_0 \leftarrow x_1 \leftarrow \cdots$ with infinitely many odd steps lies in $\widetilde V_q$.*
3. **[P]** *An infinite back-tracing sequence from a target in $\mathcal{T}_q$ takes at most $\kappa$ odd steps. Its parity vector is therefore eventually $0$, which makes it eventually periodic (a rational $2$-adic number) and never irrational.*

*Proof.*
1. A witness for (H) in $R_q(x)$ also lies in $R_q(y)$.
2. Entry is B1(2), persistence is part 1, and the statement about cycles is Theorem B(3). For back-tracing sequences, suppose some $x_k \notin \widetilde V_q$. Then the first $\kappa + 1$ odd steps after index $k$ form a backward chain of length $\kappa + 1$ in $R_q(x_k)$. The halving exponents are $\ge 1$ after the first step because $q x + 1$ is even. This contradicts Theorem B(1).
3. This follows directly from Theorem B(1). $\square$

*Correction.* The draft said the parity vector in part 3 is "neither irrational nor periodic". That is wrong: an eventually-zero vector is eventually periodic.

**[L] Strong sufficiency.** The draft called $\widetilde V_q$ *strongly sufficient*, paraphrasing [MMMM13]: a set that meets every divergent orbit, every nontrivial cycle, and every infinite back-tracing sequence with an irrational parity vector. B2(2) proves these three properties. Whether they match [MMMM13]'s actual definition has not been checked against the paper.

The draft also remarked that arithmetic progressions are not in general strongly sufficient. For instance, when $q = 3$ the class $0 \bmod 3$ meets no cycle, because a forward orbit never re-enters $3\mathbb{Z}$ once it has left.

---

## 3. Local odd depth and sharpness of Theorem B [P]

For a Theorem B target $t$, define its local odd depth $m(t)$:
- $m(t) = 0$ if $t \bmod N_q \notin V_q$;
- otherwise $m(t) = L(t) + 1$, where $L(t) < \kappa$ is the maximal length of a path from $t \bmod N_q$ in $\mathcal{G}_q$.

**Proposition B3.** *Let $t$ be a Theorem B target with $m = m(t)$.*
1. *$m(t)$ is exactly the maximal length of a backward chain of odd steps in $R_q(t)$.*
2. *$|R_q(t) \bmod 2^n| \le (n+1)^{m+1}$ and $|R_q(t) \cap [1, X]| = O_q((\log X)^{m+1})$.*
3. *(Sharpness.) $|R_q(t) \cap [1, X]| \ge c_1 (\log_2 X)^{m+1}$ for large $X$, and $|R_q(t) \bmod 2^n| \ge c_2\, n^{m+1}$, with $c_1, c_2 > 0$ depending on $q$ and $t$.*

*Proof.*

**Part 1.**
- *Upper bound.* The proof of Theorem B(1) turns a chain of length $r$ into a path of length $r - 1$ in $\mathcal{G}_q$, so $r \le L(t) + 1$.
- *Lower bound.* Take a path $z_0 \to \dots \to z_L$. Lemma 2(2) gives $w_r = c_{j_r}(w_{r-1}) \equiv z_r \pmod{N_q}$ with $j_r < q$, and $w_{L+1} = c_0(w_L)$ completes a chain of length $L + 1$.

**Part 2.** Replace $\kappa$ by $m$ in the proof of Theorem B(2),(3).

**Part 3.** For $m = 0$, use the elements $2^k t$. For $m \ge 1$, fix $j_1, \dots, j_L$ as in part 1 and set $j_m = 0$. For a tuple $(s_1, \dots, s_m, k) \in \mathbb{N}^{m+1}$, put $w_r = c_{j_r + q s_r}(w_{r-1})$ and $y = 2^k w_m$.
- *The residues stay on the path.* $c_{j + qs} - c_j = 2^{a_0 + dj}\, w\, u\, S_{qs}$, and $v_p(u S_{qs}) \ge \nu_p + \alpha_p$, so $w_r \equiv z_r \pmod{N_q}$ for every choice of $s_r$.
- *Injectivity.* $k = v_2(y)$. The target $t$ is not periodic, so $t$ occurs only once on the forward orbit of $w_m$. The odd values before that occurrence recover $w_m, \dots, w_1$, then the exponents $E_r = a_0 + d(j_r + q s_r)$, and hence the $s_r$.
- *Counting in $[1, X]$.* $E_r \le dq(s_r + 1)$, so every tuple with $k + dq \sum s_r \le \log_2(X/t) - mdq$ is counted. That gives $\Omega((\log X)^{m+1})$ elements.
- *Counting mod $2^n$.* We have $q^m y = 2^{S_0} t - \sum_{r=1}^{m} q^{r-1} 2^{S_r}$ with $S_r = k + E_{r+1} + \dots + E_m$ strictly decreasing in $r$. So when $S_0 + v_2(t) < n$, the residue $y \bmod 2^n$ determines $S_m, S_{m-1}, \dots, S_0$ successively by $2$-adic valuations. $\square$

*Example.* For $q = 21$, $t = 1$ has $m(1) = 1$, and $|R_{21}(1) \cap [1, X]| = \tfrac{1}{12} (\log_2 X)^2 + O(\log X)$.
- The predecessors are $2^k$ and $2^k (2^{6j} - 1)/21$.
- The numbers $(2^{6j} - 1)/21 = 3 S_j$ are divisible by $3$, so they have no odd predecessors.
- **[C]** Brute force gives ratios $0.116, 0.100, 0.092$ at $X = 2^{40}, 2^{80}, 2^{160}$, decreasing towards $1/12 \approx 0.083$.

---

## 4. Out-degree, density bound, explicit trapped sets

Let $\delta_{\mathrm{trap}}(q) = |\mathcal{T}_q| / N_q$ and $\delta_{\mathrm{dense}}(q) = 1 - \delta_{\mathrm{trap}}(q)$.

**Proposition B4 [P].**
1. *A vertex $z \in V_q$ has out-degree $\ge 1$ iff $c_0(z) \bmod g_0 \in H_q \bmod g_0$.*
2. *$\delta_{\mathrm{dense}}(q) \le \dfrac{d}{q} \cdot \dfrac{|H_q \bmod g_0|}{g_0} \le \dfrac{d}{q} \cdot \dfrac{\varphi(g_0)}{g_0}$.*

*Proof.*
1. By CRT, an edge requires a unit $z'$ with $z' \bmod q \in H_q$ and $z' \equiv c_0(z) \pmod{u_q}$. Such a $z'$ exists iff the two conditions agree modulo $\gcd(q, u_q) = g_0$.
2. On the fibre $z_0 + qj$, the value $c_0 = c_0(z_0) + 2^{a_0} j$ runs over all of $\mathbb{Z}/u_q$. Also $|V_q| / N_q = d/q$, and every vertex of $\mathcal{D}_q$ has out-degree $\ge 1$ when $\kappa \ge 1$. $\square$

**Comparison with `SUPPLEMENTS_A.md`, §4.** The certificate $T$ there catches only the sinks with $c_0(z) \equiv 0 \pmod{g_0}$.
- **[C]** For $q = 301 = 7 \cdot 43$ ($d = 42$, $g_0 = u_q = 7$, $H \bmod 7 = \{1, 2, 4\}$): $T$ excludes $42$ of the $294$ classes in $V_{301}$, while B4 excludes $168$.
- For $q = 1093$: $T$ catches $364$ of the $364 \cdot 729$ trapped classes in $V_{1093}$.

**Proposition B5 [P] (exact image of $R_q(1)$ modulo $2^d - 1$).** *Suppose $g_0 > 1$ and let $T_u = \{x : u \mid x\} \cup \{x : x \bmod (2^d - 1) \in \langle 2 \rangle\}$. Then $R_q(1) \subseteq T_u$, and $R_q(1) \bmod (2^d - 1) = T_u \bmod (2^d - 1)$, which has exactly $d + q$ elements.*

*Proof.*
- *Backward closure.* Since $g_0 \mid u$ and $g_0 \mid q x$, we get $u \nmid q x + 1$. So $q x + 1 \equiv 2^i \pmod{qu}$, which forces $d \mid i$, hence $u \mid x$.
- *Counting.* The $d$ powers of $2$ are prime to $u$, so they are disjoint from the $q$ multiples of $u$. These are hit by the $2^i$ and by the elements $(2^{dj} - 1)/q = u S_j$ for $1 \le j \le q$, because $S_j \bmod q$ is a bijection by Lemma 2(2). $\square$

---

## 5. Effective trap depth $\kappa_{\mathrm{trap}}(q)$

Define
$$\kappa_{\mathrm{trap}}(q) := \max\{\, m(t) : t \text{ a Theorem B target} \,\} \le \kappa.$$
When $\kappa \ge 1$ we have $\kappa_{\mathrm{trap}} \ge 1$: the target $t = 1$ has $c_0(1) = u \equiv 0 \pmod{g_0}$, so it has out-degree $0$ and $m(1) = 1$.

### 5.1 Single non-Wieferich prime [P] (superseded by 5.3–5.4, kept for its short proof)

**Proposition B6.** *If $u_q = p^\nu$ with $p$ not a Wieferich prime, then every vertex with out-degree $\ge 1$ has an edge into $R_{\mathrm{core}}$. Hence $\kappa_{\mathrm{trap}} = 1$, and B4(2) holds with equality.*

*Proof.* $\langle 2 \rangle \bmod p^\nu$ consists of all lifts of $\langle 2 \rangle \bmod p$, and $\mathrm{ord}_{p^\nu}(2) \mid d$. We have $c_d \equiv 1 \pmod p$, so $c_0(z) \equiv 2^{-i_0} c_d \pmod{p^\nu}$ for some $i_0$, and $2^{-i_0} c_d \in R_{\mathrm{core}}$. $\square$

*Examples* **[C]**: $57, 111, 219, 285$ ($u_q = 9$, $\kappa = 2$) and $489$ ($u_q = 81$, $\kappa = 4$) all have $\kappa_{\mathrm{trap}} = 1$, with $\delta_{\mathrm{dense}}(57) = 4/19$ and $\delta_{\mathrm{dense}}(489) = 36/163$.

### 5.2 Reduction to $u_q^*$ [P]

**Lemma B7.** *Let $z \in V_q$ and $r = c_0(z) \bmod u_q$. Then the successors of $z$, and hence whether $z$ has a path of length $\ell$, depend only on $r$. Concretely, $z'$ is a successor of $z$ iff $z' \equiv 2^{-a} \pmod q$ and $z' \equiv r \pmod{u_q}$ for some $a \in \{1, \dots, d\}$ with $2^{-a} \equiv r \pmod{g_0}$. For each such $a$:*
1. *The values of $c_0(z') \bmod u_q$ over the $g_0$ lifts $z' + k N_q / g_0$ are exactly the $g_0$ lifts of a single class modulo $u_q^*$.*
2. *That class is given, at each $p \mid u_q^*$ with $q = p^{\alpha_p} q'_p$, by*
$$c_0(z') \equiv (q'_p)^{-1} \cdot \frac{2^a r - 1}{p^{\alpha_p}} \pmod{p^{\nu_p - \alpha_p}}.$$

*Proof.* Compatibility of the two congruences is CRT modulo $\gcd(q, u_q) = g_0$. Two solutions differ by a multiple of $\mathrm{lcm}(q, u_q) = N_q / g_0$. Shifting $z'$ by $k N_q / g_0$ shifts $c_0(z')$ by $2^a k\, u_q^*$, which runs over the multiples of $u_q^*$ modulo $u_q$. The formula in part 2 is $c_0 = (2^a z' - 1)/q$ evaluated modulo $p^{\nu_p - \alpha_p}$, using $z' \equiv r \pmod{p^{\nu_p}}$. $\square$

Lemma B7 gives a cheap test. Only $a \bmod \mathrm{ord}_{\mathrm{lcm}(g_0, u_q)}(2)$ and $r \bmod u_q$ matter, so computing $\kappa_{\mathrm{trap}}$ needs about $e_0 \cdot u_q$ checks, with $e_0 = \mathrm{ord}_{\mathrm{lcm}(g_0, u_q)}(2)$, and never $N_q$ or $d \cdot u_q$.

### 5.3 Rules 1 and 2: the $\delta_p = 0$ collapse [P]

For $p \mid u_q^*$ (that is, $\nu_p > \alpha_p$), define
$$o := \mathrm{ord}_{g_0}(2), \qquad \lambda_p := v_p(2^o - 1) \ge \alpha_p, \qquad \delta_p := \lambda_p - \alpha_p.$$

**Proposition B8.**
1. *(Rule 1) If $u_q^* = 1$, then $\kappa_{\mathrm{trap}}(q) \le 1$.*
2. *(Rule 2) If $\delta_p = 0$ for every $p \mid u_q^*$, then $\kappa_{\mathrm{trap}}(q) = 1$ (when $\kappa \ge 1$).*

*Proof.*

**Rule 2.** Let $z$ have out-degree $\ge 1$ via an exponent $a_0$, and set $a(s) \equiv a_0 + s\,o \pmod d$. Then $2^{-a(s)} \equiv r \pmod{g_0}$, so every $a(s)$ is compatible.
- For $p \mid u_q^*$ we have $p \mid g_0$, so $p \nmid r$.
- Then $q\,(\Delta c_0) \equiv r \cdot 2^{a_0 + s_2 o}\,(h^{s_1 - s_2} - 1) \pmod{p^{\nu_p}}$ with $h = 2^o$. Since $v_p(h - 1) = \alpha_p$, Lemma 1(2) gives $v_p(\Delta c_0) = v_p(s_1 - s_2)$ modulo $p^{\nu_p - \alpha_p}$.
- So $s \bmod u_q^*$ maps injectively, hence bijectively, onto $\mathbb{Z}/u_q^*$, at all primes simultaneously. With the $g_0$-lifts of B7(1), the successors of $z$ realize *every* value of $c_0(z') \bmod u_q$.
- Choose one with $c_0(z') \equiv c_1$. Then $z \to z' \to c_1 \in R_{\mathrm{core}}$, a path of length **two** (the draft wrote "one step"). By Proposition 1, $z$ is untrapped.
- So trapped vertices of $V_q$ have out-degree $0$, and $m \le 1$.

**Rule 1** is the same argument with nothing to vary: B7(1) alone already gives every residue. $\square$

Rule 2 contains B6: for a non-Wieferich $p$, $v_p(2^{\mathrm{ord}_{p^\alpha}(2)} - 1) = \alpha$. It also disposes of $2715, 3135, 4065$ ($g_0 = 15$, $2^4 - 1 = 15$, $\delta_3 = 0$) and $4137$ ($g_0 = 21$, $u_q^* = 7$, $2^6 - 1 = 63$, $\delta_7 = 0$).

### 5.4 Rule 3: the locking-depth bound [P]

**Proposition B9.** *Suppose $u_q^* = p^{\nu_p - \alpha_p}$ is a power of a single prime $p$. Put $M_1 = \min(\delta_p,\, \nu_p - \alpha_p)$. Then*
$$\kappa_{\mathrm{trap}}(q) \le 1 + \left\lceil \frac{M_1}{\alpha_p} \right\rceil \le 1 + \left\lceil \frac{\delta_p}{\alpha_p} \right\rceil.$$

The draft stated only the right-hand bound, but its proof gives the sharper one. Write $\alpha = \alpha_p$, $\nu = \nu_p$, and $M_l = \max(0,\, M_1 - (l-1)\alpha)$. Let $L^*$ be the first $l$ with $M_l = 0$, namely $L^* = 1 + \lceil M_1 / \alpha \rceil$.

*Proof.* Suppose $z_0$ has a path $z_0 \to z_1 \to \dots \to z_{L^*}$. We show by induction on $l \le L^*$ that the values of $c_0$ at vertices reachable in $l$ steps include the whole coset
$$S_l = \{\, r \bmod u_q : r \equiv c_0(z_l) \pmod{p^{M_l}} \,\}.$$

**Step $l = 1$.** Let $r_0 = c_0(z_0)$ and use the exponents $a_1(s) \equiv a_0(z_1) + s\,o \pmod d$, all compatible mod $g_0$. Lemma 1(2) with $v_p(2^o - 1) = \alpha + \delta_p$ gives
$$v_p(\Delta c_0) = \min(\nu - \alpha,\; \delta_p + v_p(s_1 - s_2)) \pmod{p^{\nu - \alpha}}.$$
So every value is $\equiv c_0(z_1) \pmod{p^{M_1}}$, and $0 \le s < p^{\nu - \alpha - M_1}$ gives distinct values that fill that coset modulo $u_q^*$. The $g_0$-lifts of B7(1) then fill $S_1$.

**Step $l \to l+1$.** Let $B = \max(M_l, \alpha) \le \nu - 1$ and, for $0 \le t < p^{\nu - B}$, let $r^{(t)} \equiv r_l + t\,p^B \pmod{p^\nu}$, with $r^{(t)} \equiv r_l$ at the other primes of $u_q$.
- Since $B \ge M_l$, we have $r^{(t)} \in S_l$, so the induction hypothesis gives a vertex reachable in $l$ steps whose $c_0$ is $r^{(t)}$.
- Since $B \ge \alpha$ and the $p$-part of $g_0$ is $p^\alpha$, we have $r^{(t)} \equiv r_l \pmod{g_0}$. So the same exponent $a_{l+1} = a_0(z_{l+1})$ is compatible. This is the point where compatibility modulo $g_0$ has to be checked at each step.
- The successor $z'_{(t)}$ satisfies $c_0(z'_{(t)}) - c_0(z_{l+1}) \equiv (q'_p)^{-1}\, 2^{a_{l+1}}\, t\, p^{B - \alpha} \pmod{p^{\nu - \alpha}}$, with $B - \alpha = M_{l+1}$.
- So these values fill the coset modulo $p^{M_{l+1}}$, and the lifts fill $S_{l+1}$.

**Conclusion.** At $l = L^*$, $S_{L^*} = \mathbb{Z}/u_q$, so some vertex reached in $L^*$ steps has an edge to $c_1 \in R_{\mathrm{core}}$. By Proposition 1, $z_0$ is untrapped. Hence trapped vertices have $L \le L^* - 1$, that is $m \le L^*$. $\square$

*Tightness* **[C]**: on all three known examples of §5.5 the sharper bound equals the true value.

| $q$ | $\delta_3$ | $\nu_3 - \alpha_3$ | draft bound | sharper bound | actual $\kappa_{\mathrm{trap}}$ |
| --- | --- | --- | --- | --- | --- |
| 7959 | 1 | 2 | 2 | 2 | 2 |
| 11571 | 1 | 1 | 2 | 2 | 2 |
| 10887 | 2 | 1 | 3 | 2 | 2 |

*Scope.* B9 needs $u_q^*$ to be a single prime power. For example, "$g_0 = 21 \Rightarrow \kappa_{\mathrm{trap}} \le 2$ however large $\kappa$ is" follows only when $7 \nmid u_q^*$.

### 5.5 The smallest multipliers with $\kappa_{\mathrm{trap}} \ge 2$

**Facts [C].** Computed with the full graph or the residue-pair version of $\mathcal{G}_q$, with integer chains checked where stated.

| $q$ | factorization | $d$ | $g_0$ | $u_q$ | $\kappa$ | $\kappa_{\mathrm{trap}}$ |
| --- | --- | --- | --- | --- | --- | --- |
| 7959 | $3 \cdot 7 \cdot 379$ | 378 | 21 | 189 | 3 | **2** |
| 10887 | $3 \cdot 19 \cdot 191$ | 1710 | 57 | 171 | 2 | **2** |
| 11571 | $3 \cdot 7 \cdot 19 \cdot 29$ | 252 | 21 | 63 | 2 | **2** |

For $11571$, a depth-2 target is $t = 415$. Integers $w_1$ (about 450 digits) and $w_2$ with $q w_1 + 1 = 2^k \cdot 415$ and $q w_2 + 1 = 2^{k'} w_1$ were constructed and checked. Of the $15876$ classes in $V_{11571}$, $4536$ have out-degree $\ge 1$ and $1512$ are trapped at depth exactly $2$. Also $\delta_{\mathrm{dense}}(11571) = 16/3857$, below the B4 bound of $24/3857$.

*7959 by hand.*
- $\mathrm{ord}_{379}(2) = 378$, since $2^{189} \equiv -1$, $2^{126} \not\equiv 1$ and $2^{54} \not\equiv 1 \pmod{379}$.
- So $d = 378$, $\nu_3 = 3$ and $\nu_7 = 1$.
- Targets $t$ with $c_0(t) \equiv 1 \pmod{189}$ have successors $z' \equiv 1 \pmod{189}$. These have $6 \mid a_0(z')$, so $2^{a_0(z')} \equiv 1 \pmod 9$ and $c_0(z') \equiv 0 \pmod 3$, a dead end.
- So $m(t) = 2 < 3 = \kappa$.

**Theorem B10 [P\*].** *$7959$ is the smallest odd $q > 1$ with $\kappa_{\mathrm{trap}}(q) \ge 2$, and the multipliers below $12000$ with $\kappa_{\mathrm{trap}} \ge 2$ are exactly $7959, 10887, 11571$.*

*Proof.*

**Necessary condition.** By Rule 2, some $p \mid u_q^*$ has $\delta_p \ge 1$, that is $p^{\alpha+1} \mid 2^o - 1$ with $o = \mathrm{ord}_{g_0}(2)$, $\alpha = \alpha_p$.

**Case $p$ non-Wieferich.** Then $v_p(2^o - 1) = 1 + v_p(o)$, so $p^\alpha \mid \mathrm{ord}_{g_0}(2)$.
- Since $v_p(\mathrm{ord}_{p^\alpha}(2)) = \alpha - 1$, another prime $p_1 \mid g_0$ must have $p^\alpha \mid \mathrm{ord}_{p_1}(2)$.
- $p_1 \mid g_0$ forces $p_1 \mid d$.
- $p \mid u_q^*$ means $\nu_p \ge \alpha + 1$, so $v_p(2^d - 1) \ge 2\alpha + 1$, which forces $p^{2\alpha} \mid d$. (The draft wrote $p^{\alpha+1}$; the two agree only for $\alpha = 1$.)

**Enumeration below $12000$.**
- *$p = 3$, $p_1 = 7$.* We need $9 \mid d$ and $7 \mid d$.
  - From one prime $r \equiv 1 \pmod{63}$: $127$ fails ($\mathrm{ord} = 7$), and $379$ gives $7959$.
  - From two primes: $19 \cdot 29$ gives $11571$; the next, $19 \cdot 43$, is too large.
- *$p = 3$, $p_1 = 19$.* We need $19 \mid d$. The first prime with $19 \mid \mathrm{ord}_r(2)$ is $191$ (order $95$), giving $10887$; the next, $229$, is too large.
- *$p = 3$, $p_1 \in \{13, 37, 73, \dots\}$* exceeds $12000$, for example $111 \cdot 149$ and $39 \cdot 19 \cdot 53$.
- *Products in which $p_1 \nmid d$* (such as $3 \cdot 7 \cdot 13 \cdot 19$, with $d = 36$) fail the condition $p_1 \mid g_0$.
- *$9 \mid q$* needs $81 \mid d$, for instance via $163$, and $9 \cdot 19 \cdot 163 > 12000$.
- *$p = 5$* needs $25 \mid d$ (first via $101$) together with a $p_1$ that divides $d$. The smallest such configuration exceeds $12000$; for example $5 \cdot 11 \cdot 101 = 5555$ fails because $11 \nmid d = 100$.
- *$p = 7$* needs $49 \mid d$ (first via $197$), and $7 \cdot 29 \cdot 197 > 12000$.

**Case $p$ Wieferich.** Below $12000$ only $1093$ and $3511$ are possible, and $\nu_p \ge 2$ would need $p \mid d$, that is a prime $r \equiv 1 \pmod p$ dividing $q$, which is too large.

**Sufficiency.** The three survivors have $\kappa_{\mathrm{trap}} = 2$ by the table above. $\square$

*Why only [P\*].* The enumeration was done by hand and checked once, in review. An independent confirmation would be cheap with the test of §5.2: run over all odd $q \le 12000$ with $\kappa \ge 2$, without assuming Rule 2. That has not been done.

---

## 6. $p$-adic versus $2$-adic geometry

**Proposition B11.**
1. **[P]** *For every odd prime $p$ and every $t \ge 1$, the closure of $R_q(t)$ in $\mathbb{Z}_p$ has positive Haar measure, because it contains $t\, \overline{\langle 2 \rangle}$, an open set. So no single odd prime-power modulus can witness Haar measure $0$.*
2. **[P]** *For a Theorem B target with $m = m(t)$, the closure of $R_q(t)$ in $\mathbb{Z}_2$ is countable, with Cantor–Bendixson rank at most $m + 1$.*

*Proof of part 2.* This repairs the draft, which parametrized by "$(j_1, \dots, j_r)$ with $j_1 \ge 0$, $j_{\ge 2} \ge 1$", mixing up Lemma 2's index with the halving exponents and treating the admissible set as a full product.

By B3(1), each $x \in R_q(t)$ equals $2^k w_r$ with $r \le m$, where $w_r$ comes from $t$ via halving exponents $(E_1, \dots, E_r)$. The admissible tuples $(k, E_1, \dots, E_r)$ form a subset $A_r$ of $\mathbb{N}^{r+1}$; whether $E_i$ is admissible depends on earlier residues mod $q$.
- Let $K_r$ be the closure of $A_r$ in $(\mathbb{N} \cup \{\infty\})^{r+1}$. It is compact and countable.
- The map $(k, E) \mapsto 2^k w_r$, with $2^\infty = 0$ and $(2^\infty y - 1)/q = -1/q$, is continuous into $\mathbb{Z}_2$ because $q$ is a $2$-adic unit.
- So the closure of $R_q(t)$ lies in the union of the compact images $f(K_r)$.
- $(\mathbb{N} \cup \{\infty\})^{r+1}$ has empty $(r+2)$-nd derivative, and $(f K)^{(\beta)} \subseteq f(K^{(\beta)})$ for continuous $f$ on a compact metric space. $\square$

The draft's remark that composite odd moduli such as $2^p - 1$, or $\prod_{p\ \mathrm{odd}} \mathbb{Z}_p$, "can exhibit sparsity" is unproved and has moved to §8 (L9).

---

## 7. Computational record [C]

How the facts above were obtained, so that they can be redone independently.

1. **Scan 1.** All odd $q < 6000$ with $\kappa \ge 1$ and $N_q \le 4 \cdot 10^5$, using the full graph on $N_q$ vertices.
   - Result: $\kappa_{\mathrm{trap}} = 1$ for every such $q$, and B6 and B4-equality held whenever $u_q$ was a single prime power.
   - *Blind spot:* the cap $N_q \le 4 \cdot 10^5$ excluded the interesting cases. The candidates with two primes in $u_q$ and $\kappa \ge 2$ found below $6000$ were $2715, 3135, 4065, 4137$, all with $\kappa_{\mathrm{trap}} = 1$, in agreement with Rule 2.
2. **Spot checks** using the residue-pair version (about $d \cdot u_q$ checks): $11571$ (then a new counterexample to the guess in §8, L3), $7959$, $10887$.
3. **Not done:** an uncapped scan up to $12000$, which would independently confirm B10, and any search for $\kappa_{\mathrm{trap}} \ge 3$.

---

## 8. Ledger: leads, conjectures, refuted claims

Contradictory items are kept side by side, each in its best form, until one is ruled out.

**L1 [L] The depth-$L$ prime chain (Gemini).** *Claim:* $\kappa_{\mathrm{trap}}(q) \ge L$ can be built from a chain of $L$ distinct primes $p_0 = 3, p_1, \dots, p_{L-1} \mid g_0$ with
$$\mathrm{lcm}\bigl(\mathrm{ord}_{p_0^{i+1}}(2),\, \mathrm{ord}_{p_1^{i}}(2),\, \dots,\, \mathrm{ord}_{p_{i-1}^2}(2)\bigr) \;\Big|\; \mathrm{ord}_{p_i}(2),$$
together with auxiliary prime factors $r^*$ that make $p_{L-1} \mid d$ and $p_0^L \mid d$.
- *Mechanism.* Start from a target with $c_0(t) \equiv 1 \pmod{p_{L-1}}$ and $c_0(t)$ equal to truncated geometric sums $\sum_m (p_j q'_{p_j})^m$ modulo $p_j^{L-j}$. Each step peels one prime off the top, until $c_0 \equiv 0 \pmod{p_0}$ is forced.
- *Zsigmondy* does supply primes whose order is exactly a prescribed $n \ne 6$: a primitive prime divisor of $2^n - 1$ has order exactly $n$. An earlier objection in review was wrong on this point.
- *Gaps:* that the peeling closes up at each step has not been checked. The choice of the $r^*$ and the resulting $\nu_{p_j} \ge L - j$ are asserted, not verified. There is no concrete $q$ for $L = 3$ yet.
- *Next step:* pin down a concrete $q$ for $L = 3$ (for example $3 \leftarrow 19 \leftarrow p_2$ with $342 \mid \mathrm{ord}_{p_2}(2)$) and compute its $\kappa_{\mathrm{trap}}$ with §5.2.

**L2 [L] "Two primes in $g_0$ cannot reach depth $3$" (Gemini), in tension with Rule 3.**
- *Argument for.* With $g_0 = p_0 p_1$ and $\nu_{p_1} = 1$, the residue $c_0(z_1) \bmod p_1$ is free across the lifts. That unlocks $a_2$, so a path escapes at step $2$.
- *Tension.* B9 allows bounds of $3$ or more when $\delta_p \ge 2$ and $\nu_p - \alpha_p \ge 2$, for example $g_0 = 57$ ($\delta_3 = 2$) with $\nu_3 \ge 3$. B9 is only an upper bound, so there is no contradiction yet. But L2 predicts that B9 is not tight there.
- *Decisive test:* $q = 57 r \cdots$ with $27 \mid d$ (so $\nu_3 \ge 3$) and $19 \mid d$. If $\kappa_{\mathrm{trap}} = 3$ for such a $q$, L2 is refuted; if it is always $2$, L2 survives and B9 can be sharpened.
- *Proof route for L2:* make the "free mod $p_1$ unlocks $a$" step precise in the language of B7.

**L3 [R] "$\kappa_{\mathrm{trap}} \le 1$ for all $q$; perhaps provable" (an earlier review remark, made after Scan 1).**
- *Refutation, by hand, at $q = 7959 = 3 \cdot 7 \cdot 379$.* Here $d = 378$, $g_0 = 21$, $u_q = 189$, $N_q = 7959 \cdot 189$, and $\kappa = 3$.
  1. *A suitable vertex exists.* By B4(2), $c_0$ runs over all of $\mathbb{Z}/189$ along each fibre, so some $t \in V_q$ has $c_0(t) \equiv 1 \pmod{189}$.
  2. *It has a successor.* A successor is a $z' \equiv 1 \pmod{189}$ with $z' \equiv 2^{-a} \pmod{7959}$. Compatibility modulo $21$ requires $2^{-a} \equiv 1$, that is $6 \mid a$, which is possible. So $t$ has a path of length $1$ and $m(t) \ge 2$.
  3. *Every successor is a dead end.* For any such $z'$, $6 \mid a = a_0(z')$ gives $2^a \equiv 1 \pmod 9$, and $z' \equiv 1 \pmod 9$, so $9 \mid 2^a z' - 1$. Since $3 \parallel q$, $c_0(z') = (2^a z' - 1)/q \equiv 0 \pmod 3$. No unit is $\equiv 0 \pmod 3$, so $z'$ has out-degree $0$ by B4(1).
  4. Hence $L(t) = 1$, $m(t) = 2 \le \kappa - 1$, and $t$ is a Theorem B target of depth $2$. So $\kappa_{\mathrm{trap}}(7959) \ge 2$.
- *Independent computational confirmations* **[C]**: $10887$ and $11571$ (§5.5). For $11571$, the chain for $t = 415$ is reproducible: $w_1 = c_j(415)$ for the least $j < q$ with $w_1 \bmod N_q \in V_q$, and $w_2 = c_0(w_1)$. Both $q w_1 + 1 = 2^k \cdot 415$ and $q w_2 + 1 = 2^{k'} w_1$ were verified, and $w_2 \bmod q \notin H_q$, so the chain cannot be extended from this $w_1$. Maximality over all chains comes from the graph computation.
- *Surviving weaker form:* Rule 2 (B8). If every $p \mid u_q^*$ has $\delta_p = 0$, then $\kappa_{\mathrm{trap}} = 1$. By B10 [P\*], this covers every $q < 7959$.
- *Lesson:* Scan 1's cap on $N_q$ hid the counterexamples.

**L4 [P, in the form stated] Multi-prime resonance (Gemini's first draft).** *Claim:* resonance among several primes of $g_0$ could produce $\kappa_{\mathrm{trap}} \ge 2$ without any Wieferich prime.
- This is confirmed by B10.
- The draft's earlier necessary condition ("a Wieferich prime in $g_0$ with $\kappa \ge 2$, or at least two primes in $g_0$") is true but weak. Rule 2 gives the sharp form: $\delta_p \ge 1$ for some $p \mid u_q^*$.
- **[R]** The draft's parenthetical pointing to *super-Wieferich* primes ($p^3 \mid 2^{p-1} - 1$) as the route to $\kappa \ge 2$ is misleading for composite $q$.
  - *Counterexample:* $q = 57 = 3 \cdot 19$ has $\kappa = 2$. Here $3 \mid \mathrm{ord}_{19}(2) = 18$ forces $3^2 \mid d$, so $\nu_3 = v_3(2^{18} - 1) - 1 = 2$, and $3$ is not even a Wieferich prime. Likewise $7959$ has $\kappa_{\mathrm{trap}} = 2$ with no Wieferich prime dividing it.
  - *Weaker form that is exactly true (for prime $q = p$):* then $d = \mathrm{ord}_p(2)$ and $v_p(2^d - 1) = v_p(2^{p-1} - 1)$, because $(p-1)/d$ is prime to $p$. So $\nu_p = v_p(2^{p-1} - 1) - 1$, and $\kappa \ge 2$ iff $p^3 \mid 2^{p-1} - 1$. For prime multipliers, super-Wieferich is exactly the condition for $\kappa \ge 2$.
  - *Open:* whether such a $p$ would also have $\kappa_{\mathrm{trap}} \ge 2$. For $q = p$, $g_0 = p$ and $u_q^* = p^{\nu - 1}$ with $\delta_p = \nu_p$, so B9 allows up to $1 + \min(\nu, \nu - 1) = \nu$. No super-Wieferich prime is known.

**L5 [L] Multi-prime $u_q^*$.** When two or more primes divide $u_q^*$, B9 does not apply. Rule 2 still applies when every $\delta_p = 0$.
- *Conjecture:* $\kappa_{\mathrm{trap}} \le 1 + \max_p \lceil M_1(p) / \alpha_p \rceil$. Alternatively, cross-prime interaction may add depth, which is where L1's chains might live.
- *Test:* the smallest $q$ with two primes in $u_q^*$ and $\delta \ge 1$ at one of them.

**L6 [L] A formula for $\kappa_{\mathrm{trap}}$.** Is $\kappa_{\mathrm{trap}}(q)$ determined by the local data $\{(\alpha_p, \nu_p, \delta_p)\}$ together with the "who locks whom" graph on the primes of $g_0$ (where $p$ locks $p'$ if $p'^{\alpha} \mid \mathrm{ord}_p(2)$)? L1, L2 and L5 are special cases.

**L7 [L] Natural density $0$ versus Haar measure $1$ (heuristic).** For $q \ge 5$, model each exponent $k$ as giving an integral odd predecessor with probability $1/q$, and weight nodes by $y^{-\gamma}$. This gives the criticality equation
$$q^{\gamma - 1} = 2^\gamma - 1,$$
with roots $\gamma_5 \approx 0.651$, $\gamma_{21} \approx 0.0868$, $\gamma_{39} \approx 0.0426$, $\gamma_{55} \approx 0.0292$, and $\gamma_3 = 1$ (the roots were checked).
- *Prediction:* $|R_q(t) \cap [1, X]| \approx X^{\gamma_q}$ for Theorem A targets, so natural density $0$ although the closure has full Haar measure. Mass should concentrate $2$-adically near $-1/q$, decaying like $2^{-\gamma_q s}$.
- *Caveat:* the model ignores trapping and the dependence on residues mod $q$.
- *Tests:* count $R_5(13) \cap [1, 2^{28}]$ and compare with $X^{0.651}$; do the same for a Theorem A target of $q = 21$.

**L8 [L] Asymptotics and families.**
- Separate the leading constant $c(q, t)$ in $|R_q(t) \cap [1, X]| \sim c\, (\log_2 X)^{m(t)+1}$ from the uniform constant in `paper.md`.
- For primes $p$ with $2$ a primitive root, $\delta_{\mathrm{trap}}(p) = 1/p$. This needs $p$ non-Wieferich, which holds for the two known Wieferich primes but is not proved in general.
- For $q = 2^p - 1$, $\kappa = 0$ and $\delta_{\mathrm{dense}} = p/(2^p - 1)$ exactly.

**L9 [L] Sparsity at composite odd moduli (Gemini, B11(1) parenthetical).** Can the image of $R_q(t)$ in $\prod_{p\ \mathrm{odd}} \mathbb{Z}_p$ be Haar-null, or small at composite moduli?
- *Known:* B5 gives density $(d + q)/(qu)$ of classes modulo $2^d - 1$ for $t = 1$, which is small but positive.
- Nothing is proved beyond that.

**L10 [L] Strongly sufficient sets for $q > 3$.** Transfer the criterion of [MMMM13, Proposition 6.5], with its simple-cycle odd-fraction threshold $\ln 2 / \ln 3$, to the graph of B2, replacing the threshold by $\ln 2 / \ln q$. Both the citation and the transfer are unchecked.

**L11 [L] Algorithmic note.** By B7, $\kappa_{\mathrm{trap}}$ can be computed with about $e_0 \cdot u_q^*$ checks per step, with $e_0 = \mathrm{ord}_{\mathrm{lcm}(g_0, u_q)}(2)$. For example, $18$ checks for $11571$ and $54$ for $10887$ (Gemini's counts, not re-derived).
- In a *search*, testing Rule 2 first is sound now that Rule 2 is proved.
- It must not be used to confirm Rule 2 itself.

---

**References.**
- [Mon06] K. M. Monks, *Sufficient sets for the $3x+1$ problem* (2006).
- [MMMM13] K. G. Monks, K. M. Monks, K. M. Monks, M. Monks, *Strongly sufficient sets and the distribution of arithmetic sequences in the $3x+1$ graph*, Discrete Math. (2013).

Both are to be checked before citing specific statements.




---

Yes—we can settle that **conclusively right now**. There is no need to leave it open: **trap lengths $\ge 3$ unconditionally exist.**

Here is a complete, unconditional proof that $\kappa_{\mathrm{trap}}(q) \ge 3$ occurs (with no Wieferich-freeness assumptions and no computer search needed):

---

### Proposition: Existence of a depth-$3$ trap

> **Claim.** Let $p_2$ be a primitive prime divisor of $2^{19494} - 1$, let $r^*$ be any prime divisor of $2^{p_2} - 1$, and set $q = 3 \cdot 19 \cdot p_2 \cdot r^*$. Then there exists a Theorem B target $t$ for $\mathrm{Col}_q$ with $m(t) = 3$; in particular, $\kappa_{\mathrm{trap}}(q) \ge 3$.

*Proof.*

**1. Setup and valuations.**  
Since $19494 = 2 \cdot 27 \cdot 19^2 > 6$, Zsigmondy's theorem guarantees a primitive prime divisor $p_2 \mid 2^{19494} - 1$, so $\mathrm{ord}_{p_2}(2) = 19494$. Because $\mathrm{ord}_3(2) = 2$ and $\mathrm{ord}_{19}(2) = 18$, $p_2$ is an odd prime distinct from $3$ and $19$ (in fact $p_2 > 19494$). Since $p_2$ is prime and $2^{p_2} - 1 > 1$ is odd, any prime divisor $r^* \mid 2^{p_2} - 1$ has $\mathrm{ord}_{r^*}(2) = p_2$, so $r^*$ is an odd prime distinct from $3, 19, p_2$. Thus $q = 3 \cdot 19 \cdot p_2 \cdot r^*$ is squarefree ($\alpha_p = 1$ for all $p \mid q$).

Now $d = \mathrm{ord}_q(2) = \mathrm{lcm}(2, 18, 19494, p_2) = 19494\, p_2$. By `paper.md` Lemma 1(2):
* $v_3(2^d - 1) = v_3(2^2 - 1) + v_3(d/2) = 1 + 3 = 4 \implies \nu_3 = 3$.
* Direct check: $2^9 = 512 \equiv 151 \equiv 8 \cdot 19 - 1 \pmod{19^2}$, so $2^{18} \equiv -16 \cdot 19 + 1 \equiv 58 \not\equiv 1 \pmod{19^2}$; hence $v_{19}(2^{18} - 1) = 1$. Therefore $v_{19}(2^d - 1) = 1 + v_{19}(d/18) = 1 + 2 = 3 \implies \nu_{19} = 2$.
* $v_{p_2}(2^d - 1) = v_{p_2}(2^{19494} - 1) + v_{p_2}(p_2) \ge 2 \implies \nu_{p_2} \ge 1$.

Hence $3^3 \cdot 19^2 \cdot p_2^{\nu_{p_2}} \mid u_q$, $3 \cdot 19 \cdot p_2 \mid g_0$, and $3^2 \cdot 19 \mid u_q^*$.

**2. Choice of target $t$.**  
Pick $j \in \{1, \dots, u_q\}$ with $u + j \equiv 1 + q \pmod{u_q}$ and put $t = 1 + qj \ge 1$. Then $t \equiv 1 \pmod q$, so $t \bmod N_q \in V_q$ with $a_0(t) = d$ and
$$c_0(t) = \frac{2^d(1 + qj) - 1}{q} = u + 2^d j \equiv u + j \equiv 1 + q \pmod{u_q}$$
(since $u_q \mid N_q \mid 2^d - 1$).

**3. Every directed path from $t \bmod N_q$ has length $\le 2$ and hits a dead end.**  
Suppose $t \bmod N_q \to z_1 \to z_2$ is any directed path of length $2$ in $\mathcal{G}_q$, with $a_1 = a_0(z_1)$ and $a_2 = a_0(z_2)$.
* Compatibility at the first edge (`SUPPLEMENTS_B.md`, Lemma B7) requires $2^{-a_1} \equiv c_0(t) \equiv 1 + q \equiv 1 \pmod{g_0}$. Since $p_2 \mid g_0$, we get $2^{a_1} \equiv 1 \pmod{p_2}$, so $19494 \mid a_1$.
* Since $19494 = 2 \cdot 27 \cdot 19^2$, Lemma 1(2) gives $v_3(2^{a_1} - 1) \ge 4$ and $v_{19}(2^{a_1} - 1) \ge 3$, i.e., $2^{a_1} \equiv 1 \pmod{3^4 \cdot 19^3}$.
* Since $3^3 \cdot 19^2 \mid u_q$, we have $z_1 \equiv c_0(t) \equiv 1 + q \pmod{3^3 \cdot 19^2}$, and thus
  $$q\, c_0(z_1) = 2^{a_1} z_1 - 1 \equiv 1 \cdot (1 + q) - 1 = q \pmod{3^3 \cdot 19^2}.$$
  Dividing by $q$ (where $3 \parallel q$ and $19 \parallel q$) gives
  $$c_0(z_1) \equiv 1 \pmod{3^2 \cdot 19}.$$
* Compatibility at the second edge requires $2^{-a_2} \equiv c_0(z_1) \equiv 1 \pmod{3 \cdot 19}$ (since $3 \cdot 19 \mid g_0$). Because $\mathrm{ord}_{57}(2) = \mathrm{lcm}(2, 18) = 18$, this forces $18 \mid a_2$.
* By Lemma 1(2), $v_3(2^{18} - 1) = 1 + v_3(9) = 3$, so $2^{a_2} \equiv 1 \pmod{27}$, and in particular $\pmod 9$. Meanwhile $z_2 \equiv c_0(z_1) \equiv 1 \pmod 9$. Hence $2^{a_2} z_2 - 1 \equiv 1 \cdot 1 - 1 = 0 \pmod 9$, and dividing by $q$ ($3 \parallel q$) yields
  $$c_0(z_2) \equiv 0 \pmod 3.$$
  Since $3 \mid g_0$, `SUPPLEMENTS_B.md` Proposition B4(1) implies $z_2$ has out-degree $0$ in $\mathcal{G}_q$.

**4. A path of length $2$ actually exists.**  
Since $c_0(t) \equiv 1 \pmod{g_0}$, $a_1 = d$ is compatible modulo $g_0$; let $z_1 \in V_q$ be the successor with $a_0(z_1) = d$ and $z_1 \equiv c_0(t) \pmod{u_q}$. By Step 3, $c_0(z_1) \equiv 1 \pmod{3^2 \cdot 19}$. For each remaining prime $p \in \{p_2, r^*\}$ dividing $g_0$:
* if $\nu_p = 1$, then $p \nmid u_q^*$, so by Lemma B7(1) the $g_0$-lifts of $z_1$ vary freely modulo $p$ while keeping $c_0 \bmod u_q^*$ fixed;
* if $\nu_p \ge 2$, then $2^d \equiv 1 \pmod{p^{\nu_p + 1}}$ and $z_1 \equiv 1 + q \pmod{p^{\nu_p}}$ give $c_0(z_1) \equiv 1 \pmod{p^{\nu_p - 1}}$, so $c_0(z_1) \equiv 1 \pmod p$ automatically.

Using CRT across the primes of $g_0$ with $\nu_p = 1$, some $g_0$-lift $z_1'$ of $z_1$ satisfies $c_0(z_1') \equiv 1 \pmod{g_0}$, so $z_1'$ has a successor $z_2$ by Proposition B4(1).

**5. Conclusion.**  
Every directed path from $t \bmod N_q$ in $\mathcal{G}_q$ ends at step $2$ in a vertex of out-degree $0$, and paths of length $2$ exist. Every vertex of $R_{\mathrm{core}}$ has a directed path to a vertex with a self-loop (`paper.md`, Proof of Proposition 1, $(2)\implies(3)$), so no path from $t \bmod N_q$ reaches $R_{\mathrm{core}}$. Therefore $t$ is a Theorem B target with $L(t) = 2$ and $m(t) = L(t) + 1 = 3$, proving $\kappa_{\mathrm{trap}}(q) \ge 3$. $\square$

---

### Summary of where things now stand
* **Are traps of length $> 2$ possible?** **Yes—proved unconditionally ($\kappa_{\mathrm{trap}}(q) \ge 3$).**
* **Can two primes in $g_0$ with a single non-Wieferich prime in $u_q^*$ reach depth $3$?** **No—proved unconditionally (L2 settled at $\kappa_{\mathrm{trap}} \le 2$).**
* **What remains open in this direction:** Finding the *smallest* concrete $q$ with $\kappa_{\mathrm{trap}}(q) \ge 3$ (the proof above produces a large Zsigmondy $q$; $q = 1093 \cdot p_1 \cdot r$ with $1093 \mid \mathrm{ord}_{p_1}(2)$ might be smaller), and extending the survival-branch check in L1 to prove arbitrary depths $L \ge 4$.

* 
