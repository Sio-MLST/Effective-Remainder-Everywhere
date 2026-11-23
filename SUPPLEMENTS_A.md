# Supplements A to `paper.md`: sharper witnesses for Theorem A

Results sitting alongside `paper.md`: sharper witness bounds for special moduli, full step-count bounds, corollaries of Theorem A, worked examples comparing `paper.md`'s bounds to least witnesses, and explicit residue-class traps. The companion `SUPPLEMENTS_B.md` treats Theorem B, local odd depth, and Wieferich-type multipliers.

**Status.** Nothing in this file is formalized in Lean 4.35, and `paper.md` depends on nothing here. All propositions in §§1–4 below are proved in full from `paper.md` (with S1 and the covering proofs of S4–S5 carried over and adapted from earlier $\kappa = 0$ drafts). Where a statement requires $\kappa = 0$ ($g_0 = 1$, $u_q = 1$, $N_q = q$, $V_q = H_q$), this is stated explicitly; S4, S5, and S6 hold for all $\kappa \ge 0$.

Notation follows `paper.md`: $q > 1$ is odd, $d = \mathrm{ord}_q(2) \ge 2$, $2^d = 1 + qu$, $u_q$, $N_q = q u_q$, $\kappa$, $m = 2^\alpha m_q m'$, $M = m_q m' = m / 2^\alpha$, $e = \mathrm{ord}_{m'}(2) = e_q e'$, $K$, $P = \mathrm{lcm}(dq^K, e)$, $\widetilde{W}_0$, $\widetilde{Q}_0 = \widetilde{W}_0 P$, $H = \langle 2 \rangle \subseteq (\mathbb{Z}/m'\mathbb{Z})^\times$, covering length $\gamma$, $s$, $J_0^*$, $B_0(a)$, $E^*(a)$, and $E^{**}$.

---

## 1. Sharper bounds for special moduli, and step counts

Throughout, $t \ge 1$, $m \ge 1$, and $r, B \in \mathbb{N}$.

### 1.1 Moduli all of whose prime factors divide $q$ ($\kappa = 0$): single exponential

**Proposition S1.** *Assume $\kappa = 0$, $t \bmod q \in H_q$, and every prime factor of $m$ divides $q$ (so $m = m_q$). Then there exists $w \equiv r \pmod m$ with $B < w \le (B+1)\, t\, 2^{d(m+1)}$ and $w \to t$.*

*Proof.* Since $t \bmod q \in H_q$ and $\mathrm{ord}_q(2) = d$, there is $b \in \{0, \dots, d-1\}$ with $2^b t \equiv 1 \pmod q$. For $k \ge 1$ put $R_k = (2^{b + dk} t - 1)/q$. Each $R_k$ is a positive odd integer with $q R_k + 1 = 2^{b + dk} t$, so $R_k \to t$ in $b + dk + 1$ steps (`paper.md`, Lemma 2(1)). For $h \ge 1$,
$$R_{k+h} - R_k = 2^{b+dk}\, t\, \frac{2^{dh} - 1}{q}.$$
Since $t \bmod q \in H_q$, $\gcd(t, q) = 1$, and since every prime factor of $m$ divides $q$, $\gcd(2^{b+dk} t, m) = 1$. Hence $R_{k+h} \equiv R_k \pmod m$ iff $qm \mid 2^{dh} - 1$. For every prime $p \mid m$ (so $p \mid q$), $\kappa = 0$ implies $\nu_p = 0$, and `paper.md` Lemma 1(2) gives $v_p(2^{dh} - 1) = \alpha_p + v_p(h)$. Thus $v_p(qm) = \alpha_p + v_p(m) \le v_p(2^{dh} - 1)$ iff $v_p(m) \le v_p(h)$ for all $p \mid m$, i.e., iff $m \mid h$. Therefore $R_1, \dots, R_m$ lie in distinct residue classes modulo $m$ and cover every class, so there is a unique $k_r \in \{1, \dots, m\}$ with $R_{k_r} \equiv r \pmod m$, and $R_k \equiv r \pmod m$ iff $k \equiv k_r \pmod m$.

Let $k$ be least with $k \equiv k_r \pmod m$ and $R_k > B$, and put $w = R_k$. If $k = k_r \le m$, then $w < 2^{b + dm} t / q < t\, 2^{d(m+1)}$ (since $b < d$ and $q \ge 3$). Otherwise $k - m \ge 1$ and $R_{k-m} \le B$, and $qw + 1 = 2^{dm}(q R_{k-m} + 1) \le 2^{dm}(qB + 1)$ gives $qw < q\, 2^{dm}(B+1)$, hence $w < 2^{dm}(B+1) \le (B+1)\, t\, 2^{d(m+1)}$. $\square$

*Instances.* $q = 5$ ($d = 4$), $m = 5^a$: $(B+1)\, t\, 16^{m+1}$. $q = 3$ ($d = 2$), $m = 3^a$: $(B+1)\, t\, 4^{m+1}$.

*Why $\kappa = 0$ is required.* When $\kappa \ge 1$, `paper.md` Lemma 1(2) gives $v_p(2^{dh} - 1) = \alpha_p + \nu_p + v_p(h)$. For $p \mid g_0 = \gcd(q, u)$, all one-step witnesses $R_k$ lie in the single class $c_0(t) \pmod{g_0}$, so they cannot cover $\mathbb{Z}/m\mathbb{Z}$ when $g_0$ and $m$ share a prime factor.

---

### 1.2 Moduli $m = 2^\alpha m_q$ ($m' = 1$): specialization of Theorem A

**Proposition S2.** *Assume $\kappa = 0$, $t \bmod q \in H_q$, and $m = 2^\alpha m_q \ge 2$ ($m' = 1$). Then Theorem A holds with*
$$E^*(1) = \alpha + d\, q^\alpha m_q + \max\bigl(\lceil \log_2(m_q + 1) \rceil,\; d - 1 - \lfloor \log_2 q \rfloor\bigr) \le d\, m^{\log_2 q} + \alpha + d.$$

*Proof.* When $\kappa = 0$ and $m' = 1$, we have $u_q = 1$, $K = 0$, $e = 1$, $P = d$, $s = 1$, $B_0(1) = 0$, $M = m_q$, $\widetilde{W}_0 = q^\alpha m_q$, and $\widetilde{Q}_0 = d\, q^\alpha m_q$, while `paper.md` Proposition 1 allows $a = 1$. Substituting into `paper.md` Theorem A(1) gives the stated formula for $E^*(1)$.

For the upper bound: since $q \ge 3 > 2$, we have $\log_2 q > 1$, so $m^{\log_2 q} = (2^\alpha m_q)^{\log_2 q} = q^\alpha m_q^{\log_2 q} \ge q^\alpha m_q$. If $m_q = 1$ ($\alpha \ge 1$), then $\lceil \log_2 2 \rceil = 1 < d$ (as $d \ge 2$) and $d - 1 - \lfloor \log_2 q \rfloor < d$, so $E^*(1) \le d\, m^{\log_2 q} + \alpha + d$. If $m_q \ge 3$, then $\log_2 q \ge \log_2 3 > 1.584$, so $m_q^{\log_2 q} - m_q \ge m_q^{1.584} - m_q > \frac{1}{2}\lceil \log_2(m_q + 1) \rceil$ (at $m_q = 3$, $3^{1.584} - 3 > 2.69 > 1 = \frac{1}{2}\lceil \log_2 4 \rceil$, and the left side grows faster than $\log_2(m_q+1)+1$ for $m_q \ge 3$). Multiplying by $d\, q^\alpha \ge 2$ gives $d\, m^{\log_2 q} - d\, q^\alpha m_q > \lceil \log_2(m_q + 1) \rceil$, while $d - 1 - \lfloor \log_2 q \rfloor < d$, yielding $E^*(1) \le d\, m^{\log_2 q} + \alpha + d$. $\square$

For $\alpha = 0$ and $m_q$ a prime power, Proposition S1 is sharper (linear in $m$). The superlinear $q^\alpha$ factor for $\alpha > 0$ comes from the $q$-adic precision $q^n m_q$ ($n \le \alpha$) needed by the $2$-adic tail (`paper.md`, Lemma 8); S1's one-odd-step witnesses cannot help when $\alpha > 0$ because for large $k$ they all lie in $-q^{-1} \bmod 2^\alpha$.

---

### 1.3 Sharper covering lengths modulo $m'$ (valid for all $\kappa \ge 0$)

In `paper.md`, Theorem A depends on $m'$ through the minimal covering length $\gamma$ (`Lemma 3`). Note that $E^*(a)$ and $E^{**}$ are strictly increasing in $\gamma$: increasing $\gamma$ by $1$ increases $s$ and $B_0(a)$ by $1$ and $e$ respectively, raising the exponent by $J_0^* P + e - (\lfloor (s'+1)\log_2 q \rfloor - \lfloor s'\log_2 q \rfloor) \ge (q-1)d + e - \lceil \log_2 q \rceil > 0$ (since $q \ge 3$ and $d \ge 2$). Consequently, Theorem A remains valid if $\gamma$ is replaced in $s$, $B_0(a)$, $E^*(a)$, and $E^{**}$ by any upper bound $\gamma' \ge \gamma$, i.e. any $\gamma'$ with $A_{\gamma'} = \mathbb{Z}/m'\mathbb{Z}$ (monotonicity holds because $A_k = \mathbb{Z}/m'\mathbb{Z} \implies A_{k+1} = A_k + q^k H \supseteq A_k + q^k = \mathbb{Z}/m'\mathbb{Z}$).

**Remark (relation to parity words).** In older drafts, steering modulo $m'$ was phrased via a parity word $\omega$ of length $\le (s+1)e - 1$ (`Lemma S3`). In `paper.md`, this is subsumed by `Lemma 9`, which directly steers modulo $m'$ via backward odd steps $b_{K_0+1}, \dots, b_s \in \{1, \dots, e\}$.

For two families of $m'$, $\gamma$ is far smaller than the Chowla bound $1 + \lceil \max(0, m'-e)/\varphi(e) \rceil$ of `paper.md`, Lemma 3.

**Proposition S4 (prime power with $2$ a primitive root).** *Let $m' = p^k$ ($k \ge 1$) with $p$ an odd prime and $2$ a primitive root modulo $p^k$, and let $\gcd(m', q) = 1$. Then $A_2 = \mathbb{Z}/m'\mathbb{Z}$, so $\gamma = 2$. Hence Theorem A holds for all $\kappa \ge 0$ with $s = K + \kappa + 4$ (and $B_0(a) = (K + \kappa + 1)a + 2e$).*

*Proof.* Since $2$ is a primitive root modulo $p^k$, $H = (\mathbb{Z}/p^k\mathbb{Z})^\times$, so $A_1 = H \neq \mathbb{Z}/p^k\mathbb{Z}$ and $\gamma \ge 2$. Let $y \in \mathbb{Z}/p^k\mathbb{Z}$. Because $p \ge 3$, there are at least $p - 1 \ge 2$ residue classes in $\{1, \dots, p - 1\} \subseteq (\mathbb{Z}/p\mathbb{Z})^\times$; choose $h_1 \in \{1, \dots, p - 1\}$ with $q h_1 \not\equiv y \pmod p$. Since $\gcd(p, q) = 1$, $h_1$ is a unit modulo $p^k$, and $h_0 := y - q h_1 \not\equiv 0 \pmod p$ is also a unit modulo $p^k$. Thus $h_0, h_1 \in H$ and $y = h_0 + q h_1 \in A_2$. $\square$

**Proposition S5 (bounded index of $q$ modulo $\langle 2 \rangle$).** *Let $m' > 1$ be odd and prime to $q$, let $\lambda_H \ge 1$ be the least integer with $q^{\lambda_H} \in H$ (the order of $q$ in $(\mathbb{Z}/m'\mathbb{Z})^\times / H$), and put $s_0 = \lceil \log_2(m' + 1) \rceil$. Then $A_{\lambda_H s_0} = \mathbb{Z}/m'\mathbb{Z}$, so $\gamma \le \lambda_H s_0$. Hence Theorem A holds for all $\kappa \ge 0$ with $s$ replaced by $K + \kappa + \lambda_H s_0 + 2$.*

*Proof.* The integer $\lambda_H$ exists because $\gcd(q, m') = 1$ makes $q \bmod m' \in (\mathbb{Z}/m'\mathbb{Z})^\times$. Let $x \in \mathbb{Z}/m'\mathbb{Z}$, let $c_0 \in \{1, \dots, m'\}$ represent $x$, and put $c_r = m'$ for $1 \le r < \lambda_H$, so $c_r \equiv 0 \pmod{m'}$ for $r \ge 1$. Since $1 \le c_r \le m' < 2^{s_0}$, each $c_r$ is a sum of at most $s_0$ distinct powers of $2$ (its binary expansion), and at least $1$ power of $2$. Because $m' > 1$ is odd, $e = \mathrm{ord}_{m'}(2) \ge 2$, so in $\mathbb{Z}/m'\mathbb{Z}$ we can split any term $2^j$ with $j \ge 1$ as $2^{j-1} + 2^{j-1}$, and $2^0$ as $2^e = 2^{e-1} + 2^{e-1}$. Each split increases the number of summands by $1$, so after finitely many splits each $c_r$ is written modulo $m'$ as a sum of **exactly** $s_0$ elements of $H$:
$$c_r \equiv \sum_{u=0}^{s_0 - 1} 2^{j_{r,u}} \pmod{m'} \qquad (0 \le r < \lambda_H).$$
For $0 \le r < \lambda_H$ and $0 \le u < s_0$, set $i = r + \lambda_H u$, which runs bijectively over $\{0, \dots, \lambda_H s_0 - 1\}$, and $h_i = q^{-\lambda_H u} 2^{j_{r,u}} \bmod m'$. Because $q^{\lambda_H} \in H$, each $h_i \in H$, and $q^i h_i \equiv q^r 2^{j_{r,u}} \pmod{m'}$. Summing gives
$$\sum_{i=0}^{\lambda_H s_0 - 1} q^i h_i \equiv \sum_{r=0}^{\lambda_H - 1} q^r \sum_{u=0}^{s_0 - 1} 2^{j_{r,u}} \equiv \sum_{r=0}^{\lambda_H - 1} q^r c_r \equiv c_0 \equiv x \pmod{m'}.$$
Thus $A_{\lambda_H s_0} = \mathbb{Z}/m'\mathbb{Z}$, so $\gamma \le \lambda_H s_0$. $\square$

*Instances.* When $q \in \langle 2 \rangle \bmod m'$, $\lambda_H = 1$ and $\gamma \le \lceil \log_2(m'+1) \rceil$. When $m' = 2^k - 1$ and $q \equiv 2^a \pmod{m'}$, $e = k$ so Chowla gives a bound of order $m'/k$, whereas Proposition S5 gives $\gamma \le k$.

---

### 1.4 Table of bounds (all $\kappa \ge 0$ unless marked $\kappa = 0$)

| moduli $m$ | theorem / exponent of $2$ | source |
| --- | --- | --- |
| all $m$, all $\kappa \ge 0$ | $E^*(a)$ (if $t$ satisfies (H) with $a$) or $E^{**}$ | `paper.md`, Theorem A |
| odd $m = m_q$, $\kappa = 0$ | $d(m+1)$ | Proposition S1 |
| $m = 2^\alpha m_q$ ($m'=1$), $\kappa = 0$ | $\alpha + d\, q^\alpha m_q + \max\bigl(\lceil\log_2(m_q+1)\rceil,\, d - 1 - \lfloor\log_2 q\rfloor\bigr) \le d\, m^{\log_2 q} + \alpha + d$ | Proposition S2 |
| $m' = p^k$, $2$ a primitive root mod $p^k$ | `paper.md`, Theorem A with $\gamma = 2$, $s = K + \kappa + 4$ | Proposition S4 |
| $q^{\lambda_H} \in \langle 2 \rangle \bmod m'$, $\lambda_H$ least | `paper.md`, Theorem A with $\gamma \le \lambda_H \lceil\log_2(m'+1)\rceil$ | Proposition S5 |

---

### 1.5 Number of steps in `paper.md`'s construction (all $\kappa \ge 0$)

**Proposition S6.** *Let $w$ be the witness constructed in `paper.md` §4 for $(q, t, m, r, B)$. Then $\mathrm{Col}_q^T(w) = t$ with total steps $T$ and odd steps $T_{\mathrm{odd}}$ bounded by:*
1. *If $t$ itself satisfies Hypothesis (H) with exponent $a \in \{1, \dots, d\}$:*
   $$T_{\mathrm{odd}} = n + s \le \alpha + s,$$
   $$T \le 2\alpha + s + \widetilde{Q}_0 + dq^K - 1 + (s-1)J_0^* P + B_0(a) + \bigl\lfloor (\alpha + 1)\log_2 q + \log_2(B + M + 1) \bigr\rfloor.$$
2. *If $t$ does not satisfy (H) (then $\kappa \ge 1$):*
   $$T_{\mathrm{odd}} = n + s + \kappa + 1 \le \alpha + s + \kappa + 1,$$
   $$T \le 2\alpha + s + \kappa + 1 + \widetilde{Q}_0 + dq^K - 1 + (s-1)J_0^* P + B_0(1) + (\kappa+1)dq + \bigl\lfloor (\alpha + 1)\log_2 q + \log_2(B + M + 1) \bigr\rfloor.$$
*Furthermore, when $m' > 1$, $\alpha + s \le \log_2 m + \kappa + \gamma + 2$.*

*(Note: $T$ bounds the first time the orbit of $w$ reaches $t$; it need not equal it.)*

*Proof.* Trace the four stages of `paper.md` §4:
- *Tail (`Step 2`, `Lemma 7`, `Lemma 8`):* $w \to y_s = S_\sigma(w)$ uses the parity word $\sigma$ of length $\alpha$ with $n = \mathrm{ones}(\sigma) \le \alpha$ ones. Each letter $\delta \in \{0, 1\}$ executes $1 + \delta$ steps of $\mathrm{Col}_q$, totaling $\alpha + n$ steps ($n$ odd).
- *Backward odd chain (`Step 1`, `Lemmas 9, 12, 13`):* Each step $y_l \to y_{l-1}$ satisfies $\mathrm{Col}_q(y_l) = 2^{a_l} y_{l-1}$, taking $1 + a_l$ steps ($1$ odd). Across $l = 1, \dots, s$, this takes $s + \sum_{l=1}^s a_l$ steps ($s$ odd).
- *Primer alignment (`Lemma 5`):* $y_0 = 2^{\lambda_0} x \to x$ takes $\lambda_0 \le dq^K - 1$ halvings ($0$ odd).
- *Target alignment (`Proposition 1`):* In Case 1, $x = t$ ($0$ steps). In Case 2, `Proposition 1` constructs $x$ from $t$ in $\kappa + 1$ backward odd steps, each with halving exponent $a_0 + dj \le d + d(q-1) = dq$, taking at most $(\kappa+1)(dq+1)$ steps ($\kappa+1$ odd).

Thus $T_{\mathrm{odd}} = n + s \le \alpha + s$ in Case 1 (and $+\kappa+1$ in Case 2). For the exponent sum $\lambda_0 + \sum_{l=1}^s a_l$:
- From `Lemma 5`, `Lemma 12`, and `Step 4` of `paper.md`, $\lambda_0 + \sum_{l=1}^{s-1} a_l \le dq^K - 1 + (s-1)J_0^* P + B_0(a)$ (with $a = 1$ in Case 2).
- For $a_s$, `Step 5` distinguishes $k_0 = 0$, where $a_s \le \widetilde{Q}(n) \le \widetilde{Q}_0$, and $k_0 \ge 1$, where minimality of $k_0$ gives $2^{a_s - \widetilde{Q}(n)} y_{s-1} \le q\Theta < q^{n+1}(B + M + 1)$. Since $y_{s-1} \ge 1$, $n \le \alpha$, and $\widetilde{Q}(n) \le \widetilde{Q}_0$, taking base-$2$ logarithms yields
  $$a_s \le \widetilde{Q}_0 + \bigl\lfloor (\alpha + 1)\log_2 q + \log_2(B + M + 1) \bigr\rfloor,$$
  which also holds when $k_0 = 0$ (since $q \ge 3$ and $B + M + 1 \ge 2$).

Summing all step counts and using $n \le \alpha$ yields the bounds on $T$. Finally, if $m' > 1$, then $e_q \le e \le m'$ and minimality of $K$ implies $e_q \ge p^K \ge 3^K > 2^K$ whenever $K \ge 1$ (and $1 \le e_q$ if $K = 0$), so $2^{\alpha + K} \le 2^\alpha e_q \le 2^\alpha m' \le m$, giving $\alpha + K \le \log_2 m$ and $\alpha + s = \alpha + K + \kappa + \gamma + 2 \le \log_2 m + \kappa + \gamma + 2$. $\square$

---

## 2. Corollaries of Theorem A

Let $q > 1$ be odd and $t \ge 1$ satisfy the hypothesis of `paper.md` Theorem A (equivalently, `Proposition 1`: $t \bmod N_q \in V_q$ has a directed path of length $\kappa$ in $\mathcal{G}_q$; for $\kappa = 0$, simply $t \bmod q \in H_q$).

**No congruence obstruction.** Any set defined by a finite Boolean combination of congruences is a union of residue classes modulo the $\mathrm{lcm}$ of its moduli, so if nonempty it contains a predecessor of $t$ (with the witness bound of Theorem A).

**Infinitude.** Reapplying Theorem A with $B$ replaced by a predecessor already found yields infinitely many predecessors of $t$ in every residue class modulo every $m \ge 1$.

**Sufficient sets** (in the sense of Monks [Mon06]). Call $S \subseteq \mathbb{Z}_{\ge 1}$ *sufficient* for $\mathrm{Col}_q$ if the forward orbit of every positive integer meets the orbit of an element of $S$.
- For $\kappa = 0$: let $x \ge 1$ and let $y$ be the odd integer reached by halving $x$; then $t = qy + 1 \equiv 1 \pmod q$ lies in the orbit of $x$ and satisfies $t \bmod q \in H_q$, so Theorem A applies to $t$ and every arithmetic progression $a + b\mathbb{N}$ ($b \ge 1$) is sufficient.
- For $\kappa \ge 1$: the same argument works for every $x \ge 1$ whose forward orbit hits a target satisfying `Proposition 1`. That *every* $x \ge 1$ hits such a target within $\kappa + 1$ odd steps—making every arithmetic progression sufficient for all odd $q > 1$—is proved in `SUPPLEMENTS_B.md`, Proposition B1.

**Cycles.** Every element $t$ of a cycle of $\mathrm{Col}_q$ satisfies $t \bmod q \in H_q$: walking backward around the cycle from $t$, the first odd element $x$ reached satisfies $qx + 1 = 2^k t$ ($k \ge 0$). For $\kappa = 0$, Theorem A therefore applies to every cycle element, so the predecessors of every cycle element meet every class modulo every $m$. For $\kappa \ge 1$, every periodic $t$ satisfies `Proposition 1` by `paper.md` Theorem B(3) (`SUPPLEMENTS_B.md`, Proposition B1(1)), so the same holds for all odd $q > 1$.

---

## 3. Worked examples: `paper.md` bounds versus least witnesses

### 3.1 Non-Wieferich case: $q = 5$ ($\kappa = 0$, $d = 4$, $u_q = 1$), $t = 7$

Here $7 \equiv 2 \pmod 5$, so $t$ satisfies (H) with $a = 1$, $i_0 = 2$ (and $11 \to 56 \to 28 \to 14 \to 7$).

* **$m = 11$, $r = 0$, $B = 0$:** The least witness is $11$. Here $\alpha = 0$, $m_q = 1$, $m' = M = 11$, $e = \mathrm{ord}_{11}(2) = 10 = 5 \cdot 2$ ($e_q = 5, K = 1$), $P = \mathrm{lcm}(20, 10) = 20$, $\widetilde{W}_0 = 1$, $\widetilde{Q}_0 = 20$. By `paper.md` Lemma 3 (or Proposition S4), $\gamma = 2$, so $s = 5$, $J_0^* = 4$, $B_0(1) = 22$, and $\lfloor 5 \log_2 5 \rfloor = 11$. Theorem A gives
  $$E^*(1) = 0 + 20 + \max\bigl(4,\; 19 + 4\cdot 4\cdot 20 + 22 - 11\bigr) = 370,$$
  yielding $w \le 7 \cdot 2^{370} \approx 1.7 \cdot 10^{112}$ ($113$ digits).

* **$m = 10$, $r = 1$, $B = 0$:** The only smaller candidate, $1$, stays on the cycle $1 \to 6 \to 3 \to 16 \to 8 \to 4 \to 2 \to 1$, so the least witness is again $11$. Here $\alpha = 1$, $m_q = M = 5$, $m' = 1$, $K = 0$, $e = 1$, $P = 4$, $\widetilde{W}_0 = \mathrm{lcm}(25, 1) = 25$, $\widetilde{Q}_0 = 100$, $s = 1$, $B_0(1) = 0$. Theorem A (Proposition S2) gives
  $$E^*(1) = 1 + 100 + \max\bigl(3,\; 3 - 2\bigr) = 104,$$
  yielding $w \le 7 \cdot 2^{104} \approx 1.4 \cdot 10^{32}$ ($33$ digits).

### 3.2 Wieferich case: $q = 21 = 3 \cdot 7$ ($\kappa = 1$, $d = 6$, $u_q = 3$, $N_q = 63$), $t = 53$

Here $(2^1 - 21) \cdot 53 = -1007 \equiv 1 \pmod{63}$, so $t = 53$ satisfies (H) with $a = 1, i_0 = 0$. Take $m = 5$, $r = 0$, $B = 0$: $\alpha = 0$, $m_q = 1$, $m' = M = 5$, $e = 4$, $K = 0$, $P = 12$, $\widetilde{W}_0 = 1$, $\widetilde{Q}_0 = 12$. Here $H = (\mathbb{Z}/5\mathbb{Z})^\times$, so $\gamma = 2$ (Proposition S4), $s = 5$, $B_0(1) = 10$, and $\lfloor 5 \log_2 21 \rfloor = 21$. Because $q = 21$ is composite with $\kappa = 1$, `paper.md` Lemma 12 uses $E_3^* = 7^2 = 49$, $E_7^* = 3^1 = 3$, giving $J_0^* = 2\cdot 49 + 6\cdot 3 = 116$, and
$$E^*(1) = 0 + 12 + \max\bigl(3,\; 5 + 4\cdot 116\cdot 12 + 10 - 21\bigr) = 5574.$$
As a function of $m$ for fixed $q$, the exponent remains polynomial in $m$, though for composite Wieferich $q$ the constant $J_0^*$ scales roughly like $q^{\kappa + 1}$ rather than $q - 1$.

*Heuristic observation (unproved).* For $5x+1$, $t = 1$, a truncated inverse search of the backward tree finds predecessors in every class modulo $2^\alpha$ ($\alpha \le 8$) and modulo $5^a$ ($a \le 4$), all below $2^{22}$, whereas Proposition S1 gives $2^{2504}$ for $m = 625$. Because the search discards values above a cap, the numbers found are only upper bounds for least witnesses, and a class not found is no evidence of absence.

---

## 4. Explicit trapped classes (certificate form of Theorem B)

In `paper.md`, Theorem B takes $g > 1$ dividing $q$ with $\mathrm{ord}_{qg}(2) = d = \mathrm{ord}_q(2)$ (equivalently $qg \mid 2^d - 1$, so $g \mid g_0$) and defines the backward-closed trapped set
$$T_g = \{x \ge 1 : x \equiv 2^i \pmod{qg} \text{ for some } i \ge 0\} \cup \{x \ge 1 : g \mid x\}.$$
If $t \in T_g$, then every $x \in R_q(t)$ lies in $T_g$ (`paper.md` §1, Theorem B).

*Example.* $q = 21$, $g = 3$, $d = 6$: $T_3$ consists of the classes $1, 2, 4, 8, 16, 32$ and the multiples of $3$ modulo $63$. The class $5 \pmod{63}$ is outside $T_3$, so no $x \equiv 5 \pmod{63}$ reaches $1$ under $21x+1$.

*Relation to `paper.md` Theorem B and `SUPPLEMENTS_B.md` §4.* The residue-class union $T_g$ acts as a short congruence certificate: it catches all targets with $t \bmod q \notin H_q$, plus the depth-$0$ sinks where $c_0(t) \equiv 0 \pmod g$ (`SUPPLEMENTS_B.md`, Proposition B4). `paper.md` Theorem B is strictly stronger when $\kappa \ge 1$: it bounds the odd depth of *every* target in $\mathcal{T}_q$ (including those with $c_0(t) \not\equiv 0 \pmod{g_0}$ that nevertheless fail to reach $R_{\mathrm{core}}$ in $\kappa$ steps) and gives Haar measure $0$.

---

## 5. Open questions

1. Is the exponent linear in $m$ for powers of $2$ and for mixed moduli $2^\alpha m_q$?
2. Does $\gamma(q, m') = O(\log m')$ hold in general (`paper.md`, §7.2(ii) of earlier draft)? Combined with `paper.md` Theorem A, this would replace the Chowla factor $m'/\varphi(e)$ in $s$ by $O(K + \kappa + \log m')$.
3. Can the composite-$\kappa \ge 1$ shift ceiling $J_0^* \sim q^{\kappa + 1}$ in `paper.md` Lemma 12 be reduced (e.g. via coupled CRT shifts) closer to $q - 1$?
4. For $\kappa \ge 1$ and $m$ coprime to $g_0$ (or $m = m_q$ with $\gcd(m, g_0) = 1$), does a linear-exponent bound analogous to Proposition S1 hold?
5. *(Settled in `SUPPLEMENTS_B.md`, Proposition B1.)* For $\kappa \ge 1$, every cycle element and some point on every forward orbit satisfies `paper.md` Proposition 1, extending sufficiency to all odd $q > 1$.
6. Formalize S1, S2, S4, S5, and S6 in Lean 4.35 alongside `paper.md`'s modules.
