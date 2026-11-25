# Supplements A: sharper witness bounds for Theorem A

Theorem A of `paper.md` gives, for a dense target $t$, a predecessor $w \to t$ in any residue class $r \bmod m$ above any threshold $B$, with $w \le (B+1)\, t\, 2^{E}$ for an explicit exponent $E$. This supplement improves $E$ in two ways and maps which bound is best in which regime.

1. **One improvement for composite $q$.** The shifts in the construction can be kept below $q$ for every $\kappa$, instead of below a ceiling of order $q^{\kappa+1}$ (§2). For prime $q$ the ceiling was already $q - 1$.
2. **One pointwise refinement.** The exponent can use the actual number $n$ of odd steps in the $2$-adic tail, which depends on $r \bmod 2^\alpha$, instead of its maximum $\alpha$ (§3).
3. **Regimes where something simpler wins.** One-odd-step witnesses give a much smaller exponent for moduli built from primes of $q$ (§4). For two families of $m'$ the covering length $\gamma$ is far below the Chowla bound (§5). Section 6 tabulates the results.
4. **Step counts** for the constructed witness (§7).

All of this stays inside the construction of `paper.md`, and §8 explains why that construction is far from optimal. Real least witnesses are astronomically smaller than any bound here, and a substantially better bound would need a different strategy. Open questions are in §9.

---

## 1. Notation

As in `paper.md`: $q > 1$ odd, $d = \mathrm{ord}_q(2)$, $2^d = 1 + qu$, $g_0 = \gcd(q,u)$, $\alpha_p = v_p(q)$, $\nu_p = v_p(u)$, $u_q = \prod_{p \mid q} p^{\nu_p}$, $N_q = q u_q$, $\kappa = \max_p \lceil \nu_p/\alpha_p \rceil$, $H_q = \langle 2 \rangle \subseteq (\mathbb{Z}/q)^\times$, Hypothesis (H) with exponent $a$, and the graph $\mathcal{G}_q$.

For a modulus $m$, write $m = 2^\alpha m_q m'$ with every prime of $m_q$ dividing $q$ and $\gcd(m', q) = 1$, and $M = m_q m'$. Let $e = \mathrm{ord}_{m'}(2) = e_q e'$ (primes of $e_q$ divide $q$, $\gcd(e', q) = 1$), $K = \min\{k : e_q \mid q^k\}$ and $P = \mathrm{lcm}(d q^K, e)$. For $0 \le n \le \alpha$ put
$$\widetilde W(n) = \frac{\mathrm{lcm}(q^n m_q,\, q^K u_q)}{q^K u_q}, \qquad \widetilde Q(n) = \widetilde W(n)\, P.$$
With $H = \langle 2 \rangle \subseteq (\mathbb{Z}/m')^\times$, let $A_k = \{h_0 + q h_1 + \dots + q^{k-1} h_{k-1} : h_i \in H\}$ and let the *covering length* be $\gamma = \min\{k : A_k = \mathbb{Z}/m'\}$. Set $s = \kappa + 1$ if $m' = 1$ and $s = K + \kappa + \gamma + 2$ otherwise, and $B_0(a) = \kappa a$ if $m' = 1$ and $(K + \kappa + 1)a + \gamma e$ otherwise.

For the target class $r$, let $\sigma$ be the $\alpha$-letter accelerated parity word of $r \bmod 2^\alpha$, $n = \mathrm{ones}(\sigma)$, and $\rho = S_\sigma(r \bmod m) < q^n M$, as in the tail step of `paper.md`.

---

## 2. Shifts below $q$ for every $\kappa$

In `paper.md` the shifts $j_1, \dots, j_{s-1}$ of the backward chain are chosen digit by digit, one prime $p \mid q$ at a time. To stop a digit chosen at $p$ from disturbing digits already fixed at another prime $p'$, each digit at $p$ is multiplied by a weight
$$E_p^* = \prod_{p' \ne p} p'^{\max(\alpha_{p'},\, (\kappa+1)\alpha_{p'} - \nu_{p'})}.$$
This gives the shift ceiling $J_0^* = \sum_p (p^{\alpha_p} - 1) E_p^*$, of order $q^{\kappa+1}$ for composite $q$ with $\kappa \ge 1$. The weights are unnecessary. Work at each prime separately in the local ring $\mathbb{Z}_{(p)}$, where the other primes of $q$ are units, and assemble each shift by CRT.

**Theorem A1.** *In the construction of Theorem A, the shifts can be chosen with $0 \le j_k \le q - 1$, for every odd $q$ and every $\kappa \ge 0$. Equivalently, $J_0^*$ may be replaced by $q - 1$.*

*Proof.* Each constraint the construction must meet is a digit condition $(T, p, h)$: the iterate $y_T$ must have a prescribed digit at $p^h$. As in `paper.md`, each such constraint has a unique controller $(k, v)$, the shift index $k$ and the $p$-adic digit position $v < \alpha_p$ of $j_k$ that moves it, related by $h = (K + k - T)\alpha_p + \nu_p + v$.

Fix $p$ and work in $\mathbb{Z}_{(p)} = \mathbb{Z}[1/q'_p]$, where $q = p^{\alpha_p} q'_p$. If $y_{l-1} \in \mathbb{Z}_{(p)}$ has the right residue modulo $p^{\alpha_p}$, then $y_l = (2^{a_l} y_{l-1} - 1)/q \in \mathbb{Z}_{(p)}$. So $p$-integrality can be tracked at each prime separately.

*Order.* Two facts make a single left-to-right pass work.
- At fixed $(k, p)$, increasing $v$ visits the constraints $(T, h)$ in increasing lexicographic order, because $(T_2 - T_1)\alpha_p + (h_2 - h_1) = v_2 - v_1 \in [1, \alpha_p - 1]$.
- Every $p$-integrality constraint at an earlier step $l < T$ has a lexicographically earlier controller, because $(k - k')\alpha_p + (v - v') = (T - l)\alpha_p + (h - h') \ge 1$.

*Construction.* For $k = 1, \dots, s-1$ in turn, and independently for each $p \mid q$, choose the digits $\beta_{k,p,0}, \dots, \beta_{k,p,\alpha_p - 1}$ of $\tilde j_{k,p} = \sum_v \beta_{k,p,v} p^v$, holding later shifts at $0$. When digit $v$ is chosen, all earlier steps are already $p$-integral with the right residues, and since $v_p(2^P - 1) = (K+1)\alpha_p + \nu_p$ and $y_{k-1}$ is a $p$-adic unit, the $p$ choices of $\beta_{k,p,v}$ fix $y_T \bmod p^h$ and run over all $p$ lifts modulo $p^{h+1}$. Take the one that matches. Then let $j_k \in [0, q-1]$ be the CRT solution of $j_k \equiv \tilde j_{k,p} \pmod{p^{\alpha_p}}$ for all $p$.

*Nothing is disturbed.* Replacing $\tilde j_{k,p}$ by $j_k$ changes the shift by a multiple of $p^{\alpha_p}$, and setting a later shift $j_{k'}$ changes $y_T$ by
$$v_p(\Delta y_T) \ge (K + k' - T)\alpha_p + \nu_p \ge h - v + \alpha_p \ge h + 1,$$
and changes each intermediate $y_l$ ($k' \le l < T$) by valuation $\ge \alpha_p$. So all digits fixed so far, at every prime, survive.

At the end every $y_l$ lies in $\mathbb{Z}[1/q] \cap \bigcap_{p \mid q} \mathbb{Z}_{(p)} = \mathbb{Z}$, all steps are integral, $y_s \equiv \rho \pmod{q^K u_q}$, and every $j_k \le q - 1$. $\square$

*Example.* For $q = 21$ ($\kappa = 1$, $d = 6$, $u_q = 3$) and $t = 53$, which satisfies (H) with $a = 1$, take $m = 5$, $r = 0$, $B = 0$. Then $e = 4$, $K = 0$, $P = 12$, $\gamma = 2$, $s = 5$, $B_0(1) = 10$. The weights of `paper.md` are $E_3^* = 49$, $E_7^* = 3$, so $J_0^* = 116$ and the exponent is $5574$. With $J_0^* = 20$ it is
$$12 + \bigl(5 + 4 \cdot 20 \cdot 12 + 10 - 21\bigr) = 966.$$

---

## 3. The exponent depends on $r$

The uniform exponents $E^*(a)$ and $E^{**}$ of `paper.md` round the number $n$ of odd tail steps up to $\alpha$, the tail period $\widetilde Q(n)$ up to $\widetilde Q(\alpha)$, and the factor $q^{-n}$ up to $1$. Keeping the exact $n$, together with Theorem A1, gives:

**Proposition A2.** *Let $n = \mathrm{ones}(\sigma)$, determined by $r \bmod 2^\alpha$.*
1. *If $t$ satisfies (H) with exponent $a$, the constructed witness satisfies*
$$w < \max\Bigl(2^{\alpha + \widetilde Q(n)}(B + M + 1),\ \ 2^{\alpha + \widetilde Q(n) + dq^K - 1 + (s-1)(q-1)P + B_0(a)}\, t\, /\, q^{n+s}\Bigr) \le (B+1)\, t\, 2^{E^*(a,n)},$$
$$E^*(a, n) = \alpha + \widetilde Q(n) + \max\Bigl(\lceil \log_2(M+1) \rceil,\ dq^K - 1 + (s-1)(q-1)P + B_0(a) - \lfloor (n+s)\log_2 q \rfloor\Bigr).$$
2. *If $t$ does not satisfy (H), the same holds with $a = 1$, an extra $(\kappa+1)dq$ in the second argument, and $q^{n+s+\kappa+1}$ in place of $q^{n+s}$. This is the exponent $E^{**}(n)$.*

*Proof.* This is the final size estimate of Theorem A, with $j_l \le q - 1$ from Theorem A1 and without the rounding. If the last exponent needs no correction ($k_0 = 0$), then $a_s \le \widetilde Q(n)$ and $w < 2^{\alpha + \widetilde Q(n)} y_{s-1}/q^{n+1}$, with $y_{s-1}$ bounded by the product of the earlier steps. Otherwise minimality of the correction gives $2^{a_s - \widetilde Q(n)} y_{s-1} \le q\Theta$ with $\Theta = \rho + q^n(B+1) < q^n(B + M + 1)$. In case 2, $x \le (2^{dq}/q)^{\kappa+1} t$ by Proposition 1 of `paper.md`. $\square$

*Example.* For $q = 5$, $t = 7$, $m = 10$ ($\alpha = 1$, $m_q = 5$, $m' = 1$, $P = 4$, $s = 1$), the uniform exponent is $104$. That is the case $r$ odd ($n = 1$, $\widetilde Q = 100$). For $r$ even, $n = 0$, $\widetilde Q(0) = 20$ and the exponent is $24$, which saves $80$ bits. The least witness for $r = 1$ is $11$.

*When $m' = 1$ and $\kappa = 0$*, Proposition A2 reduces to $E^*(1, n) \le d\, m^{\log_2 q} + \alpha + d$. The exponent is polynomial in $m$, of degree $\log_2 q$. The superlinear factor $q^\alpha$ comes from the $q$-adic precision $q^n m_q$ the $2$-adic tail needs.

---

## 4. One odd step: moduli built from primes of $q$

When $m$ involves only primes of $q$ and avoids $g_0$, the whole construction is unnecessary. The single-odd-step predecessors of $t$ already run through every class.

**Proposition A3.** *Let $t \bmod q \in H_q$, let every prime of $m$ divide $q$, and let $\gcd(m, g_0) = 1$. Then for all $r, B$ there is $w \equiv r \pmod m$ with $w \to t$ and*
$$B < w \le (B+1)\, t\, 2^{d(m+1)}.$$

*Proof.* Choose $b < d$ with $2^b t \equiv 1 \pmod q$ and put $R_k = (2^{b+dk} t - 1)/q$, so $q R_k + 1 = 2^{b+dk} t$ and $R_k \to t$. Then
$$R_{k+h} - R_k = 2^{b+dk}\, t\, \frac{2^{dh} - 1}{q},$$
and $2^{b+dk} t$ is prime to $m$, so $R_{k+h} \equiv R_k \pmod m$ iff $qm \mid 2^{dh} - 1$. At each $p \mid m$, $\gcd(m, g_0) = 1$ gives $\nu_p = 0$, so $v_p(2^{dh} - 1) = \alpha_p + v_p(h)$, and the condition is $m \mid h$. Hence $R_1, \dots, R_m$ hit every class modulo $m$ exactly once, and the class of $r$ recurs with period $m$ in $k$. Take the first such $R_k$ above $B$. If it is among the first $m$, then $w < 2^{b+dm} t/q < t\, 2^{d(m+1)}$. Otherwise the previous one in its class is $\le B$, and $qw + 1 = 2^{dm}(q R_{k-m} + 1)$ gives $w < 2^{dm}(B + 1)$. $\square$

*Where it wins.* For $q = 5$, $m = 5^a$, Proposition A3 gives exponent $4(5^a + 1)$ and Proposition A2 gives $4 \cdot 5^a + \lceil \log_2(5^a + 1) \rceil$. A2 is better at $m = 5$ ($23$ against $24$), and A3 is better for every $a \ge 2$ ($104$ against $105$ at $m = 25$, $504$ against $507$ at $m = 125$, with the gap growing like $\log m$).

*Prime multipliers.* For prime $q = p$, $\kappa \ge 1$ requires $p$ to be Wieferich, and $\kappa \ge 2$ requires $p^3 \mid 2^{p-1} - 1$. So for every prime $q$ other than the Wieferich primes, $g_0 = 1$ and Proposition A3 applies to every power $m = q^a$.

*Where it fails.* If $p \mid \gcd(m, g_0)$, all $R_k$ lie in the single class $c_0(t) \bmod g_0$, so one odd step cannot reach every class. If $\alpha > 0$, then for large $k$ all $R_k \equiv -q^{-1} \pmod{2^\alpha}$, so the $2$-adic tail of Theorem A is genuinely needed.

---

## 5. Covering length

Theorem A depends on $m'$ through $\gamma$, for which `paper.md` uses the Chowla bound $1 + \lceil \max(0, m' - e)/\varphi(e) \rceil$. Any upper bound on $\gamma$ may be used instead:

**Lemma A4.** *If $A_k = \mathbb{Z}/m'$ then $A_{k+1} = \mathbb{Z}/m'$. So Theorem A and Proposition A2 remain valid with $\gamma$ replaced by any $\gamma' \ge \gamma$.*

*Proof.* $1 \in H$, so $A_{k+1} = A_k + q^k H \supseteq A_k + q^k = \mathbb{Z}/m'$. The construction only needs $A_{\gamma'} = \mathbb{Z}/m'$. $\square$

Two families have a far smaller $\gamma$ than the Chowla bound.

**Proposition A5 ($2$ a primitive root).** *If $m' = p^k$ with $2$ a primitive root modulo $p^k$, then $\gamma = 2$.*

*Proof.* Here $H$ is all units, so $A_1 \ne \mathbb{Z}/p^k$. Given $y$, pick $h_1 \in \{1, \dots, p-1\}$ with $q h_1 \not\equiv y \pmod p$, possible since $p - 1 \ge 2$. Then $h_1$ and $h_0 = y - q h_1$ are units, and $y = h_0 + q h_1$. $\square$

**Proposition A6 (bounded index of $q$).** *Let $\lambda_H$ be the order of $q$ in $(\mathbb{Z}/m')^\times / H$, and $s_0 = \lceil \log_2(m'+1) \rceil$. Then $\gamma \le \lambda_H s_0$.*

*Proof.* Given $x$, take $c_0 \in [1, m']$ representing $x$ and $c_r = m' \equiv 0$ for $1 \le r < \lambda_H$. Each $c_r < 2^{s_0}$ is a sum of at most $s_0$ powers of $2$. Splitting $2^j = 2^{j-1} + 2^{j-1}$, and $1 \equiv 2^e = 2^{e-1} + 2^{e-1}$, makes it a sum of exactly $s_0$ elements of $H$: $c_r \equiv \sum_{u < s_0} 2^{j_{r,u}}$. With $i = r + \lambda_H u$ and $h_i = q^{-\lambda_H u} 2^{j_{r,u}} \in H$ (since $q^{\lambda_H} \in H$),
$$\sum_{i < \lambda_H s_0} q^i h_i \equiv \sum_{r < \lambda_H} q^r c_r \equiv c_0 \equiv x \pmod{m'}. \qquad \square$$

*Where it wins.* If $q \in \langle 2 \rangle \bmod m'$, then $\gamma \le \lceil \log_2(m'+1) \rceil$. For $m' = 2^k - 1$ with $q$ a power of $2$ modulo $m'$, this gives $\gamma \le k$ where Chowla gives order $m'/k$.

---

## 6. Which bound to use

Each row is the best known bound in its regime. The exponent $\mathcal{E}$ is in $w \le (B+1)\, t\, 2^{\mathcal{E}}$.

| regime | exponent | source |
| --- | --- | --- |
| general | $E^*(a, n)$ if $t$ satisfies (H) with $a$, else $E^{**}(n)$ | Prop. A2 (with Thm. A1) |
| $m$ odd, primes of $m$ divide $q$, $\gcd(m, g_0) = 1$ | $d(m+1)$, better than A2 except for very small $m$ | Prop. A3 |
| $m' = 1$, $\kappa = 0$ | $\le d\, m^{\log_2 q} + \alpha + d$ | Prop. A2 |
| $m' = p^k$, $2$ primitive root mod $p^k$ | A2 with $\gamma = 2$ | Prop. A5 |
| $q^{\lambda_H} \in \langle 2 \rangle \bmod m'$, $\lambda_H$ small | A2 with $\gamma \le \lambda_H \lceil \log_2(m'+1) \rceil$ | Prop. A6 |

Theorem A1 helps only for composite $q$. Proposition A3 covers all powers of a non-Wieferich prime $q$.

---

## 7. Number of steps

**Proposition A7.** *The witness $w$ of Proposition A2 reaches $t$ after $T$ steps, $T_{\mathrm{odd}}$ of them odd, where:*
1. *if $t$ satisfies (H) with exponent $a$:*
$$T_{\mathrm{odd}} = n + s, \qquad T \le 2\alpha + s + \widetilde Q(n) + dq^K - 1 + (s-1)(q-1)P + B_0(a) + \bigl\lfloor (n+1)\log_2 q + \log_2(B + M + 1) \bigr\rfloor;$$
2. *otherwise, add $\kappa + 1$ odd steps and $(\kappa + 1)(dq + 1)$ steps in total, with $a = 1$.*

*If $m' > 1$, then $\alpha + s \le \log_2 m + \kappa + \gamma + 2$.*

*Proof.* Count the stages:
- the tail costs $\alpha + n$ steps, $n$ of them odd;
- the backward chain costs $s + \sum_l a_l$ steps, $s$ of them odd;
- the primer costs $\lambda_0 \le dq^K - 1$ halvings;
- in case 2, reaching $t$ from $x$ costs $\kappa + 1$ further odd steps with exponents $\le dq$.

Theorem A1 bounds $\lambda_0 + \sum_{l < s} a_l$, and the size estimate of Proposition A2 bounds $a_s$. For the last claim, minimality of $K$ gives $2^K < 3^K \le e_q \le m'$ when $K \ge 1$, so $\alpha + K \le \log_2 m$. $\square$

$T$ bounds the first time the orbit of $w$ reaches $t$; it may arrive earlier, for instance when $t$ is on a cycle.

---

## 8. How far from optimal

The remaining slack in this construction sits in four places:
- the covering length $\gamma$ (Chowla in general, §5 in special families);
- the primer, whose $K$ extra steps each pay up to $(q-1)P$;
- the tail, where uniform statements still round $n$ up to $\alpha$;
- the coarse bookkeeping in headline forms (replacing $\lceil (m'-1)/\varphi(e) \rceil$ by $m' - 1$, and similar).

Tightening any of them gives marginal gains. The construction itself is the limitation. For $5x+1$ and $t = 1$, a truncated backward search finds predecessors in every class modulo $2^\alpha$ ($\alpha \le 8$) and modulo $5^a$ ($a \le 4$) below $2^{22}$. Proposition A3 gives $2^{2504}$ for $m = 625$. (The search discards values above its cap, so what it finds are upper bounds for least witnesses, and a missed class is not evidence of absence.) Every bound here is exponential in a power of $m$; the observed least witnesses are smaller by thousands of binary digits.

---

## 9. Open questions

1. **The primer barrier.** Any shift period that preserves $y_l \bmod m'$ needs $e_q \mid P$, which by lifting the exponent forces $K$ extra steps before a shift reaches digit $0$. Can the shifts give up $\bmod m'$-invariance, taking period $\mathrm{lcm}(d, e')$ so that $K = 0$, and absorb the resulting subgroup shifts into the steering modulo $m'$? Or is there an obstruction?
2. **Per-prime delays.** For composite $q$, can the uniform $K$ and $K + \kappa$ be replaced by $K_p = \lceil v_p(e_q)/\alpha_p \rceil$ and $\max_p (K_p + \kappa_p)$ when different primes of $q$ realize $K$ and $\kappa$?
3. **Covering length.** Is $\gamma(q, m') = O(\log m')$ in general? That would replace the Chowla factor $m'/\varphi(e)$ by $\log m'$.
4. **Linear exponents.** Is there an exponent linear in $m$ for $m = 2^\alpha$, for $m = 2^\alpha m_q$, or for all $m$? In particular, for $\kappa \ge 1$ and $\gcd(m, g_0) > 1$, does a $(\kappa+1)$-step analogue of Proposition A3 exist?
5. **A $q$-adic formulation.** On $\mathbb{Z}_q$ the even branch is an isometry, the odd backward branch dilates around $(2 - q)^{-1}$, and the non-Wieferich condition is density of $\langle 2^d \rangle$ in $1 + q\mathbb{Z}_q$. Proving Theorem A directly in this setting might give the different strategy that §8 calls for.
