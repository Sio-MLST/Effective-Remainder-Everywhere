# Supplements B: how deep a trap can be

Theorem B of `paper.md` says that a target $t$ outside the dense regime is a *trap*: every backward chain of odd steps into $t$ has length at most $\kappa$, and $R_q(t)$ meets at most $(n+1)^{\kappa+1}$ classes modulo $2^n$. This supplement asks how much of that bound is actually used. The answer has three parts.

1. **Depth is exact per target.** Each trapped $t$ has a depth $m(t)$, the exact length of its longest backward chain of odd steps, and the growth of $R_q(t)$ is exactly $(\log X)^{m(t)+1}$ (§2).
2. **Shallow is the rule for simple multipliers.** If only one prime, and a non-Wieferich one, carries the excess of $u_q$ over $\gcd(q,u)$, no trap is deeper than $2$, however large $\kappa$ is (§3–4).
3. **Deep traps exist and are typical.** For every $L$ there is a multiplier with a trap of depth exactly $L$, built from a chain of primes each of which locks the previous one; and for almost all odd $q$ the maximal trap depth exceeds any fixed bound (§5–6).

The smallest multipliers with depth $1$ and $2$ are $21$ and $7959$; nothing explicit is known at depth $3$ (§7). Open questions are in §8.

Notation is that of `paper.md`, §1: $d = \mathrm{ord}_q(2)$, $2^d = 1 + qu$, $\alpha_p = v_p(q)$, $\nu_p = v_p(u)$, $u_q = \prod_{p \mid q} p^{\nu_p}$, $N_q = q u_q$, $H_q = \langle 2 \rangle \subseteq (\mathbb{Z}/q)^\times$, the graph $\mathcal{G}_q$ on $V_q$, the residues $a_0(z)$, $c_0(z)$, and $R_{\mathrm{core}}$. Lemma 1 (lifting the exponent), Lemma 2 (the odd predecessors $c_j$) and Proposition 1 (dense iff a path of length $\kappa$, iff a path to $R_{\mathrm{core}}$) are used throughout. We also write
$$g_0 = \gcd(q, u) = \prod_{p \mid q} p^{\min(\alpha_p, \nu_p)}, \qquad u_q^* = u_q / g_0 = \prod_{p \mid q} p^{\max(0,\, \nu_p - \alpha_p)}.$$
So $g_0$ is the part of $u_q$ that one step of the graph can absorb, and $u_q^*$ is the excess.

---

## 1. Depth

For a trapped target $t$ (one not in the dense regime), put $m(t) = 0$ if $t \bmod N_q \notin V_q$, and otherwise $m(t) = L(t) + 1$, where $L(t)$ is the length of the longest directed path from $t \bmod N_q$ in $\mathcal{G}_q$. Since $t$ is trapped, $L(t) < \kappa$ by Proposition 1, so $m(t) \le \kappa$. The *trap depth* of $q$ is
$$\kappa_{\mathrm{trap}}(q) = \max\{\, m(t) : t \ge 1 \text{ trapped} \,\} \le \kappa.$$
If $\kappa \ge 1$ then $\kappa_{\mathrm{trap}}(q) \ge 1$: the target $t = 1$ has $c_0(1) \equiv u \equiv 0 \pmod{g_0}$, so (Lemma B3 below) its vertex has no successor, and $1$ is trapped with $m(1) = 1$.

---

## 2. Depth is exact

**Proposition B1.** *Let $t$ be trapped and $m = m(t)$.*
1. *The longest backward chain of odd steps in $R_q(t)$ has length exactly $m$.*
2. *There are constants $c_1, c_2, C_1, C_2 > 0$ depending on $q$ and $t$ such that, for large $X$ and $n$,*
$$c_1 (\log X)^{m+1} \le |R_q(t) \cap [1, X]| \le C_1 (\log X)^{m+1}, \qquad c_2\, n^{m+1} \le |R_q(t) \bmod 2^n| \le C_2\, n^{m+1}.$$

So Theorem B's exponent $\kappa + 1$ is attained exactly when $m(t) = \kappa$, and otherwise is replaced by the target's own depth.

*Proof.* (1) The proof of Proposition 1, $(1) \Rightarrow (2)$, in `paper.md` turns a backward chain $w_1, \dots, w_r$ into a path $t \to w_1 \to \dots \to w_{r-1}$ of length $r - 1$ in $\mathcal{G}_q$ (reducing modulo $N_q$), so $r \le L(t) + 1 = m$. Conversely, given a path $z_0 = t \to z_1 \to \dots \to z_L$, Lemma 2(2) lets us choose $w_l = c_{j_l}(w_{l-1}) \equiv z_l \pmod{N_q}$ with $j_l < q$, starting from $w_0 = t$; then $w_{L+1} = c_0(w_L)$ adds one more odd step, giving a chain of length $L + 1 = m$.

(2) The upper bounds are the proof of Theorem B with $\kappa$ replaced by $m$. For the lower bounds, take $m \ge 1$ (for $m = 0$ the elements $2^k t$ suffice), fix the $j_l$ from (1), and set $j_m = 0$. For $(s_1, \dots, s_m, k) \in \mathbb{N}^{m+1}$ let $w_l = c_{j_l + q s_l}(w_{l-1})$ and $y = 2^k w_m$. Replacing $j$ by $j + qs$ changes $c_j$ by a multiple of $u S_{qs}$, and $v_p(u S_{qs}) \ge \nu_p + \alpha_p$, so the residues modulo $N_q$, and hence the whole construction, are unaffected. Distinct tuples give distinct $y$: $k = v_2(y)$, and since a trapped $t$ is not periodic, $t$ occurs once on the forward orbit of $w_m$, whose odd iterates before $t$ recover $w_m, \dots, w_1$ and hence the $s_l$. Writing $E_l$ for the exponent of the $l$-th step,
$$q^m y = 2^{S_0} t - \sum_{l=1}^{m} q^{l-1} 2^{S_l}, \qquad S_l = k + E_{l+1} + \dots + E_m,$$
with $S_0 > S_1 > \dots > S_m = k$. The $E_l$ grow linearly in $s_l$, so the tuples with $k + \sum s_l \ll \log X$ give $\gg (\log X)^{m+1}$ elements below $X$; and when $S_0 + v_2(t) < n$, the residue $y \bmod 2^n$ determines $S_m, S_{m-1}, \dots, S_0$ one at a time by $2$-adic valuations, which gives $\gg n^{m+1}$ classes modulo $2^n$. $\square$

*Example.* For $q = 21$ ($\kappa = 1$), $R_{21}(1) = \{2^k\} \cup \{2^k (2^{6j} - 1)/21 : j \ge 1\}$, since each $(2^{6j}-1)/21$ is divisible by $3$ and has no odd predecessor. Hence $|R_{21}(1) \cap [1, X]| = \tfrac{1}{12} (\log_2 X)^2 + O(\log X)$.

---

## 3. Successors depend only on $c_0$

**Lemma B2.** *Let $z \in V_q$ and $r = c_0(z) \in \mathbb{Z}/u_q$. The successors of $z$ in $\mathcal{G}_q$ are the $z' \in V_q$ with*
$$z' \equiv 2^{-a} \pmod q, \qquad z' \equiv r \pmod{u_q}, \qquad \text{for some } a \in \{1, \dots, d\} \text{ with } 2^{-a} \equiv r \pmod{g_0}.$$
*For each such $a$, the solutions form $g_0$ classes $z' + k N_q / g_0$ ($0 \le k < g_0$), and*
1. *their values $c_0 \bmod u_q$ are exactly the $g_0$ lifts of one class modulo $u_q^*$;*
2. *at each prime $p \mid u_q^*$, writing $q = p^{\alpha_p} q'_p$, that class is*
$$c_0(z') \equiv (q'_p)^{-1}\, \frac{2^a r - 1}{p^{\alpha_p}} \pmod{p^{\nu_p - \alpha_p}}.$$

In particular, whether $z$ has a path of length $\ell$ depends only on $c_0(z)$.

*Proof.* The two congruences are compatible exactly when they agree modulo $\gcd(q, u_q) = g_0$, and then determine $z'$ modulo $\mathrm{lcm}(q, u_q) = N_q / g_0$. Shifting $z'$ by $k N_q / g_0 = k q u_q^*$ shifts $c_0(z') = (2^a z' - 1)/q$ by $2^a k u_q^*$, which runs over all multiples of $u_q^*$ modulo $u_q$. Part 2 is $c_0(z') = (2^a z' - 1)/q$ read modulo $p^{\nu_p - \alpha_p}$, using $z' \equiv r \pmod{p^{\nu_p}}$. $\square$

**Lemma B3.** *$z \in V_q$ has a successor iff $c_0(z) \bmod g_0 \in H_q \bmod g_0$.* This is the compatibility condition of Lemma B2.

**Lemma B4 (sweeping).** *Suppose that from some vertex the vertices reachable in $\ell$ steps realize every value of $c_0$ modulo $u_q$. Then that vertex is dense.*

*Proof.* Some vertex reached in $\ell$ steps has $c_0 \equiv c_1 \pmod{u_q}$, where $c_1 \in R_{\mathrm{core}}$ is as in `paper.md`; it therefore has the edge to $c_1$, and Proposition 1 applies. $\square$

Every upper bound on depth below is proved the same way: one shows that, after a fixed number of steps, varying the exponent $a$ along the path makes $c_0$ sweep all of $\mathbb{Z}/u_q$. By Lemma B2(1) only the class modulo $u_q^*$ needs to be swept; $g_0$ is absorbed for free.

The sweep is driven by $o = \mathrm{ord}_{g_0}(2)$: replacing $a$ by $a + so$ keeps the compatibility condition of Lemma B2 intact. For $p \mid u_q^*$ put
$$\delta_p = v_p(2^o - 1) - \alpha_p \ge 0.$$

**Proposition B5 (no excess, or no resistance, means depth $\le 1$).** *If $\delta_p = 0$ for every $p \mid u_q^*$ (in particular if $u_q^* = 1$), every trapped vertex has no successor, so $\kappa_{\mathrm{trap}}(q) \le 1$.*

*Proof.* Let $z$ have a successor via the exponent $a_0$, and consider the exponents $a(s) = a_0 + so$. At $p \mid u_q^*$ we have $p \mid g_0$, so $p \nmid r$, and Lemma B2(2) gives
$$c_0(z'(s_1)) - c_0(z'(s_2)) \equiv (q'_p)^{-1} r\, 2^{a(s_2)}\, \frac{2^{o(s_1 - s_2)} - 1}{p^{\alpha_p}} \pmod{p^{\nu_p - \alpha_p}}.$$
Since $v_p(2^o - 1) = \alpha_p$, Lemma 1(2) gives valuation exactly $v_p(s_1 - s_2)$. So $s \bmod u_q^*$ maps injectively, hence bijectively, onto $\mathbb{Z}/u_q^*$. (The exponents $a(s)$ are distinct modulo $d$ for $s < u_q^*$: comparing $v_p(2^d - 1) = \alpha_p + \nu_p$ with $v_p(2^o-1) = \alpha_p$ gives $v_p(d/o) = \nu_p$, so $u_q^* \mid d/o$.) With Lemma B2(1), the successors of $z$ sweep $\mathbb{Z}/u_q$, and $z$ is dense by Lemma B4. $\square$

For a non-Wieferich $p$ dividing $g_0$ only through itself, $\delta_p = 0$ automatically. So depth $\ge 2$ needs *resistance*: some prime of the excess whose order is inflated by another prime of $g_0$, or a Wieferich prime.

---

## 4. The single-prime barrier

**Theorem B6.** *Suppose $u_q^* = p^{\nu - \alpha}$ is a power of one prime $p$ ($\alpha = \alpha_p$, $\nu = \nu_p > \alpha$), and $p$ is not a Wieferich prime. Then $\kappa_{\mathrm{trap}}(q) \le 2$, regardless of $\kappa$ and of how many primes divide $g_0$.*

The point is that resistance can come from other primes of $g_0$ (through $o$), but those primes are themselves absorbed after one step, after which only the $p$-adic order $o_0 = \mathrm{ord}_{p^\alpha}(2)$ constrains the exponent, and for non-Wieferich $p$ that constraint has no resistance.

*Proof.* Write $u_q = p^{\nu} u'$. Every other prime of $u_q$ has $\nu_{p'} \le \alpha_{p'}$, so $g_0 = p^\alpha u'$. Since $p$ is non-Wieferich, $v_p(2^{o_0} - 1) = \alpha$.

Let $z_0 \to z_1 \to z_2$ be a path, with $a_2 = a_0(z_2)$. We vary $a_2(s) = a_2 + s o_0$ for $0 \le s < p^{\nu - \alpha}$. Modulo $p^\alpha$ these exponents stay compatible with $c_0(z_1)$; modulo $u'$ they need not. Fix that by moving $z_1$: the lifts $z_1 + k N_q/g_0$ with $p^\alpha \mid k$ are still successors of $z_0$, leave $c_0(z_1) \bmod p^\nu$ unchanged, and by Lemma B2(1) move $c_0(z_1) \bmod u'$ freely, since $u_q^*$ is prime to $u'$. Choose $k = k_s$ so that $c_0 \equiv 2^{-a_2(s)} \pmod{u'}$. Then $a_2(s)$ is compatible, giving successors $z_2^{(s)}$.

At $p$, Lemma B2(2) with the common value $r = c_0(z_1) \bmod p^\nu$ gives differences
$$c_0(z_2^{(s_1)}) - c_0(z_2^{(s_2)}) \equiv (q'_p)^{-1} r\, 2^{a_2(s_2)}\, \frac{2^{o_0(s_1 - s_2)} - 1}{p^\alpha} \pmod{p^{\nu - \alpha}},$$
of valuation exactly $v_p(s_1 - s_2)$. So the $z_2^{(s)}$ sweep $\mathbb{Z}/u_q^*$, their lifts sweep $\mathbb{Z}/u_q$, and $z_0$ is dense by Lemma B4. Hence a trapped vertex has no path of length $2$: $L(t) \le 1$ and $m(t) \le 2$. $\square$

*Remark.* For a Wieferich $p$ with $\alpha = 1$, $v_p(2^{o_0} - 1) = 2$, and the sweep in the proof covers only a coset modulo $p$; one more step, using the freedom modulo $p$ that this coset leaves, completes it. This gives $\kappa_{\mathrm{trap}}(q) \le 3$ for $q$ built on the known Wieferich primes $1093$ and $3511$.

*Prime multipliers.* For $q = p$ prime, $p \nmid (p-1)/d$, so $\nu_p = v_p(2^{p-1} - 1) - 1$, and $\kappa \ge 2$ iff $p^3 \mid 2^{p-1} - 1$. No such prime is known. So all interesting depth comes from composite multipliers.

---

## 5. Every depth occurs

Theorem B6 says depth $\ge 3$ needs at least two primes in the excess $u_q^*$. The construction below uses exactly that: a chain of primes $p_0 = 3, p_1, \dots, p_{L-1}$ in which each $p_i$ has a multiplicative order of $2$ divisible by high powers of all earlier ones. A target is chosen so that each step of a backward chain is forced through the next prime down the chain, losing one level of $p$-adic precision each time, until at the bottom $c_0 \equiv 0 \pmod 3$ and the chain dies.

**Theorem B7.** *For every $L \ge 1$ there is a squarefree odd $q$ and a trapped $t$ with $m(t) = L$. In particular $\kappa_{\mathrm{trap}}(q) \ge L$.*

*Construction.* For $L = 1$ take $q = 21$, $t = 1$. Let $L \ge 2$ and $p_0 = 3$. For $i = 1, \dots, L-1$ put
$$E_i = \mathrm{lcm}_{0 \le j < i}\ \mathrm{ord}_{p_j^{\,i+2-j}}(2),$$
and let $p_i$ be a primitive prime divisor of $2^{E_i} - 1$ (Zsigmondy; $E_i \ge 18$), so $\mathrm{ord}_{p_i}(2) = E_i$. Inductively $v_3(E_i) = i + 1$: the term $\mathrm{ord}_{3^{i+2}}(2) = 2 \cdot 3^{i+1}$ dominates, the others having $v_3 = v_3(E_j) = j+1$. So the $E_i$, and hence the $p_i$, are distinct. Finally let $r^*$ be any prime factor of $2^{p_{L-1}} - 1$. Its only role is to make $p_{L-1}$ divide $d$: $\mathrm{ord}_{r^*}(2) = p_{L-1}$, so
$$q = p_0 p_1 \cdots p_{L-1}\, r^*, \qquad d = E_{L-1}\, p_{L-1}.$$
Since $E_{L-1} \mid d$, $2^d \equiv 1 \pmod{p_j^{L+1-j}}$, so $\nu_{p_j} \ge L - j$ for $j \le L - 2$; and $p_{L-1} \mid d$ gives $\nu_{p_{L-1}} \ge 1$. Thus
$$p_j^{L-j} \mid u_q \ (0 \le j \le L-1), \qquad p_0 p_1 \cdots p_{L-1} \mid g_0, \qquad \kappa \ge \nu_3 \ge L.$$

*The target.* Let $\sigma_k = 1 + q + \dots + q^{k-1}$, so $\sigma_0 = 0$, $\sigma_k \equiv 1 \pmod q$ for $k \ge 1$, and
$$\sigma_k - 1 = q\, \sigma_{k-1}.$$
Choose $t = 1 + qj$ with $c_0(t) = u + 2^d j \equiv \sigma_{L-1} \pmod{u_q}$; possible since $2^d \equiv 1 \pmod{u_q}$.

*Every path dies by step $L - 1$.* Let $t = z_0 \to z_1 \to \dots$ be any path, with exponents $a_r = a_0(z_r)$. We claim
$$c_0(z_r) \equiv \sigma_{L-1-r} \pmod{p_j^{\,L-r-j}} \qquad (0 \le j \le L-1-r).$$
For $r = 0$ this is the choice of $t$. Given it for $r - 1$, put $i = L - r \ge 1$. Then $c_0(z_{r-1}) \equiv \sigma_i \equiv 1 \pmod{p_i}$, and $p_i \mid g_0$, so the edge to $z_r$ forces $2^{a_r} \equiv 1 \pmod{p_i}$, that is $E_i \mid a_r$, hence $2^{a_r} \equiv 1 \pmod{p_j^{\,i+2-j}}$ for all $j < i$. Using $z_r \equiv c_0(z_{r-1}) \pmod{u_q}$,
$$q\, c_0(z_r) = 2^{a_r} z_r - 1 \equiv \sigma_i - 1 = q\, \sigma_{i-1} \pmod{p_j^{\,i+1-j}},$$
and dividing by $q$ ($p_j \parallel q$) gives the claim for $r$. At $r = L-1$ the claim reads $c_0(z_{L-1}) \equiv \sigma_0 = 0 \pmod 3$, and since $0 \notin H_q \bmod 3$, $z_{L-1}$ has no successor (Lemma B3). So every path has length at most $L - 1 < \kappa$, and $t$ is trapped.

*Some path reaches step $L - 1$.* Use the exponent $a = d$ at each step; it is compatible because $c_0 \equiv \sigma_k \equiv 1 \pmod{g_0}$ along the way. With $a = d$ and $2^d \equiv 1 \pmod{p^{\nu_p + 1}}$, the same identity $q\,c_0(z_r) \equiv \sigma_{L-r} - 1 = q\,\sigma_{L-1-r}$ holds modulo $p^{\nu_p}$ at every $p \mid g_0$, which fixes $c_0(z_r) \equiv \sigma_{L-1-r}$ modulo $u_q^*$; a lift from Lemma B2(1) fixes it modulo $u_q$. Repeating for $r = 1, \dots, L-1$ gives a path of length $L - 1$.

Hence $L(t) = L - 1$ and $m(t) = L$. $\square$

Nothing in the argument uses that $q$ has no other prime factors. All it needs is: $p_j \parallel q$, $p_j^{L-j} \mid u_q$, $p_0 \cdots p_{L-1} \mid g_0$, and $E_i \mid \mathrm{ord}_{p_i}(2)$. That is what makes the next result possible.

---

## 6. Deep traps are typical

**Theorem B8.** *For every $L$, the odd $q$ with $\kappa_{\mathrm{trap}}(q) \ge L$ have relative density $1$ among odd integers. The same holds for $\kappa(q) \ge L$.*

*Proof.* **Primes with a prescribed divisor in their order.** For every $E \ge 1$, the primes $r$ with $E \mid \mathrm{ord}_r(2)$ have positive Dirichlet density. Indeed, take $r \equiv 1$ modulo a suitable $N$ (with $8 \mid N$ and $\ell^{v_\ell(E)} \mid N$, and $2^{v_2(E)+1} \mid N$) such that $2$ is not an $\ell$-th power modulo $r$ for each odd $\ell \mid E$, and not a fourth power if $E$ is even. The Kummer extensions $\mathbb{Q}(\zeta_N, 2^{1/\ell})$ and $\mathbb{Q}(\zeta_N, 2^{1/4})$ are linearly disjoint over $\mathbb{Q}(\zeta_N)$, so Chebotarev gives these primes positive density; and for each of them $E \mid \mathrm{ord}_r(2)$.

**Sieve.** For a set of primes $\mathcal{P}$ of positive density, almost all integers have a prime factor in $\mathcal{P}$, and indeed a prime factor in $\mathcal{P} \cap (M, M']$ dividing them exactly once, for suitable $M'$ given $M$, outside a proportion as small as we like.

**$\kappa \ge L$.** Given $\varepsilon$, almost every odd $q$ has some prime $p \parallel q$ below a fixed bound $M(\varepsilon)$, outside proportion $\varepsilon$; and almost every $q$ has, for each such $p$, a prime factor $r$ with $p^L \mid \mathrm{ord}_r(2)$. Then $p^L \mid d$, so $\nu_p \ge L$ and $\kappa \ge L$.

**$\kappa_{\mathrm{trap}} \ge L$.** Apply the same reasoning to the hypotheses of Theorem B7. Choose cutoffs $M_0 < M_1 < \dots < M_{L-1}$ so that outside proportion $\varepsilon$, $q$ has primes $p_0 \in (2, M_0]$, $p_1 \in (M_0, M_1]$, ..., each dividing $q$ exactly once, with $E(p_0, \dots, p_{i-1}) \mid \mathrm{ord}_{p_i}(2)$, where $E$ is the exponent of §5 for that chain; this is possible because at each stage there are only finitely many earlier chains, each giving a positive-density set of admissible $p_i$. Then almost every such $q$ also has a prime factor $r^*$ with $p_{L-1} \mid \mathrm{ord}_{r^*}(2)$. Such $q$ satisfy every hypothesis the proof of Theorem B7 uses, and $\varepsilon$ was arbitrary. $\square$

The proportions involved decay like a small negative power of $\log X$, so the density-$1$ behaviour sets in only at enormous sizes. This is consistent with §7: in the range anyone can search, depth $\ge 2$ is rare.

---

## 7. Small multipliers

**Depth 1.** $\kappa_{\mathrm{trap}}(q) \ge 1$ iff $\kappa \ge 1$ iff $g_0 > 1$. These $q$ begin $21, 39, 55, 57, 105, \dots$; the first is $21$.

**Depth 2.** The first multiplier with $\kappa_{\mathrm{trap}} \ge 2$ is $7959 = 3 \cdot 7 \cdot 379$.

Why $7959$ has depth $2$: $\mathrm{ord}_{379}(2) = 378$, so $d = 378$, $g_0 = 21$, $u_q = 189 = 3^3 \cdot 7$, $\kappa = 3$. Take $t$ with $c_0(t) \equiv 1 \pmod{189}$. A successor $z_1$ needs $2^{-a} \equiv 1 \pmod{21}$, so $6 \mid a$ and $2^a \equiv 1 \pmod 9$; with $z_1 \equiv 1 \pmod 9$ this gives $9 \mid 2^a z_1 - 1$, so $c_0(z_1) \equiv 0 \pmod 3$ and $z_1$ has no successor. Successors exist ($a = 6$ is allowed), so $m(t) = 2 < \kappa$.

Why nothing smaller works: by Proposition B5 some $p \mid u_q^*$ must have $\delta_p \ge 1$. For non-Wieferich $p$ that requires another prime $p_1 \mid g_0$ with $p^{\alpha_p} \mid \mathrm{ord}_{p_1}(2)$, together with $p^{2\alpha_p} \mid d$. A Wieferich $p$ (at least $1093$) needs $p \mid d$, hence another prime factor $\equiv 1 \pmod{2p}$, which already puts $q$ far above $7959$. The smallest configuration of the first kind is $p = 3$, $p_1 = 7$, with $9 \cdot 7 \mid d$ supplied by $379$; every other configuration exceeds $7959$. The next two multipliers of depth $2$ are $10887 = 3 \cdot 19 \cdot 191$ and $11571 = 3 \cdot 7 \cdot 19 \cdot 29$.

**Depth 3.** Theorem B7 shows depth-$3$ multipliers exist, but its multiplier $3 \cdot 19 \cdot p_2 \cdot r^*$ involves a primitive prime divisor $p_2$ of $2^{19494} - 1$ and a prime factor of $2^{p_2} - 1$, and is neither explicit nor plausibly the smallest. The construction is also wasteful: the depth-$3$ argument only needs $2^a \equiv 1 \pmod{p_2}$ to force $2^a \equiv 1 \pmod{3^3 \cdot 19^2}$, that is $342 \mid \mathrm{ord}_{p_2}(2)$, with $27 \cdot 361 \mid d$ supplied by any primes. No explicit depth-$3$ multiplier is known.

---

## 8. Open questions

1. **Does every depth occur exactly, and can depth jump?** Theorems B7 and B8 give $\kappa_{\mathrm{trap}}(q) \ge L$, not $= L$. Let $b(n)$ be the least $q$ with $\kappa_{\mathrm{trap}}(q) \ge n$. Then $b$ is nondecreasing, $b(1) = 21$, $b(2) = 7959$, and $b(3)$ is unknown. The least $q$ with depth *exactly* $n$ equals $b(n)$ unless the first multiplier to reach depth $n$ overshoots it. Whether that ever happens is the real content of the "monotonicity" question. It cannot happen at $n = 2$, since $7959$ has depth exactly $2$.

2. **Excess at several primes.** Theorem B6 covers $u_q^*$ a single prime power. When several primes divide $u_q^*$, is depth governed by the chain structure of Theorem B7, that is by the directed graph on the primes of $g_0$ with $p \to p'$ when $p'^{\alpha_{p'}} \mid \mathrm{ord}_p(2)$, together with the local data $(\alpha_p, \nu_p, \delta_p)$? A formula of this kind would contain Proposition B5, Theorem B6 and Theorem B7 as special cases.

3. **Typical size.** Theorem B8 says $\kappa_{\mathrm{trap}}(q) \to \infty$ on a set of density $1$ but gives no rate. What is the normal order of $\kappa(q)$ and of $\kappa_{\mathrm{trap}}(q)$, and is the gap between them typically bounded?

4. **Smallest examples.** Find $b(3)$. By Theorem B6 the excess $u_q^*$ must involve at least two primes, or a Wieferich prime.
