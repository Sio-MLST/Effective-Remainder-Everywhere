# Backward orbits of $qx+1$ maps: a 0–1 law for their profinite closure

**Abstract.** For every odd $q>1$ and every target $t\ge 1$, the backward orbit $R_q(t)$ of the map $\mathrm{Col}_q$ ($x\mapsto x/2$ for even $x$, $x\mapsto qx+1$ for odd $x$) is either dense in the profinite integers $\widehat{\mathbb{Z}}$ or a Haar-null set, and no other case occurs. The target may lie anywhere, on a cycle or off it, and nothing is assumed about its forward orbit. Which case holds is decided by a directed path of length $\kappa$ in a finite graph on the residues modulo $N_q$, where $\kappa$ and $N_q$ are computed from the order of $2$ modulo $q$. In the dense case every residue class modulo every $m$ contains a predecessor of $t$, with an explicit bound on its size (Theorem A). In the null case every chain of odd steps has length at most $\kappa$, and $R_q(t)$ meets at most $(n+1)^{\kappa+1}$ classes modulo $2^n$ (Theorem B). The proofs are constructive: the witnesses in Theorem A are built by explicit finite procedures, and the dichotomy is decided by a finite computation. This can be read off the proofs themselves; as a machine check, the integer and finite-modulus statements are also formalized in Lean 4.35 core without Mathlib. The Haar-measure conclusions follow from them in a few lines and are not formalized. The results concern backward orbits only: they say nothing about forward orbits or the Collatz conjecture.

**Verification boundary.** All integer and finite-modulus statements (Proposition 1, Theorems A and B with every explicit bound) are formalized in Lean 4.35 core, with no Mathlib, as `general_prop1`, `general_theorem_A`, and `general_theorem_B` (folder `QX+1/`). The proofs use no `sorry`, and in Lean 4.35 `#print axioms` reports only `[propext, Quot.sound]`. The profinite ring $\widehat{\mathbb{Z}}$ and its Haar measure $\mu$ are not in Lean 4.35, because Lean 4.35 core has no measure theory. The measure statements follow in a few lines from the formalized ones; this derivation is §6, and it is the only part of the paper not machine-checked.

---

### 1. Definitions, Structural Parameters, and the Residue Graph $\mathcal{G}_q$

Let $\mathbb{N} = \{0, 1, 2, \dots\}$. For an odd integer $q > 1$ (so $q \ge 3$), define $\mathrm{Col}_q : \mathbb{N} \to \mathbb{N}$ by
$$\mathrm{Col}_q(x) = \begin{cases} x/2 & \text{if } x \text{ is even},\\ qx + 1 & \text{if } x \text{ is odd}. \end{cases}$$
Write $x \to y$ if $\mathrm{Col}_q^k(x) = y$ for some $k \ge 0$ (where $\mathrm{Col}_q^0 = \mathrm{id}$); the relation $\to$ is reflexive and transitive. For $t \in \mathbb{N}$, define the backward orbit
$$R_q(t) = \{x \in \mathbb{N} : x \to t\}.$$
For $t \ge 1$ and $m \ge 1$, a *backward chain of $m$ odd steps* in $R_q(t)$ is a sequence of odd integers $w_1, \dots, w_m \ge 1$ such that $qw_1 + 1 = 2^{k_1} t$ for some $k_1 \ge 0$ and $qw_{l+1} + 1 = 2^{k_{l+1}} w_l$ for some $k_{l+1} \ge 1$ ($1 \le l < m$). Then $\mathrm{Col}_q^{1 + k_1}(w_1) = t$ and $\mathrm{Col}_q^{1 + k_{l+1}}(w_{l+1}) = w_l$ for $1 \le l < m$, so $w_m \to \dots \to w_1 \to t$ and $w_1, \dots, w_m \in R_q(t)$. Let $\widehat{\mathbb{Z}} = \varprojlim_{n \ge 1} \mathbb{Z}/n\mathbb{Z}$ denote the compact topological ring of profinite integers equipped with its normalized Haar probability measure $\mu$, and write $\overline{X}$ for the closure in $\widehat{\mathbb{Z}}$ of the diagonal image of $X \subseteq \mathbb{N}$.

Since $q \ge 3$ is odd, $\gcd(2, q) = 1$ and $2 \not\equiv 1 \pmod q$, so $d = \mathrm{ord}_q(2) \ge 2$ exists and $u = (2^d - 1)/q \in \mathbb{Z}_{\ge 1}$ satisfies $2^d = 1 + qu$. Put $g_0 = \gcd(q, u)$. For each prime $p \mid q$, let $v_p$ denote the $p$-adic valuation and set $\alpha_p = v_p(q) \ge 1$ and $\nu_p = v_p(u) \ge 0$. Define
$$u_q = \prod_{p \mid q} p^{\nu_p}, \qquad N_q = q u_q = \prod_{p \mid q} p^{\alpha_p + \nu_p}, \qquad \kappa = \max_{p \mid q} \left\lceil \frac{\nu_p}{\alpha_p} \right\rceil \ge 0.$$
Equivalently, $\kappa$ is the least $k \ge 0$ with $u_q \mid q^k$, since $p^{\nu_p} \mid p^{k\alpha_p}$ iff $k \ge \lceil \nu_p/\alpha_p \rceil$. (Lean 4.35 uses this form; `nu_le_kappa` and `kappa_le_of_nu_le` prove the equivalence.) Then $g_0 = 1$ if and only if $\nu_p = 0$ for all $p \mid q$, which holds if and only if $u_q = 1$, and if and only if $\kappa = 0$. Since $q \mid N_q$ and $N_q \mid qu = 2^d - 1$, we have $\mathrm{ord}_{N_q}(2) = d$.

Let $H_q = \langle 2 \rangle \subseteq (\mathbb{Z}/q\mathbb{Z})^\times$. For each $a \in \{1, \dots, d\}$, $\gcd(2^a - q, q) = \gcd(2^a, q) = 1$, so $2^a - q$ is invertible modulo every integer whose prime factors all divide $q$; let $c_a \in (\mathbb{Z}/N_q\mathbb{Z})^\times$ denote the inverse of $2^a - q$ modulo $N_q$.

**Hypothesis (H).** An integer $x \in \mathbb{N}$ satisfies *(H)* if there exist $a \in \{1, \dots, d\}$ and $i_0 \in \{0, \dots, d - 1\}$ such that
$$2^{i_0} x (2^a - q) \equiv 1 \pmod{N_q},$$
equivalently $x \bmod N_q \in c_a \langle 2 \rangle \subseteq (\mathbb{Z}/N_q\mathbb{Z})^\times$.

Define
$$V_q = \{z \in (\mathbb{Z}/N_q\mathbb{Z})^\times : z \bmod q \in H_q\},$$
$$R_{\mathrm{core}} = \{z \in (\mathbb{Z}/N_q\mathbb{Z})^\times : \exists a \in \{1, \dots, d\},\, i_0 \in \{0, \dots, d - 1\},\, 2^{i_0} z(2^a - q) \equiv 1 \pmod{N_q}\}.$$
Reducing $2^{i_0} z(2^a - q) \equiv 1 \pmod{N_q}$ modulo $q$ yields $2^{i_0 + a} z \equiv 1 \pmod q$, so $z \bmod q \in H_q$ and $R_{\mathrm{core}} \subseteq V_q$. For each $z \in V_q$, since $z \bmod q \in H_q$ and $\mathrm{ord}_q(2) = d$, there is a unique $a_0(z) \in \{1, \dots, d\}$ with $2^{a_0(z)} z \equiv 1 \pmod q$. Choosing any integer representative $\tilde{z} \in \mathbb{Z}$ of $z$, the integer $(2^{a_0(z)} \tilde{z} - 1)/q$ is well-defined modulo $u_q$ because shifting $\tilde{z}$ by $k N_q = k q u_q$ shifts this quotient by $2^{a_0(z)} k u_q$; write $c_0(z) \in \mathbb{Z}/u_q\mathbb{Z}$ for this residue class. When $y \in \mathbb{N}$ satisfies $y \bmod N_q \in V_q$, we have $y \ge 1$ (as $0 \bmod N_q \notin (\mathbb{Z}/N_q\mathbb{Z})^\times$), and we write $a_0(y) := a_0(y \bmod N_q)$ and $c_0(y) := (2^{a_0(y)} y - 1)/q \in \mathbb{Z}_{\ge 1}$, whose residue modulo $u_q$ is $c_0(y \bmod N_q)$. Define the directed graph $\mathcal{G}_q$ on vertex set $V_q$ by
$$z \to z' \iff z' \equiv c_0(z) \pmod{u_q}.$$

---

### 2. Preliminary Arithmetic Lemmas and the Exact Partition Criterion

**Lemma 1 (Binomial and $2$-adic lifting).** *Let $p$ be a prime dividing $q$.*
1. *For every integer $\lambda \ge 1$, integer $g \equiv 1 \pmod{p^\lambda}$, and integer $\beta \ge 0$,*
   $$g^\beta - 1 \equiv \beta(g - 1) \pmod{p^{2\lambda}}.$$
2. *For every integer $h \in \mathbb{Z}$ with $v_p(h - 1) = \lambda \ge 1$ and every integer $N \ge 1$,*
   $$v_p(h^N - 1) = \lambda + v_p(N).$$
   *In particular, $v_p(2^{dN} - 1) = \alpha_p + \nu_p + v_p(N)$ for all $N \ge 1$.*

*Proof.* (1) Write $g = 1 + p^\lambda z$ with $z \in \mathbb{Z}$. By the binomial theorem, $g^\beta - 1 = \sum_{k=1}^\beta \binom{\beta}{k} p^{k\lambda} z^k$ (the sum being $0$ if $\beta = 0$). Every term with $k \ge 2$ has $k\lambda \ge 2\lambda$, yielding $g^\beta - 1 \equiv \beta(g - 1) \pmod{p^{2\lambda}}$.

(2) Write $h = 1 + p^\lambda z$ with $p \nmid z$. Then
$$h^p - 1 = p(h - 1) + \binom{p}{2} p^{2\lambda} z^2 + \sum_{k=3}^p \binom{p}{k} p^{k\lambda} z^k.$$
Since $p$ is odd, $p \mid \binom{p}{2}$, so the $k = 2$ term has $p$-adic valuation at least $2\lambda + 1 \ge \lambda + 2$; for $3 \le k \le p$, $k\lambda \ge 3\lambda \ge \lambda + 2$. Because $v_p(p(h - 1)) = \lambda + 1$, we obtain $v_p(h^p - 1) = \lambda + 1$. By induction on $\eta \ge 0$, $v_p(h^{p^\eta} - 1) = \lambda + \eta$. Writing $N = p^\eta b$ with $\eta = v_p(N) \ge 0$ and $p \nmid b$, part (1) gives $(h^{p^\eta})^b - 1 \equiv b(h^{p^\eta} - 1) \pmod{p^{2(\lambda + \eta)}}$. Since $v_p\bigl(b(h^{p^\eta} - 1)\bigr) = \lambda + \eta < 2(\lambda + \eta)$, it follows that $v_p(h^N - 1) = \lambda + v_p(N)$. Applying this to $h = 2^d = 1 + qu$, which satisfies $v_p(2^d - 1) = \alpha_p + \nu_p \ge 1$, yields $v_p(2^{dN} - 1) = \alpha_p + \nu_p + v_p(N)$. $\blacksquare$

**Lemma 2 (Odd backward steps).** *Let $y \in \mathbb{N}$ satisfy $y \bmod N_q \in V_q$, and let $a_0 = a_0(y)$. Then:*
1. *The odd integers $w \ge 1$ such that $qw + 1 = 2^\ell y$ for some $\ell \ge 1$ are precisely*
   $$c_j(y) = \frac{2^{a_0 + dj} y - 1}{q} = c_0(y) + 2^{a_0} y u S_j \qquad (j \ge 0),$$
   *where $c_0(y) = (2^{a_0} y - 1)/q \ge 1$ and $S_j = \sum_{l=0}^{j-1} 2^{dl}$.*
2. *For every $j \ge 1$ and every prime $p \mid q$, $v_p(S_j) = v_p(j)$. In particular, $j \mapsto S_j \bmod q$ is a well-defined bijection on $\mathbb{Z}/q\mathbb{Z}$, and as $j$ runs over $\{0, \dots, q - 1\}$, $c_j(y) \bmod N_q$ visits every residue class modulo $N_q$ congruent to $c_0(y) \pmod{u_q}$ exactly once.*

*Proof.* (1) Since $w \ge 1$ and $q \ge 3$ are odd, $qw + 1 = 2^\ell y$ with $\ell \ge 1$ holds if and only if $2^\ell y \equiv 1 \pmod q$ and $w = (2^\ell y - 1)/q$. Because $\mathrm{ord}_q(2) = d$ and $a_0 \in \{1, \dots, d\}$, $2^\ell y \equiv 1 \pmod q$ with $\ell \ge 1$ is equivalent to $\ell = a_0 + dj$ with $j \ge 0$. Since $y \bmod N_q \in V_q$ implies $y \ge 1$, for every $j \ge 0$ we have $2^{a_0 + dj} y - 1 \ge 2 \cdot 1 - 1 = 1$, odd and divisible by $q$, so $c_j(y)$ is a positive odd integer. The second expression follows from $2^{dj} - 1 = (2^d - 1) S_j = q u S_j$.

(2) For $j \ge 1$ and $p \mid q$, Lemma 1(2) gives $v_p(S_j) = v_p(2^{dj} - 1) - v_p(2^d - 1) = v_p(j)$. For $0 \le j_1 < j_2$, $S_{j_2} - S_{j_1} = 2^{d j_1} S_{j_2 - j_1}$ satisfies $v_p(S_{j_2} - S_{j_1}) = v_p(j_2 - j_1)$ for every $p \mid q$, so $S_{j_2} \equiv S_{j_1} \pmod q$ if and only if $j_2 \equiv j_1 \pmod q$. Hence $j \mapsto S_j \bmod q$ is a well-defined bijection on $\mathbb{Z}/q\mathbb{Z}$. Writing $c_j(y) = c_0(y) + u_q \bigl(2^{a_0} y (u/u_q) S_j\bigr)$ and noting that $\gcd\bigl(2^{a_0} y (u/u_q), q\bigr) = 1$, $c_j(y) \bmod N_q$ visits each of the $q = N_q / u_q$ residue classes modulo $N_q$ congruent to $c_0(y) \pmod{u_q}$ exactly once as $j$ runs over $\{0, \dots, q - 1\}$. $\blacksquare$

**Proposition 1 (Exact Partition Criterion).** *For every odd $q > 1$ and every $t \ge 1$, the following are equivalent:*
1. *Some $x \in R_q(t)$ satisfies Hypothesis (H).*
2. *$t \bmod N_q \in V_q$, and $t \bmod N_q$ has a directed path in $\mathcal{G}_q$ to $R_{\mathrm{core}}$.*
3. *$t \bmod N_q \in V_q$, and $t \bmod N_q$ has a directed path in $\mathcal{G}_q$ of length $\kappa$.*

*Moreover, when (3) holds, there exists $x \in R_q(t)$ satisfying (H) with $a = 1$ (and $i_0 = 0$ if $\kappa \ge 1$) such that*
$$x \le \left(\frac{2^{dq}}{q}\right)^{\kappa + 1} t$$
*(and when $\kappa = 0$, $x = t$ satisfies (H) with $a = 1$).*

*Proof.* $(1) \implies (2)$: Let $x \in R_q(t)$ satisfy (H), so $2^{i_0} x (2^a - q) \equiv 1 \pmod{N_q}$ for some $a \in \{1, \dots, d\}$ and $i_0 \in \{0, \dots, d - 1\}$. Choose $N \ge 0$ with $\mathrm{Col}_q^N(x) = t$.

If no odd step occurs among $x, \mathrm{Col}_q(x), \dots, \mathrm{Col}_q^{N-1}(x)$, then $x = 2^N t$. Choosing $i' \in \{0, \dots, d - 1\}$ with $i' \equiv i_0 + N \pmod d$ and using $2^d \equiv 1 \pmod{N_q}$ yields $2^{i'} t(2^a - q) \equiv 2^{i_0} x(2^a - q) \equiv 1 \pmod{N_q}$, so $t \bmod N_q \in R_{\mathrm{core}} \subseteq V_q$, giving a path of length $0$ to $R_{\mathrm{core}}$.

Otherwise, let $w_m, \dots, w_1$ ($m \ge 1$) be the odd integers from which an odd step is taken along $x, \mathrm{Col}_q(x), \dots, \mathrm{Col}_q^{N-1}(x)$, so that $x = 2^{k_0} w_m$ ($k_0 \ge 0$), $qw_{l+1} + 1 = 2^{k_{l+1}} w_l$ with $k_{l+1} \ge 1$ ($1 \le l < m$; $k_{l+1} \ge 1$ because $qw_{l+1} + 1$ is even while $w_l$ is odd), and $qw_1 + 1 = 2^{k_1} t$ with $k_1 \ge 0$. Since $2^{k_1} t \equiv 1 \pmod q$, we have $\gcd(t, q) = 1$, hence $\gcd(t, N_q) = 1$, and $t \bmod q \in H_q$, so $t \bmod N_q \in V_q$. If $k_1 = 0$, then $t \equiv 1 \pmod q$, so $a_0(t) = d$, $2^d t - t = qut$, and $w_1 = (t - 1)/q \equiv (2^d t - 1)/q \equiv c_0(t \bmod N_q) \pmod{u_q}$ (as $u_q \mid u$); if $k_1 \ge 1$, then $k_1 = a_0(t) + dj$ for some $j \ge 0$ and Lemma 2(1) gives $w_1 = c_j(t) \equiv c_0(t \bmod N_q) \pmod{u_q}$. Similarly, for $1 \le l < m$, $2^{k_{l+1}} w_l \equiv 1 \pmod q$ implies $w_l \bmod N_q \in V_q$ and $w_{l+1} \equiv c_0(w_l \bmod N_q) \pmod{u_q}$. Finally, $x = 2^{k_0} w_m$ gives $2^{i'} w_m(2^a - q) \equiv 1 \pmod{N_q}$ for $i' \in \{0, \dots, d - 1\}$ with $i' \equiv i_0 + k_0 \pmod d$, so $w_m \bmod N_q \in R_{\mathrm{core}} \subseteq V_q$. Thus $(t \bmod N_q) \to (w_1 \bmod N_q) \to \dots \to (w_m \bmod N_q) \in R_{\mathrm{core}}$ is a directed path in $\mathcal{G}_q$.

$(2) \implies (3)$: Truncating a directed path of length $L \ge \kappa$ gives a path of length $\kappa$. Suppose $t \bmod N_q$ has a directed path of length $L < \kappa$ ending at $z \in R_{\mathrm{core}}$ with $2^{i_0} z(2^a - q) \equiv 1 \pmod{N_q}$ ($1 \le a \le d$, $0 \le i_0 < d$). Modulo $q$, this gives $2^{i_0 + a} z \equiv 1 \pmod q$, so $a_0(z) \equiv i_0 + a \pmod d$. Since $2^d \equiv 1 \pmod{N_q}$ and $2^{i_0} z \equiv c_a \pmod{N_q}$, we have
$$2^{a_0(z)} z \equiv 2^{i_0 + a} z \equiv 2^a c_a = (2^a - q)c_a + q c_a \equiv 1 + q c_a \pmod{N_q},$$
whence $c_0(z) \equiv c_a \pmod{u_q}$. Since $c_a \bmod N_q \in R_{\mathrm{core}}$ satisfies $2^a c_a \equiv 1 + q c_a \pmod{N_q}$, we have $a_0(c_a) = a$ and $c_0(c_a) \equiv c_a \pmod{u_q}$, so both $z \to (c_a \bmod N_q)$ and $(c_a \bmod N_q) \to (c_a \bmod N_q)$ are edges in $\mathcal{G}_q$. Appending $\kappa - L$ edges yields a path of length $\kappa$.

$(3) \implies (1)$ and the size bound: If $\kappa = 0$, then $u_q = 1$, $N_q = q$, $c_1 \equiv (2 - q)^{-1} \equiv 2^{-1} \pmod q \in H_q$, and $V_q = H_q = c_1 \langle 2 \rangle = R_{\mathrm{core}}$, so $x = t < (2^{dq}/q) t$ itself satisfies (H) with $a = 1$. Assume $\kappa \ge 1$, and let $z_0 \to z_1 \to \dots \to z_\kappa$ be a directed path in $\mathcal{G}_q$ with $z_0 = t \bmod N_q$. For $m \ge 0$ put
$$D_m = u_q / \gcd(u_q, q^m).$$
Then $D_0 = u_q$, $D_\kappa = 1$ (as $u_q \mid q^\kappa$), and $D_m \mid q D_{m+1}$ (as $\gcd(u_q, q^{m+1}) \mid q \gcd(u_q, q^m)$). The single modulus $D_m$ records, for all primes at once, how much of $u_q$ is still undetermined after $m$ steps, so no per-prime bookkeeping or CRT is needed.

*Lifting step.* Let $z \in V_q$ with $a = a_0(z)$ and integer representative $\tilde z$, and let $Y \in \mathbb{Z}$ with $Y \equiv c_0(z) \pmod{D_{m+1}}$. Let $X$ be the class modulo $N_q$ with $2^a X \equiv 1 + qY \pmod{N_q}$; it exists because $2$ is a unit modulo $N_q$. Then:
- $X \equiv 2^{-a} \equiv z \pmod q$, so $X \in V_q$ and $a_0(X) = a$;
- $q c_0(X) = 2^a X - 1 \equiv qY \pmod{q u_q}$, so $c_0(X) \equiv Y \pmod{u_q}$;
- $2^a(X - \tilde z) \equiv q\bigl(Y - c_0(z)\bigr) \pmod{N_q}$, and $D_m \mid q D_{m+1} \mid q(Y - c_0(z))$ with $D_m \mid N_q$, so $X \equiv z \pmod{D_m}$.

*Induction.* We show for $0 \le m \le \kappa$: for every $Y \equiv c_0(z_m) \pmod{D_m}$ there are $j_1, \dots, j_m \in \{0, \dots, q-1\}$ such that $x_l = c_{j_l}(x_{l-1})$ ($x_0 = t$) satisfy $x_l \bmod N_q \in V_q$ and $c_0(x_m) \equiv Y \pmod{u_q}$. For $m = 0$ take $x_0 = t$, since $D_0 = u_q$. For $m \to m+1$, lift $Y$ at $z = z_{m+1}$ to $X$. Since $z_m \to z_{m+1}$ we have $X \equiv z_{m+1} \equiv c_0(z_m) \pmod{D_m}$, so the case $m$ with target $X$ gives $x_m$ with $c_0(x_m) \equiv X \pmod{u_q}$. Lemma 2(2) then gives $j_{m+1} < q$ with $x_{m+1} = c_{j_{m+1}}(x_m) \equiv X \pmod{N_q}$, so $x_{m+1} \bmod N_q \in V_q$ and $c_0(x_{m+1}) \equiv c_0(X) \equiv Y \pmod{u_q}$.

At $m = \kappa$ we have $D_\kappa = 1$, so the target $Y = c_1$ is allowed. Lemma 2(2) once more gives $x = c_j(x_\kappa) \equiv c_1 \pmod{N_q}$, that is $(2 - q)x \equiv 1 \pmod{N_q}$: $x$ satisfies (H) with $a = 1$, $i_0 = 0$. Each of the $\kappa + 1$ steps has $a_0 + dj \le dq$, so $x_l < (2^{dq}/q)\, x_{l-1}$ and $x \le (2^{dq}/q)^{\kappa + 1} t$. $\blacksquare$

---

### 3. Modulus Parameters, Covering Length, and Main Theorems

Given an integer $m \ge 1$, factor $m = 2^\alpha m_q m'$ uniquely with $\alpha \ge 0$, $m_q, m' \ge 1$ odd, every prime factor of $m_q$ dividing $q$, and $\gcd(m', q) = 1$, and put $M = m_q m' = m / 2^\alpha$. Let $e = \mathrm{ord}_{m'}(2) \ge 1$ (so $e = 1$ if $m' = 1$, while $e \ge 2$ if $m' > 1$ because $m' \ge 3$ is odd). Factor $e = e_q e'$ uniquely with $e_q, e' \ge 1$, every prime factor of $e_q$ dividing $q$, and $\gcd(e', q) = 1$, and let $K \ge 0$ be the least integer with $e_q \mid q^K$ (with $K = 0$ if $e_q = 1$, in particular whenever $m' = 1$). Set
$$P = \mathrm{lcm}(dq^K, e),$$
and for $0 \le n \le \alpha$ define
$$\widetilde{W}(n) = \prod_{p \mid q} p^{\max\bigl(0,\, (n - K)\alpha_p + v_p(m_q) - \nu_p\bigr)} = \frac{\mathrm{lcm}(q^n m_q,\, q^K u_q)}{q^K u_q}, \qquad \widetilde{Q}(n) = \widetilde{W}(n) P,$$
writing $\widetilde{W}_0 = \widetilde{W}(\alpha)$ and $\widetilde{Q}_0 = \widetilde{Q}(\alpha)$. The second equality for $\widetilde{W}(n)$ holds because every prime factor of $q^n m_q$ and of $q^K u_q$ divides $q$, with $v_p(q^n m_q) - v_p(q^K u_q) = (n - K)\alpha_p + v_p(m_q) - \nu_p$. Note that $\widetilde{W}(n)$ and $\widetilde{Q}(n)$ are nondecreasing in $n$.

Let $H = \langle 2 \rangle \subseteq (\mathbb{Z}/m'\mathbb{Z})^\times$ (with $H = \{0\} = \mathbb{Z}/1\mathbb{Z}$ if $m' = 1$), and define $A_0 = \{0\} \subseteq \mathbb{Z}/m'\mathbb{Z}$ and
$$A_k = \{h_0 + qh_1 + \dots + q^{k-1} h_{k-1} : h_0, \dots, h_{k-1} \in H\} \subseteq \mathbb{Z}/m'\mathbb{Z} \qquad (k \ge 1).$$


**Lemma 3 (Covering length modulo $m'$).** *There exists a least integer $\gamma \ge 0$ such that $A_\gamma = \mathbb{Z}/m'\mathbb{Z}$. Moreover, $\gamma = 0$ if and only if $m' = 1$, and when $m' > 1$,*
$$1 \le \gamma \le 1 + \bigl\lceil \max(0, m' - e)/\varphi(e) \bigr\rceil.$$
*(A binary-splitting argument also gives $\gamma \le \lambda_H \lceil \log_2(m'+1) \rceil$, where $\lambda_H$ is the order of $q$ in $(\mathbb{Z}/m'\mathbb{Z})^\times/H$. That bound is not used below and is not formalized.)*

*Proof.* If $m' = 1$, then $A_0 = \{0\} = \mathbb{Z}/1\mathbb{Z}$, so $\gamma = 0$. Assume $m' > 1$, so $m' \ge 3$ is odd, $\gcd(m', q) = 1$, $e \ge 2$, and $|A_0| = 1 < m'$ forces $\gamma \ge 1$; existence follows from the bound below.

*Chowla bound:* Let $U, W \subseteq \mathbb{Z}/m'\mathbb{Z}$ be nonempty subsets with $0 \in W$ such that $\gcd(\tilde{w}, m') = 1$ for every $w \in W \setminus \{0\}$ (where $\tilde{w}$ denotes an integer representative of $w$). We prove $|U + W| \ge \min(m', |U| + |W| - 1)$ by induction on $|W| \ge 1$. For $|W| = 1$, $W = \{0\}$ and $|U + W| = |U| = \min(m', |U|)$. For $|W| \ge 2$, if $U + W = \mathbb{Z}/m'\mathbb{Z}$ there is nothing to prove. Otherwise, $U \subseteq U + W \neq \mathbb{Z}/m'\mathbb{Z}$, so $U$ is a nonempty proper subset of $\mathbb{Z}/m'\mathbb{Z}$. Pick $w^* \in W \setminus \{0\}$. Since $\gcd(\tilde{w}^*, m') = 1$, $w^*$ generates $\mathbb{Z}/m'\mathbb{Z}$; if $U + w^* \subseteq U$, finiteness of $U$ would give $U + w^* = U$ and hence (as $U \neq \varnothing$) $U = \mathbb{Z}/m'\mathbb{Z}$, a contradiction. Thus there exists $u_0 \in U$ with $u_0 + w^* \notin U$. Setting $U' = U \cup (W + u_0)$ and $W' = W \cap (U - u_0) = (U \cap (W + u_0)) - u_0$ gives $U' \neq \varnothing$, $0 \in W'$, $w^* \notin W'$ (so $1 \le |W'| < |W|$), $W' \setminus \{0\} \subseteq W \setminus \{0\}$, $U' + W' = (U + W') \cup (W + u_0 + W') \subseteq U + W$, and
$$|U'| + |W'| = |U \cup (W + u_0)| + |U \cap (W + u_0)| = |U| + |W + u_0| = |U| + |W|.$$
By the induction hypothesis, $|U + W| \ge |U' + W'| \ge \min(m', |U'| + |W'| - 1) = \min(m', |U| + |W| - 1)$.

Now set $S = \{0\} \cup \{2^j - 1 \bmod m' : 1 \le j < e,\, \gcd(j, e) = 1\} \subseteq H - 1 \subseteq \mathbb{Z}/m'\mathbb{Z}$. Because $e = \mathrm{ord}_{m'}(2) \ge 2$, the residues $2^j - 1 \bmod m'$ for $1 \le j < e$ are nonzero and pairwise distinct, so $|S| = \varphi(e) + 1$. Every prime $\ell \mid m'$ is odd, so $d_\ell := \mathrm{ord}_\ell(2) \ge 2$, and $2^e \equiv 1 \pmod{m'}$ gives $d_\ell \mid e$; if $\ell \mid 2^j - 1$, then $d_\ell \mid j$, impossible when $\gcd(j, e) = 1$. Hence every nonzero element of $S$—and therefore of $q^k S$, since $\gcd(q, m') = 1$—is coprime to $m'$. Since $(A_k + q^k) + q^k S \subseteq A_k + q^k H = A_{k+1}$, Chowla's theorem yields $|A_{k+1}| \ge \min(m', |A_k| + \varphi(e))$ for all $k \ge 1$. Starting from $|A_1| = |H| = e$, induction gives $|A_k| \ge \min(m', e + (k - 1)\varphi(e))$ for all $k \ge 1$, whence $\gamma \le 1 + \lceil \max(0, m' - e)/\varphi(e) \rceil$. $\blacksquare$

Put
$$s = \begin{cases} K + \kappa + 1 = \kappa + 1 & \text{if } m' = 1,\\ K + \kappa + \gamma + 2 & \text{if } m' > 1, \end{cases}$$
so $s \ge K + \kappa + 1$ in all cases. For each prime $p \mid q$, define (with the convention that an empty product equals $1$)
$$E_p^* = \prod_{\substack{p' \mid q \\ p' \neq p}} {p'}^{\max\bigl(\alpha_{p'},\, (\kappa + 1)\alpha_{p'} - \nu_{p'}\bigr)}, \qquad J_0^* = \begin{cases} q - 1 & \text{if } \kappa = 0,\\ \displaystyle\sum_{p \mid q} (p^{\alpha_p} - 1) E_p^* & \text{if } \kappa \ge 1. \end{cases}$$
For $a \in \{1, \dots, d\}$, set
$$B_0(a) = \begin{cases} \kappa a & \text{if } m' = 1,\\ (K + \kappa + 1)a + \gamma e & \text{if } m' > 1, \end{cases}$$
$$E^*(a) = \alpha + \widetilde{Q}_0 + \max\Bigl(\lceil \log_2(M + 1) \rceil,\;\; dq^K - 1 + (s - 1)J_0^* P + B_0(a) - \lfloor s \log_2 q \rfloor\Bigr),$$
$$E^{**} = \alpha + \widetilde{Q}_0 + \max\Bigl(\lceil \log_2(M + 1) \rceil,\;\; dq^K - 1 + (s - 1)J_0^* P + B_0(1) + (\kappa + 1)dq - \lfloor (s + \kappa + 1)\log_2 q \rfloor\Bigr).$$

**Theorem A (Coverage and Haar Measure One).** *Let $q > 1$ be odd and let $t \ge 1$. Suppose that some $x \in R_q(t)$ satisfies Hypothesis (H) (equivalently, by Proposition 1, $t \bmod N_q \in V_q$ and $t \bmod N_q$ has a directed path of length $\kappa$ in $\mathcal{G}_q$). Then for every integer $m \ge 1$ and all $r, B \in \mathbb{N}$, there exist $n \in \{0, \dots, \alpha\}$ (depending only on $r \bmod 2^\alpha$) and $w \in \mathbb{N}$ such that $w \to t$, $w \equiv r \pmod m$, $w > B$, and:*
1. *If $t$ itself satisfies (H) with exponent $a \in \{1, \dots, d\}$ (in particular, $a = 1$ may always be taken when $\kappa = 0$), then*
   $$w < \max\left( 2^{\alpha + \widetilde{Q}(n)}(B + M + 1),\;\; \frac{2^{\alpha + \widetilde{Q}(n) + dq^K - 1 + (s - 1)J_0^* P + B_0(a)}\, t}{q^{n + s}} \right) \le (B + 1)\, t\, 2^{E^*(a)}.$$
2. *If $t$ does not satisfy (H) (then necessarily $\kappa \ge 1$),*
   $$w < \max\left( 2^{\alpha + \widetilde{Q}(n)}(B + M + 1),\;\; \frac{2^{\alpha + \widetilde{Q}(n) + dq^K - 1 + (s - 1)J_0^* P + B_0(1) + (\kappa + 1)dq}\, t}{q^{n + s + \kappa + 1}} \right) \le (B + 1)\, t\, 2^{E^{**}}.$$

*Consequently (§6), $\overline{R_q(t)} = \widehat{\mathbb{Z}}$ and $\mu\bigl(\overline{R_q(t)}\bigr) = 1$.*

**Theorem B (Finite-Depth Trap and Haar Measure Zero).** *Let $q > 1$ be odd and let $t \ge 1$. Suppose that no $x \in R_q(t)$ satisfies Hypothesis (H) (equivalently, by Proposition 1, either $t \bmod q \notin H_q$, or $t \bmod N_q \in V_q$ has no directed path of length $\kappa$ in $\mathcal{G}_q$). Then:*
1. *(Bounded odd depth.) Every backward chain of odd steps in $R_q(t)$ has length at most $\kappa$ (in particular, no such chain of length $m \ge 1$ exists when $g_0 = 1$).*
2. *(Sparsity modulo $2^n$ and measure zero.) For every $n \ge 1$,*
   $$|R_q(t) \bmod 2^n| \le (n + 1)^{\kappa + 1}.$$
   *Consequently (§6), $\overline{R_q(t)} \neq \widehat{\mathbb{Z}}$ and $\mu\bigl(\overline{R_q(t)}\bigr) = 0$.*
3. *(Non-periodicity and polylogarithmic growth.) No element of $R_q(t)$ (in particular, not $t$) is periodic under $\mathrm{Col}_q$, and for $X \ge 2$,*
   $$|R_q(t) \cap [1, X]| = O_q\bigl((\log X)^{\kappa + 1}\bigr)$$
   *(uniformly in $t \ge 1$).*

The hypotheses of Theorems A and B are complementary, so every pair $(q, t)$ falls under exactly one of them. Hence $\mu\bigl(\overline{R_q(t)}\bigr) \in \{0, 1\}$ (§6), and Proposition 1 decides which value occurs by a finite check on $\mathcal{G}_q$.

---

### 4. Proof of Theorem A

Suppose some element of $R_q(t)$ satisfies (H). If $t$ itself satisfies (H) with exponent $a \in \{1, \dots, d\}$, set $x = t$. Note that when $\kappa = 0$, $u_q = 1$ and $N_q = q$, so $c_1 \equiv 2^{-1} \pmod q \in H_q$ and $R_{\mathrm{core}} = V_q = H_q = c_1 \langle 2 \rangle$; thus Proposition 1 guarantees that $t$ itself satisfies (H) with $a = 1$. If $t$ does not satisfy (H), then $\kappa \ge 1$ and Proposition 1 yields $x \in R_q(t)$ satisfying (H) with $a = 1$ and $x \le (2^{dq}/q)^{\kappa + 1} t$.

Since $R_q(x) \subseteq R_q(t)$ by transitivity of $\to$, it suffices to prove that for every $x \ge 1$ satisfying (H) with fixed $a \in \{1, \dots, d\}$ and $i_0 \in \{0, \dots, d - 1\}$, every $m \ge 1$, and all $r, B \in \mathbb{N}$, there exist $n \in \{0, \dots, \alpha\}$ (depending only on $r \bmod 2^\alpha$) and $w \in R_q(x)$ such that $w \equiv r \pmod m$, $w > B$, and
$$w < \max\left( 2^{\alpha + \widetilde{Q}(n)}(B + M + 1),\;\; \frac{2^{\alpha + \widetilde{Q}(n) + dq^K - 1 + (s - 1)J_0^* P + B_0(a)}\, x}{q^{n + s}} \right).$$
Indeed, since $\widetilde{Q}(n) \le \widetilde{Q}_0$ for $0 \le n \le \alpha$, $B + M + 1 \le (B + 1)(M + 1) \le (B + 1)\, t\, 2^{\lceil \log_2(M+1) \rceil}$, $1 \le B + 1$, $q^{-n} \le 1$, and $q^{-N} \le 2^{-\lfloor N \log_2 q \rfloor}$ for all $N \ge 1$ (noting $s \ge 1$), taking $x = t$ gives Theorem A(1) and taking $a = 1$, $x \le (2^{dq}/q)^{\kappa + 1} t$ gives Theorem A(2).

Fix $m \ge 1$ and $r, B \in \mathbb{N}$, with parameters as in Section 3. Throughout, $p$ and $p'$ denote prime divisors of $q$.

#### Step 1. Lifting for $P$, starting point, and primer

**Lemma 4 (Per-prime lifting for $P$).** *Write $P = d q^K f$. Then $\gcd(f, q) = 1$, and for every prime $p \mid q$ and integer $N \ge 1$,*
$$v_p(2^{NP} - 1) = (K + 1)\alpha_p + \nu_p + v_p(N).$$
*In particular, $2^{NP} \equiv 1 \pmod{\Lambda}$ for all $N \ge 0$, where $\Lambda = q^{K+1} u_q = \prod_{p \mid q} p^{(K+1)\alpha_p + \nu_p}$.*

*Proof.* By definition, $P = \mathrm{lcm}(d q^K, e) = d q^K f$ with $f = e / \gcd(d q^K, e)$. For any prime $p \mid q$, $v_p(e) = v_p(e_q) \le v_p(q^K) \le v_p(d q^K)$, so $v_p(\gcd(d q^K, e)) = v_p(e)$ and hence $p \nmid f$. Thus $\gcd(f, q) = 1$. Since $v_p(N q^K f) = K \alpha_p + v_p(N)$, Lemma 1(2) gives
$$v_p(2^{NP} - 1) = v_p(2^{d(N q^K f)} - 1) = \alpha_p + \nu_p + K\alpha_p + v_p(N) = (K + 1)\alpha_p + \nu_p + v_p(N).$$
Hence $2^{NP} \equiv 1 \pmod{\Lambda}$ for $N \ge 1$, and trivially for $N = 0$. $\blacksquare$

**Lemma 5 (Starting point).** *Assume $x \ge 1$ satisfies (H) with exponents $(a, i_0)$, and let $c_* \in \mathbb{Z}$ satisfy $(2^a - q)c_* \equiv 1 \pmod{\Lambda}$. There exists $\lambda_0 \in \{0, \dots, d q^K - 1\}$ such that $y_0 = 2^{\lambda_0} x$ satisfies $y_0 \equiv c_* \pmod{\Lambda}$, $y_0 \ge 1$, and $y_0 \to x$.*

*Proof.* Since $N_q$ and $\Lambda$ share the same prime factors, $\gcd(2^a - q, \Lambda) = 1$ and (H) implies $\gcd(2^{i_0} x, \Lambda) = 1$, so there exists $\chi \in \mathbb{Z}$ with $2^{i_0} x \chi \equiv c_* \pmod{\Lambda}$. Reducing modulo $N_q$ (as $N_q \mid \Lambda$) and multiplying by $2^a - q$ gives $2^{i_0} x(2^a - q)\chi \equiv 1 \pmod{N_q}$, whence $\chi \equiv 1 \pmod{N_q}$ by (H).

The residues $2^{d m_0} \bmod \Lambda$ for $0 \le m_0 < q^K$ are pairwise distinct: if $2^{d m_0} \equiv 2^{d m'_0} \pmod{\Lambda}$ with $0 \le m'_0 < m_0 < q^K$, then $2^{d(m_0 - m'_0)} \equiv 1 \pmod{\Lambda}$, so Lemma 1(2) gives $\alpha_p + \nu_p + v_p(m_0 - m'_0) \ge (K + 1)\alpha_p + \nu_p$, hence $v_p(m_0 - m'_0) \ge K \alpha_p$ for every $p \mid q$, forcing $q^K \mid m_0 - m'_0$, a contradiction. Each $2^{d m_0}$ satisfies $2^{d m_0} \equiv 1 \pmod{N_q}$ (as $N_q \mid 2^d - 1$), and there are exactly $\Lambda / N_q = q^K$ residue classes modulo $\Lambda$ congruent to $1 \pmod{N_q}$. Therefore $\chi \equiv 2^{d m_0} \pmod{\Lambda}$ for some $0 \le m_0 < q^K$. Setting $\lambda_0 = d m_0 + i_0 \in \{0, \dots, d q^K - 1\}$ yields $y_0 = 2^{\lambda_0} x = 2^{d m_0}(2^{i_0} x) \equiv \chi(2^{i_0} x) \equiv c_* \pmod{\Lambda}$, with $y_0 \ge 1$ and $y_0 \to x$ by $\lambda_0$ halvings. $\blacksquare$

Given base exponents $b_1, \dots, b_s \ge 1$ and shifts $j_1, \dots, j_s \ge 0$, define $a_l = b_l + j_l P \ge 1$ and recursively $y_l = (2^{a_l} y_{l-1} - 1)/q$ for $1 \le l \le s$ whenever $q \mid 2^{a_l} y_{l-1} - 1$. Whenever $y_{l-1} \ge 1$ and $q \mid 2^{a_l} y_{l-1} - 1$, $2^{a_l} y_{l-1} - 1 \ge 1$ is odd and divisible by the odd integer $q \ge 3$, so $y_l \ge 1$ is a positive odd integer satisfying $\mathrm{Col}_q(y_l) = 2^{a_l} y_{l-1}$, whence $y_l \to y_{l-1}$; in this case we say *step $l$ is integral*. Because $d \mid P$, for $l = 1$ (since $y_0 \ge 1$) or for $2 \le l \le s$ when step $l - 1$ is integral (so $y_{l-1} \ge 1$), step $l$ is integral if and only if $2^{b_l} y_{l-1} \equiv 1 \pmod q$, independently of $j_l$.

**Lemma 6 (Primer).** *Let $0 \le l \le s$, put $b_1 = \dots = b_l = a$, and let $j_1, \dots, j_l \ge 0$ be arbitrary. If steps $1, \dots, l$ are integral, then for every prime $p \mid q$,*
$$y_l \equiv c_* \pmod{p^{e_l(p)}}, \qquad e_l(p) = \max\bigl(0,\, (K + 1 - l)\alpha_p + \nu_p\bigr).$$
*Moreover, steps $1, \dots, K + 1$ are integral for every choice of shifts (when $b_1 = \dots = b_{K+1} = a$).*

*Proof.* Induct on $l \ge 0$, the case $l = 0$ being Lemma 5 since $v_p(\Lambda) = (K + 1)\alpha_p + \nu_p = e_0(p)$. For $l \ge 1$, assume $y_{l-1} \equiv c_* \pmod{p^{E_{l-1}}}$ where $E_{l-1} = e_{l-1}(p) \le (K + 1)\alpha_p + \nu_p = v_p(\Lambda)$. If $E_{l-1} < \alpha_p$, then $(K + 2 - l)\alpha_p + \nu_p < \alpha_p$, so $e_l(p) = 0$ and the congruence holds trivially. Assume $E_{l-1} \ge \alpha_p$. By Lemma 4, $2^{j_l P} \equiv 1 \pmod{\Lambda}$, and by construction $(2^a - q)c_* \equiv 1 \pmod{\Lambda}$, so
$$2^{a_l} y_{l-1} - 1 = 2^{j_l P} 2^a y_{l-1} - 1 \equiv 2^a c_* - 1 \equiv q c_* \pmod{p^{E_{l-1}}}.$$
In particular, when $l - 1 \le K$, we have $e_{l-1}(p) \ge \alpha_p$ for every $p \mid q$, so $q \mid 2^{a_l} y_{l-1} - 1$ and step $l$ is integral for all shifts. Whenever step $l$ is integral and $E_{l-1} \ge \alpha_p$, $q y_l = 2^{a_l} y_{l-1} - 1 \equiv q c_* \pmod{p^{E_{l-1}}}$; dividing by $q$ (with $v_p(q) = \alpha_p$) gives $y_l \equiv c_* \pmod{p^{E_{l-1} - \alpha_p}}$, where $E_{l-1} - \alpha_p = e_l(p)$. $\blacksquare$

#### Step 2. The $2$-adic tail

For $\delta \in \{0, 1\}$, set $S_\delta(z) = (q^\delta z + \delta)/2$. For a word $\omega = \delta_1 \cdots \delta_\ell \in \{0, 1\}^\ell$ ($\ell \ge 0$), define $S_\omega = S_{\delta_\ell} \circ \dots \circ S_{\delta_1}$ ($S_\varnothing = \mathrm{id}$) and define $\Phi(\omega) \in \mathbb{N}$ recursively by $\Phi(\varnothing) = 0$ and $\Phi(\delta \omega') = q^{\mathrm{ones}(\omega')} \delta + 2\Phi(\omega')$, where $\mathrm{ones}(\omega) = \sum_{l=1}^\ell \delta_l$. Induction on $\ell \ge 0$ gives
$$S_\omega(z) = \frac{q^{\mathrm{ones}(\omega)} z + \Phi(\omega)}{2^\ell}, \qquad \Phi(\omega) \ge 0.$$

**Lemma 7 (Tail word).** *If $z \in \mathbb{N}$ and $2^\ell \mid q^{\mathrm{ones}(\omega)} z + \Phi(\omega)$, then $S_\omega(z) \in \mathbb{N}$ and $z \to S_\omega(z)$.*

*Proof.* Induct on $\ell \ge 0$ ($\ell = 0$ is trivial). For $\omega = \delta \omega'$ ($\ell \ge 1$), $q^{\mathrm{ones}(\omega)} z + \Phi(\omega) = q^{\mathrm{ones}(\omega')}(q^\delta z + \delta) + 2\Phi(\omega')$ is even and $q^{\mathrm{ones}(\omega')}$ is odd, so $q^\delta z + \delta$ is even and $z \equiv \delta \pmod 2$. Thus $S_\delta(z) \in \mathbb{N}$, $\mathrm{Col}_q^{1 + \delta}(z) = S_\delta(z)$, and $q^{\mathrm{ones}(\omega)} z + \Phi(\omega) = 2\bigl(q^{\mathrm{ones}(\omega')} S_\delta(z) + \Phi(\omega')\bigr)$, so $2^{\ell - 1} \mid q^{\mathrm{ones}(\omega')} S_\delta(z) + \Phi(\omega')$. By the induction hypothesis, $z \to S_\delta(z) \to S_{\omega'}(S_\delta(z)) = S_\omega(z) \in \mathbb{N}$. $\blacksquare$

Let $\bar r = r \bmod m \in \{0, \dots, m - 1\}$, and write $\bar r = 2^\alpha Q_0 + C_0$ with $C_0 = r \bmod 2^\alpha \in \{0, \dots, 2^\alpha - 1\}$ and $Q_0 \in \{0, \dots, M - 1\}$. Set $r_0 = \bar r$ and, for $0 \le l < \alpha$, $\delta_{l+1} = r_l \bmod 2$ and $r_{l+1} = S_{\delta_{l+1}}(r_l) \in \mathbb{N}$. Define $C_l \in \mathbb{N}$ ($0 \le l \le \alpha$) recursively by $C_{l+1} = S_{\delta'_{l+1}}(C_l)$ with $\delta'_{l+1} = C_l \bmod 2$ ($0 \le l < \alpha$). Setting $n_l = \delta_1 + \dots + \delta_l$ ($n_0 = 0$), induction on $0 \le l \le \alpha$ shows that $r_l = 2^{\alpha - l} q^{n_l} Q_0 + C_l$ and (for $l < \alpha$) $\delta_{l+1} = \delta'_{l+1}$: for $l = 0$ this is $r_0 = 2^\alpha Q_0 + C_0$ (with $r_0 \equiv C_0 \pmod 2$ if $\alpha > 0$), and for $l < \alpha$,
$$r_{l+1} = \frac{q^{\delta_{l+1}}(2^{\alpha - l} q^{n_l} Q_0 + C_l) + \delta_{l+1}}{2} = 2^{\alpha - l - 1} q^{n_{l+1}} Q_0 + C_{l+1},$$
which also yields $r_{l+1} \equiv C_{l+1} \pmod 2$ and $\delta_{l+2} = \delta'_{l+2}$ whenever $l + 1 < \alpha$.

Put $\sigma = \delta_1 \cdots \delta_\alpha$ ($\sigma = \varnothing$ if $\alpha = 0$), $n = \mathrm{ones}(\sigma) = n_\alpha \in \{0, \dots, \alpha\}$ (depending only on $C_0 = r \bmod 2^\alpha$), $\Phi_\sigma = \Phi(\sigma) \ge 0$, and $\rho = r_\alpha = S_\sigma(\bar r) \in \mathbb{N}$. Induction on $0 \le l \le \alpha$ gives $C_l \le q^{n_l} 2^{\alpha - l} - 1$: at $l = 0$, $C_0 \le 2^\alpha - 1$; for $l < \alpha$, if $\delta'_{l+1} = 0$, then $C_l$ is even while $q^{n_l} 2^{\alpha - l} - 1$ is odd, so $C_l \le q^{n_l} 2^{\alpha - l} - 2$ and $C_{l+1} = C_l/2 \le q^{n_{l+1}} 2^{\alpha - l - 1} - 1$; if $\delta'_{l+1} = 1$, then $C_{l+1} = (q C_l + 1)/2 \le q^{n_{l+1}} 2^{\alpha - l - 1} - (q - 1)/2 \le q^{n_{l+1}} 2^{\alpha - l - 1} - 1$ since $q \ge 3$. At $l = \alpha$, $C_\alpha \le q^n - 1$, whence
$$2^\alpha \rho = q^n \bar r + \Phi_\sigma, \qquad \rho = q^n Q_0 + C_\alpha \le q^n(M - 1) + (q^n - 1) = q^n M - 1.$$

**Lemma 8 (Tail matching).** *If $y \in \mathbb{N}$, $y \equiv \rho \pmod{q^n m_q m'}$, and $y \ge \rho + q^n(B + 1)$, then $w = \bar r + 2^\alpha \frac{y - \rho}{q^n}$ is an integer with $B < w \le \frac{2^\alpha}{q^n} y$, $w \equiv r \pmod m$, and $w \to y$.*

*Proof.* Since $q^n M = q^n m_q m' \mid y - \rho$, $z = (y - \rho)/q^n \in \mathbb{Z}$ is divisible by $M$ and satisfies $z \ge B + 1$. Thus $w \in \mathbb{N}$, $w - \bar r = 2^\alpha z$ is divisible by $2^\alpha M = m$ (so $w \equiv r \pmod m$), and $w \ge 2^\alpha(B + 1) > B$. Using $q^n \bar r - 2^\alpha \rho = -\Phi_\sigma \le 0$ gives
$$w = \frac{q^n \bar r + 2^\alpha(y - \rho)}{q^n} = \frac{2^\alpha y - \Phi_\sigma}{q^n} \le \frac{2^\alpha}{q^n}\, y.$$
Finally, $q^n w + \Phi_\sigma = 2^\alpha y$, so Lemma 7 gives $w \to S_\sigma(w) = y$. $\blacksquare$

#### Step 3. Steering modulo $m'$

Put $K_0 = K + \kappa + 1$, and fix $b_1 = \dots = b_{K_0} = a$.

**Lemma 9 (Steering modulo $m'$).** *There exist $b_{K_0 + 1}, \dots, b_s \in \{1, \dots, e\}$ such that, for every shift sequence whose path is integral up to step $s$, $y_s \equiv \rho \pmod{m'}$.*

*Proof.* If $m' = 1$, then $s = K_0$ and the congruence modulo $1$ is trivial. Assume $m' > 1$, so $s = K_0 + \tau_0$ with $\tau_0 = \gamma + 1 \ge 2$ by Lemma 3. Since $e \mid P$, $2^P \equiv 1 \pmod{m'}$; since $\gcd(q, m') = 1$, every integral step satisfies $q y_l \equiv 2^{b_l} y_{l-1} - 1 \pmod{m'}$, so $y_l \bmod m'$ is determined by $y_{l-1} \bmod m'$ and $b_l$, independently of all shifts. Write $\bar y_l = y_{K_0 + l} \bmod m'$ ($0 \le l \le \tau_0$) and $\theta_l = b_{K_0 + l}$ ($1 \le l \le \tau_0$); note that $\bar y_0$ is independent of $j_1, \dots, j_{K_0}$ whenever steps $1, \dots, K_0$ are integral. By induction on $l \in \{0, \dots, \tau_0\}$, in $\mathbb{Z}/m'\mathbb{Z}$,
$$q^l \bar y_l \equiv 2^{\theta_1 + \dots + \theta_l} \bar y_0 - \sum_{k=1}^l q^{k-1} 2^{\theta_{k+1} + \dots + \theta_l}$$
(multiplying $q \bar y_l \equiv 2^{\theta_l} \bar y_{l-1} - 1$ by $q^{l-1}$). Setting $l = \tau_0$ and $\eta_k = \sum_{l=k+1}^{\tau_0} \theta_l$ ($0 \le k \le \tau_0$, $\eta_{\tau_0} = 0$) gives $q^{\tau_0} \bar y_{\tau_0} \equiv 2^{\eta_0} \bar y_0 - \sum_{k=1}^{\tau_0} q^{k-1} 2^{\eta_k} \pmod{m'}$.

Since $A_\gamma = \mathbb{Z}/m'\mathbb{Z}$, choose $h_1, \dots, h_\gamma \in H$ with $\sum_{k=1}^\gamma q^{k-1} h_k \equiv \bar y_0 - q^\gamma - q^{\gamma+1} \rho \pmod{m'}$. Write $h_k \equiv 2^{\tilde\eta_k} \pmod{m'}$ with $0 \le \tilde\eta_k < e$ ($1 \le k \le \gamma$), set $\tilde\eta_0 = \tilde\eta_{\tau_0} = 0$, and let $\theta_l \in \{1, \dots, e\}$ ($1 \le l \le \tau_0$) be the unique integer with $\theta_l \equiv \tilde\eta_{l-1} - \tilde\eta_l \pmod e$. Then $\eta_k \equiv \tilde\eta_k \pmod e$ for all $0 \le k \le \tau_0$. Since $2^e \equiv 1 \pmod{m'}$,
$$q^{\gamma + 1} \bar y_{\tau_0} \equiv \bar y_0 - (\bar y_0 - q^\gamma - q^{\gamma + 1} \rho) - q^\gamma = q^{\gamma + 1} \rho \pmod{m'}.$$
Since $\gcd(q, m') = 1$, $y_s \equiv \bar y_{\tau_0} \equiv \rho \pmod{m'}$. $\blacksquare$

#### Step 4. Perturbation, single-digit control, and shift selection

Fix $b_1, \dots, b_s$ as above. When $m' = 1$, $s = \kappa + 1$, $b_1 = \dots = b_s = a$, so $\sum_{l=1}^{s-1} b_l = \kappa a = B_0(a)$ and $b_s = a \le d \le P$. When $m' > 1$, $b_1 = \dots = b_{K_0} = a$ and $b_{K_0 + 1}, \dots, b_s \in \{1, \dots, e\}$, so $\sum_{l=1}^{s-1} b_l \le B_0(a)$ and $b_s \le e \le P$. Thus $\sum_{l=1}^{s-1} b_l \le B_0(a)$ and $b_s \le P$ in all cases.

**Lemma 10 (Perturbation).** *Let $j$ and $j'$ be shift sequences of length $s$ that differ only at index $k \ge 1$, and put $\Delta = |j'_k - j_k| > 0$. Suppose the path $y$ of $j$ is integral up to step $L$, where $k \le L \le s$. For $i \ge 0$ and each prime $p \mid q$, define*
$$\ell_p(i) = (K - i)\alpha_p + \nu_p + v_p(\Delta).$$
*If $k + i \le L$ and $\ell_p(i) \ge 0$ for every prime $p \mid q$, then the path $y'$ of $j'$ is integral up to step $k + i$, and for every $p \mid q$, $v_p(y'_{k+i} - y_{k+i}) = \ell_p(i)$.*

*Proof.* Induct on $i \ge 0$. For $i = 0$, $y'_l = y_l \ge 1$ for $0 \le l < k$, and step $k$ is integral for $y'$ because $y'_{k-1} = y_{k-1}$ and $b'_k = b_k$. Writing $\underline{a}_k = \min(a_k, a'_k)$ and $\epsilon = \mathrm{sgn}(j'_k - j_k) \in \{\pm 1\}$, we have
$$y'_k - y_k = \epsilon\, \frac{2^{\underline{a}_k} y_{k-1}(2^{\Delta P} - 1)}{q}.$$
Since $2^{\underline{a}_k} y_{k-1} \equiv 2^{b_k} y_{k-1} \equiv 1 \pmod q$, $v_p(2^{\underline{a}_k} y_{k-1}) = 0$, and Lemma 4 yields $v_p(y'_k - y_k) = (K + 1)\alpha_p + \nu_p + v_p(\Delta) - \alpha_p = \ell_p(0)$.

For $i \ge 1$, assume $\ell_p(i) \ge 0$ for every $p \mid q$. Then $\ell_p(i - 1) = \ell_p(i) + \alpha_p \ge \alpha_p \ge 0$ for every $p \mid q$. By the induction hypothesis, $y'$ is integral up to step $k + i - 1$ (so $y'_{k+i-1} \ge 1$) and $y'_{k+i-1} \equiv y_{k+i-1} \pmod q$. Because step $k + i$ is integral for $y$ (as $k + i \le L$) and $b'_{k+i} = b_{k+i}$, we have $2^{b'_{k+i}} y'_{k+i-1} \equiv 2^{b_{k+i}} y_{k+i-1} \equiv 1 \pmod q$, so step $k + i$ is integral for $y'$ as well. Since $j'_{k+i} = j_{k+i}$, we have $a'_{k+i} = a_{k+i}$ and
$$y'_{k+i} - y_{k+i} = \frac{2^{a_{k+i}}(y'_{k+i-1} - y_{k+i-1})}{q},$$
giving $v_p(y'_{k+i} - y_{k+i}) = \ell_p(i - 1) - \alpha_p = \ell_p(i)$ for every $p \mid q$. $\blacksquare$

**Lemma 11 (Single-digit control).** *Fix a prime $p \mid q$, an index $k \ge 1$, a digit position $v \ge 0$, and a delay $i \ge 0$ such that $k + i \le s$ and*
$$h = (K - i)\alpha_p + \nu_p + v \ge 0.$$
*Let $E_0 \ge 1$ be an integer coprime to $p$ such that $(K - i)\alpha_{p'} + \nu_{p'} + v_{p'}(E_0) \ge \alpha_{p'}$ for every prime $p' \neq p$ dividing $q$. Let $j$ be a shift sequence whose path $y$ is integral up to step $k + i$. For $\beta \in \{0, \dots, p - 1\}$, let $j^{(\beta)}$ replace $j_k$ by $j_k + \beta p^v E_0$, with path $y^{(\beta)}$. Then:*
1. *Every $y^{(\beta)}$ is integral up to step $k + i$, and $y^{(\beta)}_l \equiv y_l \pmod q$ for all $0 \le l < k + i$.*
2. *At step $k + i$, $y^{(\beta)}_{k+i} \equiv y_{k+i} \pmod{p^h}$ and $y^{(\beta)}_{k+i} \equiv y_{k+i} \pmod{{p'}^{(K - i)\alpha_{p'} + \nu_{p'} + v_{p'}(E_0)}}$ for every prime $p' \neq p$ dividing $q$.*
3. *As $\beta$ varies over $\{0, \dots, p - 1\}$, the residues $y^{(\beta)}_{k+i} \bmod p^{h+1}$ are pairwise distinct and comprise all $p$ residue classes modulo $p^{h+1}$ congruent to $y_{k+i} \bmod p^h$.*

*Proof.* For $\beta = 0$, $y^{(0)} = y$ and (1)–(2) are trivial. For $\beta \in \{1, \dots, p - 1\}$, apply Lemma 10 with $L = k + i$ and $\Delta = \beta p^v E_0 > 0$. Since $p \nmid \beta E_0$, $v_p(\Delta) = v$ and $v_{p'}(\Delta) \ge v_{p'}(E_0)$ for every $p' \neq p$ dividing $q$. Thus at every delay $i' \in \{0, \dots, i\}$, $\ell_p(i') = h + (i - i')\alpha_p \ge 0$ and $\ell_{p'}(i') \ge (K - i)\alpha_{p'} + \nu_{p'} + v_{p'}(E_0) + (i - i')\alpha_{p'} \ge (i - i' + 1)\alpha_{p'} \ge \alpha_{p'}$. For $i' < i$, both $\ell_p(i') \ge \alpha_p$ and $\ell_{p'}(i') \ge \alpha_{p'}$ (while $y^{(\beta)}_l = y_l$ for $0 \le l < k$), proving (1) and (2).

For (3), let $0 \le \beta' < \beta \le p - 1$ and put $g = 2^{p^v E_0 P}$. By Lemma 4, $\lambda := v_p(g - 1) = (K + 1)\alpha_p + \nu_p + v = h + (i + 1)\alpha_p \ge 1$. Iterating the difference identities yields the integer identity
$$q^{i+1}\bigl(y^{(\beta)}_{k+i} - y^{(\beta')}_{k+i}\bigr) = 2^{a_{k+1} + \dots + a_{k+i} + a_k + \beta' p^v E_0 P}\, y_{k-1}\, (g^{\beta - \beta'} - 1)$$
(with the sum $a_{k+1} + \dots + a_{k+i}$ empty if $i = 0$). Since $y_{k-1} \equiv 2^{-a_k} \pmod q$ is a unit at $p$ and $p \nmid (\beta - \beta')$, Lemma 1(1) yields $v_p(g^{\beta - \beta'} - 1) = \lambda = h + (i + 1)\alpha_p$. Subtracting $v_p(q^{i+1}) = (i + 1)\alpha_p$ gives $v_p(y^{(\beta)}_{k+i} - y^{(\beta')}_{k+i}) = h$, so $y^{(\beta)}_{k+i} \not\equiv y^{(\beta')}_{k+i} \pmod{p^{h+1}}$. By (2), all $p$ residues lie in $y_{k+i} \bmod p^h$, hence exhaust all $p$ lifts modulo $p^{h+1}$. $\blacksquare$

For a target step $T \in \{K + 1, \dots, s\}$, a prime $p \mid q$, and a level $h \ge 0$ with $h < \alpha_p$ (if $T < s$) or $h < K\alpha_p + \nu_p$ (if $T = s$), define the **controller** $(k, v)$ of $(T, p, h)$ by taking $v \in \{0, \dots, \alpha_p - 1\}$ unique with $v \equiv h - \nu_p \pmod{\alpha_p}$, $\delta = (\nu_p + v - h)/\alpha_p \in \mathbb{Z}$, and $k = T - K - \delta$ (delay $i = T - k = K + \delta$). Then $(K - i)\alpha_p + \nu_p + v = h$, and since $\delta \in \mathbb{Z}$, $h \ge 0$, and $v \le \alpha_p - 1$,
$$\delta \le \left\lfloor \frac{\nu_p + \alpha_p - 1}{\alpha_p} \right\rfloor = \left\lceil \frac{\nu_p}{\alpha_p} \right\rceil \le \kappa,$$
so $i \le K + \kappa$. When $T < s$ and $h < \alpha_p$, $\nu_p + v - h \ge 1 - \alpha_p > -\alpha_p$ implies $\delta \ge 0$, so $i \in [K, K + \kappa]$. When $T = s$ and $h \le K\alpha_p + \nu_p - 1$, $\nu_p + v - h \ge 1 - K\alpha_p$ implies $\delta > -K$, hence $\delta \ge -K + 1$; therefore $i = K + \delta \in [1, K + \kappa]$, $k = s - i \le s - 1$, and $k \ge (K + \kappa + 1) - K - \kappa = 1$.

Moreover, for $E_0 = E_p^*$, we have $p \nmid E_p^*$ and every prime $p' \neq p$ dividing $q$ has $v_{p'}(E_p^*) = \max\bigl(\alpha_{p'},\, (\kappa + 1)\alpha_{p'} - \nu_{p'}\bigr)$, so for any delay $i \le K + \kappa$,
$$(K - i)\alpha_{p'} + \nu_{p'} + v_{p'}(E_p^*) \ge \max\bigl((K - i + 1)\alpha_{p'} + \nu_{p'},\; (K - i + \kappa + 1)\alpha_{p'}\bigr) \ge \max\bigl(\alpha_{p'},\, (K - i + 1)\alpha_{p'} + \nu_{p'}\bigr).$$

**Lemma 12 (Shift selection).** *There exist shifts $j_1, \dots, j_{s-1} \ge 0$, with $j_l \le J_0^*$ for all $1 \le l \le s - 1$, such that taking $j_s = 0$ makes the path integral up to step $s$ and satisfies $y_s \equiv \rho \pmod{q^K u_q}$.*

*Proof.* Initialize $j_1 = \dots = j_s = 0$. By Lemma 6, the path is integral up to step $K + 1$. If $s = K + 1$, then $m' = 1$, $K = 0$, $\kappa = 0$, $q^K u_q = 1$, and $\{1, \dots, s - 1\} = \varnothing$, so the result holds trivially. Assume $s \ge K + 2$.

*Stages $T = K + 1, \dots, s - 1$.* Assume inductively that the path is integral up to step $T$. Choose $\zeta_T \in \mathbb{Z}$ satisfying $2^{b_{T+1}} \zeta_T \equiv 1 \pmod q$. Process all primes $p \mid q$ and, for each, levels $h = 0, \dots, \alpha_p - 1$ in increasing order:
- *Automatic digits:* If $T \le K + \kappa$ and $h < e_T(p)$, then $b_1 = \dots = b_{T+1} = a$ (since $T + 1 \le K_0$). Lemma 6 gives $y_T \equiv c_* \pmod{p^{e_T(p)}}$, while $2^a \zeta_T \equiv 1 \equiv 2^a c_* \pmod q$ gives $c_* \equiv \zeta_T \pmod{p^{\alpha_p}}$. Since $h + 1 \le \min(\alpha_p, e_T(p))$, it follows that $y_T \equiv \zeta_T \pmod{p^{h+1}}$ with no shift change.
- *Steered digits:* Otherwise, let $(k, v)$ be the controller of $(T, p, h)$ with delay $i = T - k \in [K, K + \kappa]$. If $T \ge K + \kappa + 1$, then $k = T - i \ge 1$; if $T \le K + \kappa$, then $h \ge e_T(p) \ge (K + 1 - T)\alpha_p + \nu_p$, so writing $h = (K + 1 - T)\alpha_p + \nu_p + x_0$ with $x_0 \ge 0$ gives $v \equiv x_0 \pmod{\alpha_p}$, whence $v \le x_0$ and $k = 1 + (x_0 - v)/\alpha_p \ge 1$. Note also $k \le T \le s - 1$. Applying Lemma 11 at $(k, v)$ with $E_0 = E_p^*$ preserves integrality up to step $T$, preserves $y_T \bmod p^h$ and $y_T \bmod {p'}^{\alpha_{p'}}$ for every prime $p' \neq p$ dividing $q$ (preserving all previously matched digits of $y_T$, whether automatic or steered), and chooses $\beta \in \{0, \dots, p - 1\}$ so that $y_T \equiv \zeta_T \pmod{p^{h+1}}$.

At the end of Stage $T$, $y_T \equiv \zeta_T \pmod q$, making step $T + 1$ integral. When $\kappa = 0$, every steered digit at Stage $T$ uses the single index $k = T - K \in [1, s - 1 - K]$; if $j_k \ge q$, reducing $j_k$ modulo $q$ at the end of Stage $T$ alters $j_k$ by $\Delta > 0$ divisible by $q$, and Lemma 10 with $L = T$ and delay $i = K$ gives $\ell_{p'}(K) = v_{p'}(\Delta) \ge \alpha_{p'}$ for all $p' \mid q$, preserving integrality up to step $T$ and $y_T \equiv \zeta_T \pmod q$.

*Stage $T = s$.* The path is now integral up to step $s$ (with $j_s = 0$). Process Stage $T = s$ in increasing order of $k = 1, \dots, s - 1$; at each $k$, loop over all primes $p \mid q$ and $v = 0, \dots, \alpha_p - 1$ in increasing order whenever $h = (K + k - s)\alpha_p + \nu_p + v$ satisfies $0 \le h < K\alpha_p + \nu_p$. Notice that $(k, v)$ is the controller of $(s, p, h)$ with delay $i = s - k \in [1, K + \kappa]$, and for each fixed $p \mid q$, lexicographic order on $(k, v)$ visits $h = 0, \dots, K\alpha_p + \nu_p - 1$ in strictly increasing order. Applying Lemma 11 at $(k, v)$ with $E_0 = E_p^*$ preserves integrality up to step $s$, preserves $y_s \bmod p^h$, and for every prime $p' \neq p$ dividing $q$ preserves $y_s \bmod {p'}^{(K - i + 1)\alpha_{p'} + \nu_{p'}}$. Since every level $h_{p'}$ at prime $p'$ fixed at step $k$ or an earlier step $k'' < k$ satisfies $h_{p'} + 1 \le (K + k - s)\alpha_{p'} + \nu_{p'} + \alpha_{p'} = (K - i + 1)\alpha_{p'} + \nu_{p'}$, all previously fixed digits at every $p' \neq p$ are preserved. Choosing $\beta \in \{0, \dots, p - 1\}$ matches $y_s \equiv \rho \pmod{p^{h+1}}$.

When $\kappa = 0$, Stages $T < s$ only use $k \in [1, s - 1 - K]$ and Stage $T = s$ only uses $k \in [s - K, s - 1]$ (which is empty if $K = 0$). At the end of each step $k \in [s - K, s - 1]$, if $j_k \ge q$, reducing $j_k$ modulo $q$ changes $j_k$ by $\Delta > 0$ divisible by $q$, and Lemma 10 with $L = s$ and delay $i = s - k \ge 1$ gives $\ell_{p'}(s - k) = (K + k - s)\alpha_{p'} + v_{p'}(\Delta) \ge (K + k - s + 1)\alpha_{p'} \ge \alpha_{p'} \ge 0$ for all $p' \mid q$, preserving integrality up to step $s$ and all digits of $y_s$ fixed at steps $\le k$.

At completion, $y_s \equiv \rho \pmod{p^{K\alpha_p + \nu_p}}$ for all $p \mid q$, so $y_s \equiv \rho \pmod{q^K u_q}$. When $\kappa = 0$, the reductions modulo $q$ yield $j_l \le q - 1 = J_0^*$ for all $1 \le l \le s - 1$. When $\kappa \ge 1$, the map $(T, p, h) \mapsto (p, k, v)$ on all steered digits across $T = K + 1, \dots, s$ is injective: every such digit has $0 \le v < \alpha_p$ and $h = (K + k - T)\alpha_p + \nu_p + v$; for fixed $(p, k, v)$, at most one $T < s$ has $h \in [0, \alpha_p)$, and $T = s$ cannot share $(p, k, v)$ with an earlier $T < s$ because its level would be $h - (s - T)\alpha_p < 0$. Hence each $(p, v)$ contributes at most one term $\beta p^v E_p^*$ ($\beta \le p - 1$) to $j_l$, giving
$$j_l \le \sum_{p \mid q} \sum_{v=0}^{\alpha_p - 1} (p - 1) p^v E_p^* = \sum_{p \mid q} (p^{\alpha_p} - 1) E_p^* = J_0^* \qquad (1 \le l \le s - 1). \qquad \blacksquare$$

*Remark (separating primes without CRT).* What keeps the primes independent is the weight $E_p^*$, not a CRT step. A change of $\beta p^v E_p^*$ in one shift moves $y$ at $p$ by exactly one controlled digit (Lemma 11(3)). At every other prime $p' \mid q$ it moves $y$ only above all levels that are still in play, because $v_{p'}(E_p^*)$ is that large. Writing $j_l = \sum_{p} E_p^* \beta_l(p)$ with digits $\beta_l(p) < p^{\alpha_p}$ makes this a digit system. The Lean 4.35 proof (`GeneralAOp`, `GeneralAStage`, `GeneralASelect`) follows this scheme. It orders the work differently: it starts from all-zero digits (allowed by Lemma 6), extends integrality one stage at a time, and then fixes the digits of $y_s$; the digit of index $s$ is never touched, so $j_s = 0$ holds automatically.

**Lemma 13 (Tight wide step).** *With $j_1, \dots, j_{s-1}$ fixed as in Lemma 12, let $y_s(j)$ denote the value of $y_s$ when $j_s = j \ge 0$. For every $j \ge 0$, the path remains integral up to step $s$ and $y_s(j) \equiv \rho \pmod{m'}$. Moreover, there is a unique $j'_s \in \{0, \dots, \widetilde{W}(n) - 1\}$ such that for every $j \ge 0$ with $j \equiv j'_s \pmod{\widetilde{W}(n)}$, we have $y_s(j) \equiv \rho \pmod{\tilde{\Lambda}(n)}$, where $\tilde{\Lambda}(n) = q^K u_q \widetilde{W}(n) = \mathrm{lcm}(q^n m_q, q^K u_q)$.*

*Proof.* Because $d \mid P$, integrality at step $s$ is independent of $j_s$, so Lemma 9 gives $y_s(j) \equiv \rho \pmod{m'}$ for all $j \ge 0$. For any integers $0 \le j_2 < j_1$,
$$q\bigl(y_s(j_1) - y_s(j_2)\bigr) = 2^{b_s + j_2 P} y_{s-1} \bigl(2^{(j_1 - j_2) P} - 1\bigr).$$
Since $2^{b_s + j_2 P} y_{s-1} \equiv 1 \pmod q$, Lemma 4 yields
$$v_p\bigl(y_s(j_1) - y_s(j_2)\bigr) = K\alpha_p + \nu_p + v_p(j_1 - j_2) \qquad \text{for every } p \mid q.$$
Taking $j_2 = 0$ shows $y_s(j) \equiv y_s(0) \equiv \rho \pmod{q^K u_q}$ for all $j \ge 0$. If $0 \le j_2 < j_1 < \widetilde{W}(n)$ satisfied $y_s(j_1) \equiv y_s(j_2) \pmod{\tilde{\Lambda}(n)}$, then $v_p(j_1 - j_2) \ge v_p(\widetilde{W}(n))$ for all $p \mid q$, forcing $\widetilde{W}(n) \mid j_1 - j_2$, a contradiction. Since there are $\tilde{\Lambda}(n)/(q^K u_q) = \widetilde{W}(n)$ residue classes modulo $\tilde{\Lambda}(n)$ congruent to $\rho \pmod{q^K u_q}$, there is a unique $j'_s \in \{0, \dots, \widetilde{W}(n) - 1\}$ with $y_s(j'_s) \equiv \rho \pmod{\tilde{\Lambda}(n)}$. Finally, if $j \ge 0$ satisfies $j \equiv j'_s \pmod{\widetilde{W}(n)}$, then either $j = j'_s$ or $v_p(y_s(j) - y_s(j'_s)) \ge K\alpha_p + \nu_p + v_p(\widetilde{W}(n)) = v_p(\tilde{\Lambda}(n))$ for all $p \mid q$, so $y_s(j) \equiv \rho \pmod{\tilde{\Lambda}(n)}$. $\blacksquare$

#### Step 5. Completion and profinite density

Take the tail data $\sigma, n, \rho$ from Step 2 and $j_1, \dots, j_{s-1}, j'_s$ from Lemmas 12 and 13, and set $\Theta = \rho + q^n(B + 1) < q^n(B + M + 1)$. Since $y_l = (2^{a_l} y_{l-1} - 1)/q < 2^{a_l} y_{l-1}/q$ for $1 \le l \le s - 1$, $y_0 = 2^{\lambda_0} x$ with $\lambda_0 \le d q^K - 1$, $j_l \le J_0^*$, and $\sum_{l=1}^{s-1} b_l \le B_0(a)$, we have
$$y_{s-1} \le \frac{2^{dq^K - 1 + (s - 1)J_0^* P + B_0(a)}\, x}{q^{s - 1}}.$$

Let $k_0 \ge 0$ be the least integer such that $a_s = b_s + \bigl(j'_s + k_0 \widetilde{W}(n)\bigr)P$ satisfies $2^{a_s} y_{s-1} \ge q\Theta + 1$, and set $j_s^* = j'_s + k_0 \widetilde{W}(n) \equiv j'_s \pmod{\widetilde{W}(n)}$. By Lemma 13, $y_s = y_s(j_s^*)$ is integral, $y_s \equiv \rho \pmod{m'}$, and $y_s \equiv \rho \pmod{\tilde{\Lambda}(n)}$, hence $y_s \equiv \rho \pmod{q^n m_q}$ (as $q^n m_q \mid \tilde{\Lambda}(n)$). Since $\gcd(q^n m_q, m') = 1$, we obtain $y_s \equiv \rho \pmod{q^n m_q m'}$. Moreover,
$$y_s = \frac{2^{a_s} y_{s-1} - 1}{q} \ge \Theta = \rho + q^n(B + 1).$$
Lemma 8 therefore produces $w \in \mathbb{N}$ with $w > B$, $w \equiv r \pmod m$, $w \to y_s \to \dots \to y_0 \to x$, and
$$w \le \frac{2^\alpha}{q^n}\, y_s < \frac{2^{\alpha + a_s} y_{s-1}}{q^{n + 1}}.$$

- **If $k_0 = 0$:** Since $b_s \le P$ and $j'_s \le \widetilde{W}(n) - 1$, we have $a_s = b_s + j'_s P \le \widetilde{W}(n) P = \widetilde{Q}(n)$, so
  $$w < \frac{2^{\alpha + \widetilde{Q}(n)} y_{s-1}}{q^{n+1}} \le \frac{2^{\alpha + \widetilde{Q}(n) + dq^K - 1 + (s - 1)J_0^* P + B_0(a)}\, x}{q^{n + s}}.$$
- **If $k_0 \ge 1$:** Here $a_s - \widetilde{Q}(n) = b_s + \bigl(j'_s + (k_0 - 1)\widetilde{W}(n)\bigr)P \ge b_s \ge 1$, so $2^{a_s - \widetilde{Q}(n)} y_{s-1}$ is an integer. By minimality of $k_0$, $2^{a_s - \widetilde{Q}(n)} y_{s-1} < q\Theta + 1$, hence $2^{a_s - \widetilde{Q}(n)} y_{s-1} \le q\Theta$ and $2^{a_s} y_{s-1} \le 2^{\widetilde{Q}(n)} q\Theta$. Consequently,
  $$w < \frac{2^{\alpha + \widetilde{Q}(n)} q\Theta}{q^{n+1}} = \frac{2^{\alpha + \widetilde{Q}(n)} \Theta}{q^n} < 2^{\alpha + \widetilde{Q}(n)}(B + M + 1).$$

Combining both cases proves the bounds in Theorem A. $\blacksquare$

---

### 5. Proof of Theorem B

Assume $q > 1$ is odd, $t \ge 1$, and no $x \in R_q(t)$ satisfies Hypothesis (H). By Proposition 1, either $t \bmod N_q \notin V_q$ (equivalently $t \bmod q \notin H_q$, since $H_q \subseteq (\mathbb{Z}/q\mathbb{Z})^\times$ and $\gcd(t, N_q) = 1 \iff \gcd(t, q) = 1$), or $t \bmod N_q \in V_q$ has no directed path of length $\kappa$ in $\mathcal{G}_q$.

(1) Suppose $R_q(t)$ contains a backward chain of $m \ge 1$ odd steps $w_1, \dots, w_m \ge 1$, with $qw_1 + 1 = 2^{k_1} t$ ($k_1 \ge 0$) and $qw_{l+1} + 1 = 2^{k_{l+1}} w_l$ ($k_{l+1} \ge 1$, $1 \le l < m$). Then $2^{k_1} t \equiv 1 \pmod q$ implies $\gcd(t, q) = 1$ (so $\gcd(t, N_q) = 1$) and $t \bmod q \in H_q$, hence $t \bmod N_q \in V_q$; as in Proposition 1, $w_1 \equiv c_0(t \bmod N_q) \pmod{u_q}$ (whether $k_1 = 0$ or $k_1 \ge 1$). When $m \ge 2$, for each $1 \le l \le m - 1$, $2^{k_{l+1}} w_l \equiv 1 \pmod q$ similarly implies $w_l \bmod N_q \in V_q$ and $w_{l+1} \equiv c_0(w_l \bmod N_q) \pmod{u_q}$. Thus $(t \bmod N_q) \to (w_1 \bmod N_q) \to \dots \to (w_{m-1} \bmod N_q)$ is a directed path of length $m - 1$ in $\mathcal{G}_q$. Because $t \bmod N_q$ has no path of length $\kappa$ in $\mathcal{G}_q$ (in particular, when $\kappa = 0$, $t \bmod N_q \notin V_q$), we must have $m - 1 \le \kappa - 1$, so $m \le \kappa$. When $g_0 = 1$, $\kappa = 0$, forcing $m \le 0$, so no chain of length $m \ge 1$ exists.

(2) Let $n \ge 1$. For $0 \le r \le \kappa$, let $O_0 = \{t\}$ and, for $r \ge 1$, let $O_r \subseteq R_q(t)$ consist of all odd integers $w_r \ge 1$ appearing at the end of a backward chain $w_1, \dots, w_r$ of $r$ odd steps in $R_q(t)$. Clearly $|O_0 \bmod 2^n| = 1$. For $r \ge 1$, each $w \in O_r$ satisfies $w = (2^j w' - 1)/q$ for some $w' \in O_{r-1}$ and $j \ge 0$. Modulo $2^n$, $q$ is odd and hence invertible; every $j \ge n$ gives $2^j w' \equiv 0 \pmod{2^n}$ and thus the single residue $-q^{-1} \bmod 2^n$ independently of $w'$, while $0 \le j \le n - 1$ gives at most $n |O_{r-1} \bmod 2^n|$ residues. Hence
$$|O_r \bmod 2^n| \le n\, |O_{r-1} \bmod 2^n| + 1,$$
which by induction gives $|O_r \bmod 2^n| \le (n + 1)^r$ for $0 \le r \le \kappa$ (since $n(n + 1)^{r-1} + 1 \le (n + 1)^r$).

Every $x \in R_q(t)$ satisfies $x \ge 1$ (since $\mathrm{Col}_q^N(0) = 0 \neq t$) and $\mathrm{Col}_q^N(x) = t$ for some $N \ge 0$. If no odd step occurs among $x, \mathrm{Col}_q(x), \dots, \mathrm{Col}_q^{N-1}(x)$, then $x = 2^N t$ with $t \in O_0$; otherwise, letting $w_m, \dots, w_1$ ($m \ge 1$) be the odd integers from which an odd step is taken along $x, \mathrm{Col}_q(x), \dots, \mathrm{Col}_q^{N-1}(x)$, we have $x = 2^k w_m$ ($k \ge 0$), $qw_{l+1} + 1 = 2^{k_{l+1}} w_l$ ($k_{l+1} \ge 1$, $1 \le l < m$), and $qw_1 + 1 = 2^{k_1} t$ ($k_1 \ge 0$), so $w_1, \dots, w_m$ is a backward chain of $m$ odd steps in $R_q(t)$. By (1), $m \le \kappa$, so $w_m \in \bigcup_{r=0}^\kappa O_r$. Thus every $x \in R_q(t)$ has the form $x = 2^k w$ with $w \in \bigcup_{r=0}^\kappa O_r$ and $k \ge 0$. Modulo $2^n$, all terms with $k \ge n$ collapse to $0$, while $0 \le k \le n - 1$ yields at most $n$ multiples per residue class in $\bigcup_{r=0}^\kappa O_r \bmod 2^n$. Hence
$$|R_q(t) \bmod 2^n| \le n \left|\bigcup_{r=0}^\kappa O_r \bmod 2^n\right| + 1 \le n \sum_{r=0}^\kappa (n + 1)^r + 1 = (n + 1)^{\kappa + 1}.$$


(3) Suppose some $x_0 \in R_q(t)$ is periodic under $\mathrm{Col}_q$, so $\mathrm{Col}_q^L(x_0) = x_0$ for some $L \ge 1$. Since $x_0 \in R_q(t)$, $\mathrm{Col}_q^N(x_0) = t$ for some $N \ge 0$; thus
$$\mathrm{Col}_q^L(t) = \mathrm{Col}_q^L(\mathrm{Col}_q^N(x_0)) = \mathrm{Col}_q^N(\mathrm{Col}_q^L(x_0)) = \mathrm{Col}_q^N(x_0) = t,$$
so $t$ lies on a cycle $t = \xi_0 \to \xi_1 \to \dots \to \xi_L = t$ with $\xi_{j+1} = \mathrm{Col}_q(\xi_j)$. Because $t \ge 1$ and $t/2^L < t$, the cycle contains at least one odd element. Let $0 \le j_1 < \dots < j_r < L$ ($r \ge 1$) be all indices with $\xi_{j_i}$ odd. Then $q \xi_{j_r} + 1 = 2^{k_1} t$ with $k_1 = L - 1 - j_r \ge 0$, $q \xi_{j_i} + 1 = 2^{j_{i+1} - j_i - 1} \xi_{j_{i+1}}$ ($1 \le i < r$) with $j_{i+1} - j_i - 1 \ge 1$ (since $q \xi_{j_i} + 1$ is even and $\xi_{j_{i+1}}$ is odd), and since $t = \xi_0 = 2^{j_1} \xi_{j_1}$, $q \xi_{j_r} + 1 = 2^{k_1 + j_1} \xi_{j_1}$ with $k_1 + j_1 \ge 1$ (since $q \xi_{j_r} + 1$ is even and $\xi_{j_1}$ is odd). Repeating $(\xi_{j_r}, \xi_{j_{r-1}}, \dots, \xi_{j_1})$ any number $R \ge 1$ of times produces a backward chain $w_1, \dots, w_{Rr}$ of $Rr$ odd steps in $R_q(t)$ (with $w_1 = \xi_{j_r}, \dots, w_r = \xi_{j_1}$, and $w_{l+r} = w_l$), contradicting (1) once $Rr > \kappa$.

For $X \ge 2$, as shown in (2), every $y \in R_q(t) \cap [1, X]$ has the form $y = 2^k w_m$ for some $0 \le m \le \kappa$, $k \ge 0$, and odd integers $w_1, \dots, w_m \ge 1$ defined from $w_0 = t$ by $q w_l + 1 = 2^{j_l} w_{l-1}$ ($1 \le l \le m$) with $j_1 \ge 0$ and $j_2, \dots, j_m \ge 1$. For $l = 1$: if $j_1 = 0$, then $w_1 \ge 1 > \frac{1}{2q} 2^0$; if $j_1 \ge 1$, then $t \ge 1$ gives $q w_1 = 2^{j_1} t - 1 \ge 2^{j_1} - 1 \ge \frac{1}{2} 2^{j_1}$, so $w_1 \ge \frac{1}{2q} 2^{j_1}$. For each $2 \le l \le m$, $j_l \ge 1$ and $w_{l-1} \ge 1$ give $2^{j_l} w_{l-1} \ge 2$, so $q w_l = 2^{j_l} w_{l-1} - 1 \ge \frac{1}{2} 2^{j_l} w_{l-1}$ and $w_l \ge \frac{1}{2q} 2^{j_l} w_{l-1}$. By induction, $w_m \ge (2q)^{-m} 2^{j_1 + \dots + j_m} \ge (2q)^{-\kappa} 2^{j_1 + \dots + j_m}$ (which also holds for $m = 0$ since $w_0 = t \ge 1$). Therefore $2^k w_m \le X$ implies
$$k + j_1 + \dots + j_m \le \lfloor \log_2 X + \kappa \log_2(2q) \rfloor =: N_X.$$
Since $(m, k, j_1, \dots, j_m)$ uniquely determines $y$ and $N_X \ge 1$ for $X \ge 2$, counting nonnegative integer tuples $(k, j_1, \dots, j_m) \in \mathbb{N}^{m+1}$ with $k + j_1 + \dots + j_m \le N_X$ gives
$$|R_q(t) \cap [1, X]| \le \sum_{m=0}^\kappa \binom{N_X + m + 1}{m + 1} \le (\kappa + 1)(N_X + \kappa + 1)^{\kappa + 1} = O_q\bigl((\log X)^{\kappa + 1}\bigr)$$
uniformly in $t \ge 1$. $\blacksquare$

---

### 6. From finite moduli to $\widehat{\mathbb{Z}}$ (not machine-checked)

Let $\pi_m : \widehat{\mathbb{Z}} \to \mathbb{Z}/m\mathbb{Z}$ be the projections. For $X \subseteq \mathbb{N}$ write $\overline{X}$ for the closure of its diagonal image.

1. **Density.** If $X$ meets every residue class modulo every $m \ge 1$, then $\overline{X} = \widehat{\mathbb{Z}}$, because the cylinders $\pi_m^{-1}(r)$ form a basis of nonempty open sets. Theorem A gives this for $X = R_q(t)$, already with $w > B$. Hence $\mu(\overline{R_q(t)}) = 1$.
2. **Null sets.** For every $n$, $\pi_{2^n}^{-1}(X \bmod 2^n)$ is closed and contains $X$. Also $(\pi_{2^n})_*\mu$ is uniform, since it is a translation-invariant probability on a finite group. So $\mu(\overline{X}) \le |X \bmod 2^n|/2^n$. Theorem B(2) gives $\mu(\overline{R_q(t)}) \le (n+1)^{\kappa+1}/2^n \to 0$, hence $\mu(\overline{R_q(t)}) = 0$ and $\overline{R_q(t)} \neq \widehat{\mathbb{Z}}$.
3. **Dichotomy.** "Some $x \in R_q(t)$ satisfies (H)" and "no $x \in R_q(t)$ satisfies (H)" are negations of each other, so 1 and 2 give $\mu(\overline{R_q(t)}) \in \{0, 1\}$ for every odd $q > 1$ and $t \ge 1$.

**Lean 4.35 correspondence.**

| Paper | Lean 4.35 (`QX+1/Collatz/`) |
|---|---|
| Proposition 1 | `Prop1`, `general_prop1` (GeneralDefs, GeneralLift) |
| (3) ⇒ (1) via $D_m$ | `Dm`, `glift_step`, `lift_chain`, `prop1_three_to_one` (GeneralLift) |
| Theorem A (integer content, both bounds) | `TheoremA`, `general_theorem_A` (GeneralTheoremA, GeneralTheoremAProof) |
| Lemma 12 | `shift_select` (GeneralASelect) |
| Theorem B (1), (2) count bound, (3) | `TheoremB`, `general_theorem_B` (GeneralDefs, GeneralTheoremB) |
| $\kappa = \max_p \lceil \nu_p/\alpha_p \rceil$ | `nu_le_kappa`, `kappa_le_of_nu_le` (GeneralAStage) |
| §6 (Haar measure, closure, 0–1 law) | not formalized (no measure theory in Lean 4.35 core) |
