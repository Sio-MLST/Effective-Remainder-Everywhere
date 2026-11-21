# Supplements to `paper.md`

Results that sit next to the main paper: sharper bounds for special moduli, corollaries, a worked example and open questions.

**Status.** Nothing in this file is formalized in Lean 4.35, and nothing here is needed for `paper.md`. Proposition S1 and the results of §§2 and 4 are proved in full. Statements S2 to S6 are given with the idea of the proof only; complete proofs remain to be written. Unless stated otherwise the statements are for $\kappa = 0$, that is $u_q = 1$, $N_q = q$, $V_q = H_q$, where the criterion of Proposition 1 reads $t \bmod q \in \langle 2 \rangle$. Extending each to $\kappa \ge 1$ is listed in §5.

Notation is that of `paper.md`: $d = \mathrm{ord}_q(2)$, $2^d = 1 + qu$, $m = 2^\alpha m_q m'$ as in its §3, and $L$ with $q \le 2^L$.

---

## 1. Sharper bounds for special moduli ($\kappa = 0$)

Throughout, $t \ge 1$ with $t \bmod q \in \langle 2 \rangle$, $m \ge 1$, and $r, B \in \mathbb{N}$.

### 1.1 Moduli all of whose prime factors divide $q$: a single exponential

**Proposition S1.** *If every prime factor of $m$ divides $q$, there is $w \equiv r \pmod m$ with $B < w \le (B+1)\, t\, 2^{d(m+1)}$ and $w \to t$.*

*Proof.* Pick $b \in \{0, \dots, d-1\}$ with $2^b t \equiv 1 \pmod q$, and put $R_k = (2^{b + dk} t - 1)/q$ for $k \ge 1$. Each $R_k$ is a positive odd integer with $R_k \to t$ (this is Lemma 2(1) of the paper with $y = t$). For $h \ge 1$,
$$R_{k+h} - R_k = 2^{b+dk}\, t\, \frac{2^{dh} - 1}{q},$$
and $2^{b+dk} t$ is prime to $m$. For a prime $p \mid q$, lifting the exponent (Lemma 1(2)) gives $v_p(2^{dh} - 1) = \alpha_p + v_p(h)$ since $\nu_p = 0$. Hence $R_{k+h} \equiv R_k \pmod m$ iff $qm \mid 2^{dh} - 1$ iff $m \mid h$. So $R_1, \dots, R_m$ meet every class modulo $m$, and $R_k \equiv r$ exactly when $k \equiv k_r \pmod m$.

Let $k$ be least with $k \equiv k_r \pmod m$ and $R_k > B$, and $w = R_k$. If $k = k_r \le m$, then $w < 2^{b + dm} t/q < t\, 2^{d(m+1)}$. Otherwise $R_{k-m} \le B$ and $qw + 1 = 2^{dm}(qR_{k-m} + 1) \le 2^{dm}(qB + 1)$, so $w < 2^{dm}(B+1)$. $\square$

*Instances.* $q = 5$ ($d = 4$), $m = 5^a$: $(B+1)\,t\,16^{m+1}$. $q = 3$ ($d = 2$), $m = 3^a$: $(B+1)\,t\,4^{m+1}$.

### 1.2 Moduli $m = 2^\alpha m_q$ (no other odd primes): polynomial exponent

**Proposition S2.** *If $m = 2^\alpha m_q \ge 2$, some $w \equiv r \pmod m$ with*
$$B < w < (B+1)\, t\, 2^{\,d\, m^{\log_2 q} + \alpha + d + 1}$$
*reaches $t$.*

The exponent is polynomial in $m$ of degree $\log_2 q$. For $\alpha = 0$ and $q$ a prime power it is linear, but S1 is sharper there. The superlinear factor for $\alpha > 0$ comes from the prefix of at most $\alpha$ odd steps that fixes $r \bmod 2^\alpha$: each odd step costs a factor $q$ of precision. The one-odd-step witnesses of S1 cannot help, since for large $k$ they all lie in the single class $-q^{-1} \bmod 2^\alpha$. This is a limit of this method, not a lower bound.

### 1.3 Fewer odd steps for other moduli

The double exponential in the general bound is paid for odd steps in the word that moves between classes modulo $m'$. Writing a word by the positions of its ones makes the cost explicit.

**Lemma S3** *Let $H = \langle 2 \rangle \subseteq (\mathbb{Z}/m')^\times$, $e = \mathrm{ord}_{m'}(2)$. A word of length $\ell$ with ones at positions $C_1 > \dots > C_s \ge 1$ (counted from the end) acts on $\mathbb{Z}/m'$ by*
$$S_\omega(z) = q^s 2^{-\ell} z + \sum_{k=1}^{s} q^{s-k} 2^{-C_k},$$
*and for all $h_0, \dots, h_s \in H$ some word with exactly $s$ ones and length at most $(s+1)e - 1$ acts as $z \mapsto q^s h_0 z + \sum_k q^{s-k} h_k$.*

So $s$ odd steps reach $y$ from $z$ iff $y - q^s h_0 z \in H + qH + \dots + q^{s-1}H$ for some $h_0 \in H$, and the question is how small $s$ can be for this sumset to cover $\mathbb{Z}/m'$. `paper.md`, Lemma 3 (Chowla) gives $s \le 1 + \lceil (m' - e)/\varphi(e) \rceil$ for every $m'$. Two families do much better.

**Proposition S4.** *If $m' = p^r$ with $2$ a primitive root modulo $p^r$ and $\gcd(m', q) = 1$, two odd steps suffice: for all $z, y$ some word with exactly two ones and length at most $3\varphi(m') - 1$ sends $z$ to $y$. The witness bound becomes $(B+1)\,t\,2^{2q^3 m^{L+1}}$.*

(Idea: with $c = y - q^2 z$ choose a unit $h_2$ with $c - h_2$ also a unit, which needs only $p \ge 3$.)

**Proposition S5.** *Let $\lambda \ge 1$ be least with $q^\lambda \in H$ (the order of $q$ in $(\mathbb{Z}/m')^\times / H$), $s_0 = \lceil \log_2 (m' + 1) \rceil$ and $n = \lambda s_0$. Then $n$ odd steps suffice, and the witness bound is*
$$(B+1)\,t\,2^{\,2 q^{2\lambda + 1} m^{(\lambda+1)L + 1}}.$$
*For $q \in \langle 2 \rangle \bmod m'$, $\lambda = 1$.*

(Idea: write each residue in binary, split powers of $2$ using $2^j = 2^{j-1} + 2^{j-1}$ until each has exactly $s_0$ terms, and absorb $q^{-\lambda u}$ using $q^\lambda \in H$.)

### 1.4 Table of exponents of $2$

| moduli $m$ | exponent | source |
| --- | --- | --- |
| odd $m$, all prime factors divide $q$ | $d(m+1)$ | S1 |
| $m = 2^\alpha m_q$ | $d\, m^{\log_2 q} + \alpha + d + 1$ | S2 |
| $m' = p^r$, $2$ a primitive root | $2 q^3 m^{L+1}$ | S4 |
| $q^\lambda \in \langle 2 \rangle \bmod m'$ | $2 q^{2\lambda+1} m^{(\lambda+1)L+1}$ | S5 |
| all $m$ | the bound of Theorem A in `paper.md` | Theorem A |

### 1.5 Number of steps

**Proposition S6.** *In the construction behind these bounds (a parity word followed by halvings), the witness $w$ satisfies $\mathrm{Col}_q^N(w) = t$ with exactly $s$ odd steps, $s \le \log_2 m + s_* + 1$ where $s_* = \lfloor (m'-1)/\varphi(e) \rfloor + 1$, and $N \le 2 m^{L+1} q^{s_*+1} + (L+1)s + \log_2 (B+2)$.* $N$ bounds the first time the orbit of $w$ reaches $t$; it need not equal it.

For `paper.md` the corresponding statement would use $s = K + \kappa + \gamma + 2$ from its §3. That has not been written down.

---

## 2. Corollaries of Theorem A

**No congruence obstruction.** A set defined by a finite Boolean combination of congruences is a union of classes modulo the lcm of the moduli, so if it is nonempty it contains a predecessor of $t$, whenever $t$ satisfies the hypothesis of Theorem A.

**Infinitude.** Reapplying Theorem A with $B$ replaced by a predecessor already found gives infinitely many predecessors in every class.

**Sufficient sets** (in the sense of Monks). Call $S \subseteq \mathbb{N}_{\ge 1}$ sufficient for $\mathrm{Col}_q$ if the orbit of every positive integer meets the orbit of an element of $S$. Let $x \ge 1$ and let $y$ be the odd number reached by halving $x$. Then $t = qy + 1 \equiv 1 \pmod q$ lies in the orbit of $x$ and $t \bmod q \in H_q$. If $\kappa = 0$, Theorem A applies to $t$, so every arithmetic progression $a + b\mathbb{N}$ is sufficient, with $w$ bounded as in Theorem A. For $\kappa \ge 1$ the same holds for every $x$ whose orbit meets a target satisfying the criterion of Proposition 1; whether that is every $x$ is open (§5).

**Cycles.** Every element $t$ of a cycle of $\mathrm{Col}_q$ satisfies $t \bmod q \in H_q$: going backward around the cycle from $t$, the first odd element $x$ satisfies $qx + 1 = 2^k t$. So for $\kappa = 0$ the predecessors of every cycle element meet every class modulo every $m$. For $\kappa \ge 1$ this needs the criterion of Proposition 1 at the cycle element.

---

## 3. Worked example: size of the bound versus the least witness

$q = 5$ ($d = 4$, $L = 3$), $t = 7$ (admissible, $7 \equiv 2 \pmod 5$), with $11 \to 56 \to 28 \to 14 \to 7$.

* $m = 11$, $r = 0$, $B = 0$: the least witness is $11$. The general bound $t\, 2^{2 m^{L+1} q^m}$ (stated here without proof) gives $t\, 2^{2 \cdot 11^4 \cdot 5^4}$, which has about $5.5$ million digits.
* $m = 10$, $r = 1$, $B = 0$: the least witness is again $11$ (the only smaller candidate, $1$, lies on a cycle not containing $7$). Here S2 gives $w < 7 \cdot 2^{4 \cdot 10^{\log_2 5} + 6} \approx 2.22 \cdot 10^{255}$.

The bounds describe the witness the construction produces, not the least one, and their size is driven by the odd prime factors of $m$ not dividing $q$.

*Heuristic observation (unproved).* For $5x+1$, $t = 1$, a truncated inverse search of the backward tree finds predecessors in every class modulo $2^\alpha$ ($\alpha \le 8$) and modulo $5^a$ ($a \le 4$), all below $2^{22}$, whereas S1 gives about $2^{2500}$ for $m = 625$. Because the search discards values above a cap, the numbers found are only upper bounds for least witnesses, and a class not found is no evidence of absence.

---

## 4. Explicit trapped classes

A concrete certificate form of the finite-depth trap. Let $g > 1$ divide $q$ with $\mathrm{ord}_{qg}(2) = d = \mathrm{ord}_q(2)$ (equivalently $qg \mid 2^d - 1$). Put
$$T = \{x : x \equiv 2^i \pmod{qg} \text{ for some } i \ge 0\} \cup \{x : g \mid x\}.$$
**If $t \in T$, then every $x$ reaching $t$ lies in $T$.**

*Proof.* It suffices to show $\mathrm{Col}_q(x) \in T \Rightarrow x \in T$. For even $x$ this is clear. For odd $x$, $qx + 1 \equiv 1 \pmod g$, so $g \nmid qx + 1$, hence $qx + 1 \equiv 2^i \pmod{qg}$. Reducing modulo $q$ gives $d \mid i$, so $2^i \equiv 1 \pmod{qg}$ and $g \mid x$. $\square$

*Example.* $q = 21$, $g = 3$, $d = 6$: $T$ consists of the classes $1, 2, 4, 8, 16, 32$ and the multiples of $3$ modulo $63$. The class of $5$ modulo $63$ is outside $T$, so no $x \equiv 5 \pmod{63}$ reaches $1$ under $21x + 1$. Consistently, $t = 1$ is not among the qualifying targets listed for $q = 21$ in `README.md`.

The theorem of `paper.md` (Theorem B) is stronger: it bounds the odd depth of every chain by $\kappa$ and gives Haar measure zero. The sets $T$ give the same conclusion as an explicit union of residue classes, closed under taking predecessors, which is useful as a short certificate.

---

## 5. Open questions

1. Is the exponent linear in $m$ for powers of $2$ and for mixed moduli $2^\alpha m_q$?
2. Does every modulus admit a single exponential? This follows from the construction behind S2 to S5 if the connecting word can always be taken with $O(\log m')$ odd steps. Known: S4 and S5 for two families, and the Chowla bound of `paper.md`, Lemma 3, in general.
3. For $\kappa \ge 1$: does every cycle element satisfy the criterion of Proposition 1? Is every positive integer's orbit eventually met by a target satisfying it (needed for sufficiency, §2)?
4. Compare the bound of Theorem A in `paper.md` ($E^*$, $E^{**}$) numerically with S1 to S5 for small $(q, m)$, and restate S1 to S6 for $\kappa \ge 1$ using $u_q$, $\kappa$ and $D_m$.
5. Formalize S1 to S6 in Lean 4.35 as additional modules, after (4).

