# Reaching Every Residue: Backward Trees of qx + 1 Maps with Non-Wieferich Multiplier

## Abstract

Let $q>1$ be odd with $\gcd\bigl(q,(2^{\operatorname{ord}_q(2)}-1)/q\bigr)=1$, that is, not a Wieferich number in the sense of Franco and Pomerance, and let $\operatorname{Col}_q$ halve even numbers and send odd $x$ to $qx+1$. Let $t\ge1$ be congruent modulo $q$ to a power of $2$. We prove that for every modulus $m$, residue $r$ and threshold $B$ some $w\equiv r\pmod m$ with $w>B$ reaches $t$, with an explicit bound on the least such $w$ and on the number of steps from $w$ to $t$ (Theorem A, Corollary 6.14). So the predecessors of $t$ meet every residue class modulo every $m$, effectively; equivalently, they are dense in the profinite integers. The hypothesis on $q$ cannot be dropped: for odd $q$, the predecessors of $1$ meet every residue class modulo every $m$ if and only if $q$ is not a Wieferich number, and for a Wieferich number they stay inside a proper union of residue classes that is closed under taking predecessors. For $5x+1$, whose known cycles through $1$, $13$ and $17$ have pairwise disjoint backward trees, each of the three trees meets every residue class. Theorems A and B are also verified in Lean v4.35.0. The paper makes no claim about the Collatz conjecture.

*Keywords:* Collatz problem; $3x+1$ problem; $qx+1$ maps; generalized Collatz maps; backward tree; predecessor set; residue classes; profinite integers; Wieferich numbers; Crandall numbers; Lean 4; formal verification.

## 1. Introduction

For an integer $q>1$ define $\operatorname{Col}_q:\mathbb N\to\mathbb N$ by

$$\operatorname{Col}_q(x)=\begin{cases} x/2 & x \text{ even},\\ qx+1 & x \text{ odd}.\end{cases}$$

Here $\mathbb N=\{0,1,2,\dots\}$; since $\operatorname{Col}_q$ maps positive integers to positive integers, and all statements below concern positive integers, they may be read over the positive integers. We say $x$ *reaches* $y$, written $x\to y$, if $\operatorname{Col}_q^{k}(x)=y$ for some $k\ge 0$. For a *target* $t$, the set of $x$ reaching $t$ is the *predecessor set* of $t$ [Wir98]; we sometimes call it the backward tree of $t$, rooted at $t$, which Applegate and Lagarias call the tree of preimages [AL95b]. An element of it with prescribed properties is a *witness*, as in Theorem A. Throughout, $q$ is not assumed prime; the letter $p$ is reserved for primes.

**Notation.** The multiplier is called $q$ as in Crandall, Steiner and Franco–Pomerance [Cra78, Ste81, FP95]. The map $\operatorname{Col}_q$ is the unaccelerated map, written $C$ by Lagarias and $\operatorname{Col}$ by Tao [Lag85, Tao22]; we follow Tao. Much of the literature instead uses the accelerated map $T_q$ (written $T$ by Lagarias), which sends odd $x$ to $(qx+1)/2$ and whose orbits omit the value $qx+1$ after each odd $x$, or the odd-to-odd map $C_q$ of Crandall and Franco–Pomerance, which sends odd $x$ to the largest odd divisor of $qx+1$. The maps $S_0(x)=x/2$ and $S_1(x)=(qx+1)/2$ of §6 are the two branches of $T_q$, which acts as $S_0$ on even $x$ and as $S_1$ on odd $x$. In the $3x+1$ literature the same objects appear under other names: an element of the predecessor set of $t$ is the end of a *back-tracing path* from $t$ in the sense of Wirsching and Monks [Wir98, Mon06], or a node of the *$3x+1$ graph* from which $t$ is reachable [MMMM13]; and $w$ and $t$ *merge* [Mon06] when their orbits meet, which is weaker than $w\to t$. We work with the unaccelerated map because the statements concern it: predecessor sets are closed under doubling, the targets in Theorem A may be even, and the residue classes of even numbers are included.

Many results on predecessor sets concern counting: how many $y\le x$ reach $1$ [AL95, KL03], or what proportion of orbits behave well [Tao22]. Here we ask which residue classes a predecessor set meets. Density results and coverage results are logically independent: a set of positive density can miss entire residue classes, and a set meeting every class can have density zero. The nearest density statement for $3x+1$ is in an unrefereed manuscript of Mazur [Maz26]: the predecessor set of every $t$ with $3\nmid t$ has positive lower natural density, while for $3\mid t$ it consists of the numbers $2^kt$, as in Proposition 3.1. Whether these sets have positive density within each residue class is not addressed there.

For $3x+1$ the coverage question is essentially settled in the literature. Monks [Mon06] proved that every arithmetic progression is *sufficient*: every orbit merges with the orbit of some element of it. His theorem completed a line of partial results on particular progressions, reported to include Cadogan [Cad84] (the class $1$ modulo $4$), Korec and Znám [KZ87] (classes $a$ modulo $p^n$ with $p\nmid a$, for odd primes $p$ such that $2$ is a primitive root modulo $p^2$) and Andaloro [And00] (the class $1$ modulo $16$). His theorems are stated in terms of merging, but his construction (Lemmas 3.2, 3.6 and 3.8 of [Mon06], with Lemmas 3.4, 3.5 and 3.7) back-traces from an arbitrary $x$ with $3\nmid x$, and so produces predecessors of $x$ in every residue class modulo every $m$; nothing in it is specific to the target $1$ [REF-CHECK]. Monks, Monks, Monks and Monks [MMMM13] state this explicitly: by [MMMM13, Theorem 4.1], for $3x+1$ every $x$ not divisible by $3$ back-traces to a given class modulo $d=2^n3^kb$ with $\gcd(b,6)=1$ along a path with at most $2(b-1)f+n+1$ odd steps, where $f$ is the order of $3/2$ modulo $b$ [REF-CHECK]. (In the proof of their Lemma 4.3 they refer to "[8, Lemma 2.8]"; [Mon06] has no Lemma 2.8, and the construction meant is that of its §3 [REF-CHECK].) This bounds the number of odd steps, not the total number of steps or the size of the integer reached: the number of halvings in their paths is controlled only modulo a power of $3$ that grows with the number of odd steps. Their Lemma 4.3 is the analogue of our Lemma 6.3. Theorem A bounds the witness itself, and Corollary 6.14 bounds both the number of odd steps and the total number of steps. Theorem A extends the coverage statement to every odd multiplier that is not a Wieferich number, where the role of $2$ being a primitive root modulo $3^k$ is taken by Lemma 6.5. Corollary 3.2 extends Monks's sufficiency theorem to the same multipliers. The question matters because a residue class containing no number that reaches $1$ proves at once that $\operatorname{Col}_q$ has orbits avoiding $1$. By Theorem B and Proposition 5.2 such a class exists for every Wieferich number (defined in §2). Theorem A shows that no such class exists when $q$ is odd and not a Wieferich number, in particular for $q=3$ and $q=5$.

**Theorem A (coverage).** *Let $q>1$, and suppose $2^d=1+qu$ for some $d,u\in\mathbb N$ with $\gcd(q,u)=1$. Let $q\le 2^L$, and let $t\ge 1$ satisfy $t\equiv 2^i\pmod q$ for some $i\ge 0$. Let $m\ge1$, let $m'$ be the largest divisor of $m$ prime to $2q$, let $e=\operatorname{ord}_{m'}(2)$, and put*

$$s_*=\Bigl\lfloor\frac{m'-1}{\varphi(e)}\Bigr\rfloor+1 .$$

*Then for all $r,B\in\mathbb N$ there is a $w$ with*

$$w\to t,\qquad w\equiv r \pmod m,\qquad B<w\le (B+1)\,t\,2^{\,2m^{L+1}q^{s_*+1}}.$$

Since $\varphi(e)\ge1$, always $s_*\le m'$; since $2^e>m'$, the order $e$ grows with $m'$, and typically $s_*$ is much smaller than $m'$. The proof first gives a simpler bound, with $q^{m}$ in place of $q^{s_*+1}$ (§6.9). Both bounds are proved, so the witness satisfies the smaller of the two. The bound of Theorem A is the smaller one except exactly when $m=1$, or $m=3$ with $3\nmid q$: indeed $s_*+1>m$ forces $s_*\ge m\ge m'$, and as $s_*\le m'$ this means $m=m'$ and $s_*=m'$, which for $m'>1$ requires $\varphi(e)=1$, i.e. $e=2$ and $m'=3$. The consequences in §§3–4 are derived from the simpler bound with $q^m$; for $m=1$, and for $m=3$ when $3\nmid q$, they genuinely need it (see the proofs of Corollaries 1.1 and 4.2).

Such a $w$ is a *witness* for the residue $r$ modulo $m$ above $B$; the number $t$ is the *target*, the root of its backward tree.

By Lemma 2.1, the hypothesis on $q$ says exactly that $q$ is odd and not a Wieferich number. The condition on $q$ is a hypothesis, and Theorem B shows it cannot be dropped.

**The guiding example.** The map $\operatorname{Col}_5$ has three known cycles, with least odd elements $1$, $13$ and $17$. A trajectory that enters one cycle stays there, so the backward trees of these cycles are pairwise disjoint. Since $2$ generates $(\mathbb Z/5)^\times$, every $t$ with $5\nmid t$ satisfies the hypothesis of Theorem A:

**Corollary 1.1.** *If $5\nmid t$, then for every $m\ge1$ and every $r,B\in\mathbb N$ some $w\equiv r\pmod m$ with $B<w\le (B+1)\,t\,2^{2^{5m}}$ reaches $t$ under $5x+1$.*

So the backward tree of $1$, of $13$ and of $17$ each meets every residue class modulo every $m$, effectively, although no number lies in two of them. The target need not lie on a cycle, and the bound is far from the truth: for $t=7$ the least multiple of $11$ that reaches $7$ is $11$ itself, while Theorem A guarantees one below about $10^{5509226}$ (Example 4.6). So coverage of residue classes does not determine which cycle, if any, an orbit enters, and does not imply that every orbit reaches $1$.

**Theorem B (trap).** *Let $g>1$ divide $q$, and suppose $2$ has the same order $d$ modulo $q$ and modulo $qg$. If $t$ lies in the set*

$$\{x : x\equiv 2^i \ (\mathrm{mod}\ qg)\ \text{for some } i\ge 0\}\ \cup\ \{x : g\mid x\},$$

*then so does every $x$ reaching $t$ under $\operatorname{Col}_q$.*

Together with Theorem A, this gives a classification for odd $q$ (Proposition 5.2): the predecessors of $1$ meet every residue class modulo every $m$ if and only if $q$ is not a Wieferich number. The smallest Wieferich number is $21$; for $21x+1$, no $x\equiv5\pmod{63}$ reaches $1$. Franco and Pomerance [FP95] proved that for every Wieferich number $q$ some orbit of $\operatorname{Col}_q$ avoids $1$, and that Wieferich numbers have relative density $1$ among odd numbers (as stated in [Mor12, §9.7]). Theorem A therefore concerns a set of multipliers that has density zero but is infinite: it contains every power of $3$ (§2).

The same results apply to $3x+1$, with bound $(B+1)\,t\,2^{2^{4m}}$ for every $t$ with $3\nmid t$ (Corollary 4.2). For $3x+1$ the coverage statement itself is in [Mon06, MMMM13], and [MMMM13] bounds the number of odd steps [REF-CHECK]; what is new here is a bound on the witness itself and on the total number of steps, and the extension to every odd $q$ that is not a Wieferich number. As $5x+1$ shows, these results bear on residue classes, not on whether orbits reach $1$.

The double exponential in Theorem A, which occurs when $s_*$ is close to $m'$, is needed by the proof only for the odd prime factors of $m$ that do not divide $q$. When every prime factor of $m$ divides $q$, in particular for powers of $q$, the bound is singly exponential, $(B+1)\,t\,2^{d(m+1)}$ with $d=\operatorname{ord}_q(2)$ (Propositions 4.3 and 4.5); for $5x+1$ and $m=5^a$ this is $(B+1)\,t\,16^{m+1}$. When every odd prime factor of $m$ divides $q$, for instance for powers of $2$, the bound is $(B+1)\,t\,2^{\,d\,m^{\log_2 q}+\alpha+d+1}$ with $m=2^\alpha m_q$, an exponent polynomial in $m$ (Corollary 6.9). For two further families of moduli with other odd prime factors the exponent is also polynomial in $m$ (Propositions 6.11 and 6.12); §7 collects the bounds.

Theorems A and B are proved in the text, without reference to the Lean file. The Lean file, checked with Lean v4.35.0, is an independent machine check of the same statements, with different intermediate steps; Appendix A lists the formal statements. Everything else in this paper is proved in the text, except where a statement is attributed to the literature or labeled as heuristic.

§2 treats the condition on $q$, §3 the consequences of Theorem A, §4 the examples, §5 Wieferich numbers and Theorem B, §6 the proof of Theorem A, and §7 its scope.

## 2. The multiplier

**Lemma 2.1.** *Let $q>1$. There are $d,u$ with $2^d=1+qu$ and $\gcd(q,u)=1$ if and only if $q$ is odd and not a Wieferich number.*

*Proof.* If $q$ is even, $2^d=1+qu$ forces $d=0$, $u=0$ and $\gcd(q,0)=q>1$. Let $q$ be odd, $d_0=\operatorname{ord}_q(2)$, and $2^{d_0}=1+qv$. If $\gcd(q,v)=1$, take $d=d_0$. Conversely let $2^d=1+qu$ with $\gcd(q,u)=1$. Then $d_0\mid d$; write $d=d_0j$. By the binomial theorem $(1+qv)^j=1+jqv+q^2z$ for some $z$, so $u=jv+qz$. A prime dividing both $q$ and $v$ would divide $u$, which is impossible. $\square$

This is the definition of Franco and Pomerance [FP95, Definition 2], also used by Moree [Mor12, §9.7]; the Wieferich numbers in this sense form OEIS sequence A182297 [OEIS]. Other definitions under the same name are in use, for example OEIS A077816; throughout, we mean A182297.

So $q$ is a Wieferich number when some prime $p\mid q$ divides $2^{d}-1$ to a higher power than it divides $q$, where $d=\operatorname{ord}_q(2)$. For a prime $q$, this is Wieferich's condition $q^2\mid 2^{q-1}-1$ [Wie09], met by $1093$ and $3511$. For a composite it is common, through interaction between prime factors: if a prime $p$ with $p\mid q$ but $p^2\nmid q$ divides $\operatorname{ord}_r(2)$ for another prime $r\mid q$, then lifting the exponent puts an extra factor $p$ into $2^d-1$. For $q=21$: $\operatorname{ord}_7(2)=3$, so $3\mid d=6$, and $2^6-1=63=21\cdot3$. The smallest Wieferich number is $21$, the first term of A182297.

The numbers $3,5,7,9,15$ are not Wieferich numbers: $2^2=1+3$, $2^4=1+5\cdot3$, $2^3=1+7$, $2^6=1+9\cdot7$, $2^4=1+15$. More generally $\operatorname{ord}_{3^k}(2)=2\cdot3^{k-1}$, and lifting the exponent gives $v_3\bigl(4^{3^{k-1}}-1\bigr)=1+(k-1)=k$, so no power of $3$ is a Wieferich number.

For even $q$ the conclusion of Theorem A fails as well: an odd number maps to an odd number, so an orbit that reaches an odd number other than $1$ never reaches $1$, and the predecessors of $1$ are exactly the powers of $2$.

## 3. The main theorem and its readings

**Proposition 3.1 (classification of targets).** *Let $q$ be odd, not a Wieferich number, and $t\ge1$. Either $t\equiv 2^i\pmod q$ for some $i$, and the predecessors of $t$ meet every residue class modulo every $m$; or the predecessors of $t$ are exactly the numbers $2^kt$, $k\ge0$.*

*Proof.* The first case is Theorem A. Let $y$ reach $t$, and suppose some term of the orbit before it first reaches $t$ is odd; let $x$ be the last such term. All later terms up to $t$ are obtained by halving, so $qx+1=2^kt$ for some $k\ge0$. Then $2^kt\equiv1\pmod q$, so $t\equiv 2^{-k}$ is a power of $2$ modulo $q$. Hence, if $t$ is not a power of $2$ modulo $q$, every term before $t$ is even and $y=2^kt$. $\square$

In the second case the predecessors miss the class $1\bmod q$, so the hypothesis on $t$ in Theorem A cannot be weakened. Since $q$ is odd, $t\equiv2^i$ implies $\gcd(q,t)=1$. For $q=3$ and $q=5$, where $2$ generates all units, the condition is simply $q\nmid t$.

Write $X_m=t\,2^{2m^{L+1}q^m}$, the bound proved in §6.9. Theorem A has four consequences, each proved here in a line or two; none is part of the Lean file.

**Infinitude and profinite density.** Every interval $(B,(B+1)X_m]$ contains a predecessor of $t$ in each residue class modulo $m$. Applying this with $B$ replaced by a predecessor already found gives a larger one, so every residue class modulo every $m$ contains infinitely many predecessors of $t$. The profinite integers $\widehat{\mathbb Z}$ are the inverse limit of the rings $\mathbb Z/m\mathbb Z$, and a set $S\subseteq\mathbb N$ is dense in $\widehat{\mathbb Z}$ exactly when it meets every residue class modulo every $m$. So the predecessor set of every $t$ in the first case of Proposition 3.1 is dense in $\widehat{\mathbb Z}$; this density is topological, not a proportion.

**No congruence obstruction.** For $t$ as in Theorem A, a set defined by a finite Boolean combination of congruences is a union of residue classes modulo the least common multiple of the moduli, so if it is nonempty it contains a predecessor of $t$. No statement of the form "no $w\equiv r\pmod m$ reaches $t$" is true for such $t$. In particular, for $q$ odd and not a Wieferich number, no residue class can certify that some orbit of $\operatorname{Col}_q$ avoids $1$. For every Wieferich number such a class exists (Proposition 5.2), so for the target $1$ the condition on $q$ is exactly the boundary of this method.

**Sufficiency.** Following Monks [Mon06], call a set $S$ of positive integers *sufficient* for $\operatorname{Col}_q$ if the orbit of every positive integer meets the orbit of some element of $S$. Using the accelerated map instead gives the same notion: its orbits omit only the even values $qx+1$, and two orbits sharing such a value also share its half.

**Corollary 3.2.** *If $q$ is odd and not a Wieferich number, every arithmetic progression $a+b\mathbb N$ with $b\ge1$ is sufficient for $\operatorname{Col}_q$.*

*Proof.* Let $x\ge1$. Halving $x$ until it is odd gives an odd $y$ in its orbit, and then $t=qy+1\equiv1=2^0\pmod q$ is in its orbit too. Theorem A with $m=b$, threshold $a$ and $r=a$ gives $w>a$ with $w\equiv a\pmod b$ and $w\to t$, so $w\in a+b\mathbb N$ and the orbits of $x$ and $w$ meet at $t$. $\square$

For $q=3$ this is Monks's theorem [Mon06, Theorem 1.1], here with an explicit bound on the element of $S$. For Wieferich $q$ the question is left open: Theorem B does not settle it, since orbits may merge outside the trapped set.

**Cycles.** Let $q$ be odd. Every element $t$ of every cycle of $\operatorname{Col}_q$ is a power of $2$ modulo $q$. Indeed a cycle contains an odd element, since halving alone decreases. Going around the cycle backward from $t$, let $x$ be the first odd element reached (this may be $t$ itself, after a full turn). The path from $x$ to $t$ is the step $x\mapsto qx+1$ followed by halvings, so $qx+1=2^kt$ for some $k\ge0$ and $t\equiv2^{-k}\pmod q$. For $q=3$ this says that no element of a cycle is divisible by $3$. Hence Theorem A applies to every cycle element:

**Corollary 3.3.** *If $q$ is odd and not a Wieferich number, then the predecessor set of every element of every cycle of $\operatorname{Col}_q$ meets every residue class modulo every $m$, with the bound of Theorem A.*

Equivalently, every arithmetic progression contains a number whose orbit enters the cycle; for $q=3$ this is what the proof of [Mon06, Corollary 1.3] shows. The target $1$ alone would say nothing about a nontrivial cycle, which is disjoint from the backward tree of $1$; the content comes from being free to take $t$ on the cycle.

## 4. Examples

**Proposition 4.1.** *For all $m\ge1$, $\ 2m^4\,5^m\le 2^{5m}$ and $2m^3\,3^m\le 2^{4m}$.*

*Proof.* For $m=1,2$ the left sides are $10, 800$ and $6, 144$, against $32, 1024$ and $16, 256$. For $m\ge2$, passing from $m$ to $m+1$ multiplies the left sides by at most $5\cdot\tfrac{81}{16}<32$ and $3\cdot\tfrac{27}{8}<16$. $\square$

*Proof of Corollary 1.1.* $2^4=1+5\cdot3$ with $\gcd(5,3)=1$, and every $t$ with $5\nmid t$ is a power of $2$ modulo $5$. Take $L=3$. The bound of §6.9, $w\le(B+1)\,t\,2^{2m^{4}5^m}$, holds for every $m\ge1$, and Proposition 4.1 gives $2m^45^m\le2^{5m}$. (The exponent $2m^45^{s_*+1}$ of Theorem A would not suffice for $m=1$ and $m=3$: there $s_*+1=m+1$, and $2\cdot5^2=50>2^5$, $2\cdot3^4\cdot5^4>2^{15}$.) $\square$

**The cycles of $5x+1$.** Under $\operatorname{Col}_5$,

$$1\to6\to3\to16\to8\to4\to2\to1,$$
$$13\to66\to33\to166\to83\to416\to208\to104\to52\to26\to13,$$
$$17\to86\to43\to216\to108\to54\to27\to136\to68\to34\to17.$$

The cycle through $13$ is Crandall's [Cra78; Mor12, §9.7]. The cycle through $17$ is recorded by Steiner [Ste81], who shows that the cycles through $1$ and $13$ are the only ones consisting of a single circuit (in the accelerated map $T_5$: one run of odd steps followed by one run of halvings); the cycle through $17$ consists of two. By Corollary 1.1 the three backward trees, which are pairwise disjoint (§1), each meet every residue class modulo every $m$.

Whether $\operatorname{Col}_5$ has further cycles, and whether every orbit of $\operatorname{Col}_5$ enters a cycle, are open.

**Corollary 4.2.** *If $3\nmid t$, then for every $m\ge1$ and every $r,B\in\mathbb N$ some $w\equiv r\pmod m$ with $B<w\le (B+1)\,t\,2^{2^{4m}}$ reaches $t$ under $3x+1$.*

*Proof.* $2^2=1+3$, every $t$ with $3\nmid t$ is $\equiv1$ or $2\pmod3$, and $L=2$. Apply the bound of §6.9 and Proposition 4.1, as in the proof of Corollary 1.1. (Theorem A's exponent fails for $m=1$, since $2\cdot3^2>2^4$. For $m=3$ it would suffice: as $3\mid q$, here $m'=1$ and $s_*=1$, and $2\cdot3^3\cdot3^2=486\le2^{12}$.) $\square$

For moduli that are powers of $q$, the bound of Theorem A can be made singly exponential.

**Proposition 4.3 (powers of $q$).** *Let $q$ be odd and not a Wieferich number, let $2^d=1+qu$ with $\gcd(q,u)=1$, and let $t\ge1$ satisfy $t\equiv2^i\pmod q$ for some $i\ge0$. For every $a\ge0$, with $m=q^a$, and all $r,B\in\mathbb N$, some $w\equiv r\pmod m$ with $B<w\le(B+1)\,t\,2^{d(m+1)}$ reaches $t$.*

*Proof.* Here $d\ge1$, since $d=0$ forces $u=0$ and $\gcd(q,0)=q>1$. As $2^d\equiv1\pmod q$ and $t\equiv2^i$, there is $b$ with $0\le b<d$ and $2^bt\equiv1\pmod q$. For $k\ge1$ put $R_k=(2^{b+dk}t-1)/q$. This is an integer; it is odd, because $b+dk\ge1$ makes the numerator odd and $q$ is odd; and it is positive. As $qR_k+1=2^{b+dk}t$, one odd step and $b+dk$ halvings take $R_k$ to $t$.

For $h\ge1$, $R_{k+h}-R_k=2^{b+dk}t\,(2^{dh}-1)/q$, and $2^{b+dk}t$ is prime to $q$, since $t\equiv2^i$ and $q$ is odd. So $R_{k+h}\equiv R_k\pmod{q^a}$ if and only if $(1+qu)^h\equiv1\pmod{q^{a+1}}$, which by Lemma 6.4 (with $K=a$) holds if and only if $q^a\mid h$. Hence $R_1,\dots,R_m$ lie in distinct classes modulo $m$, so they meet every class. In particular there is $k_r\in\{1,\dots,m\}$ with $R_{k_r}\equiv r$, and $R_k\equiv r$ exactly when $k\equiv k_r\pmod m$.

The $R_k$ increase without bound. Let $k$ be the least index with $k\equiv k_r\pmod m$ and $R_k>B$, and put $w=R_k$. If $k=k_r$, then $w<2^{b+dm}t/q<t\,2^{d(m+1)}$ (as $b<d$). Otherwise $k-m\ge1$ and $R_{k-m}\le B$, and $qw+1=2^{dm}(qR_{k-m}+1)\le2^{dm}(qB+1)$ gives $w<2^{dm}(B+1)$. In both cases $w\le(B+1)\,t\,2^{d(m+1)}$. $\square$

The proof uses only Lemma 6.4. Proposition 4.3 is proved here and is not part of the Lean file.

**Corollary 4.4.** *If $5\nmid t$, then for every $a\ge0$, with $m=5^a$, and all $r,B\in\mathbb N$, some $w\equiv r\pmod m$ with $B<w\le(B+1)\,t\,16^{m+1}$ reaches $t$ under $5x+1$. If $3\nmid t$, the same holds for $m=3^a$ under $3x+1$, with $4^{m+1}$ in place of $16^{m+1}$.*

*Proof.* Take $2^4=1+5\cdot3$ and $2^2=1+3$ in Proposition 4.3; for $q=3$ and $q=5$ every $t$ prime to $q$ is a power of $2$ modulo $q$. $\square$

**Proposition 4.5 (moduli dividing a power of $q$).** *Under the hypotheses of Proposition 4.3, let $m\ge1$ be a number all of whose prime factors divide $q$. Then for all $r,B\in\mathbb N$ some $w\equiv r\pmod m$ with $B<w\le(B+1)\,t\,2^{d(m+1)}$ reaches $t$.*

*Proof.* Take $b$ and $R_k$ as in the proof of Proposition 4.3. That proof shows that each $R_k$ reaches $t$, and its size estimate uses only that $R_1,\dots,R_m$ meet every class modulo $m$ and that $R_k\equiv r$ exactly when $k\equiv k_r\pmod m$. For $h\ge1$, $R_{k+h}-R_k=2^{b+dk}t\,(2^{dh}-1)/q$, and $2^{b+dk}t$ is prime to $m$, since every prime factor of $m$ divides $q$. So $R_{k+h}\equiv R_k\pmod m$ if and only if $qm\mid2^{dh}-1$. Let $p\mid q$ be a prime. From $2^d-1=qu$ and $\gcd(q,u)=1$ we get $v_p(2^d-1)=v_p(q)\ge1$, and since $p$ is odd, lifting the exponent gives $v_p(2^{dh}-1)=v_p(2^d-1)+v_p(h)=v_p(q)+v_p(h)$. Hence $qm\mid2^{dh}-1$ if and only if $v_p(m)\le v_p(h)$ for every prime $p\mid m$, that is, if and only if $m\mid h$. So $R_1,\dots,R_m$ lie in distinct classes modulo $m$, and the rest of the proof of Proposition 4.3 applies without change. $\square$

For $m=q^a$ this is Proposition 4.3, which gets the same period from Lemma 6.4 alone; the new cases are composite $q$, for instance $q=15$ and $m=3^a5^b$. Proposition 4.5 is proved here and is not part of the Lean file.

**Example 4.6 (a target off the known cycles).** Let $q=5$, so $d=\operatorname{ord}_5(2)=4$ and $L=3$, and take the target $t=7$, which is admissible because $7\equiv2\pmod5$. Whether the orbit of $7$ enters a cycle is not known, and Theorem A does not need it to: it concerns the numbers that reach $7$, not where $7$ goes. One of them is $11$, since
$$11\to56\to28\to14\to7.$$

*Modulus $m=11$, residue $r=0$, threshold $B=0$.* The least witness is $11$, as no smaller positive number is divisible by $11$. In Theorem A, $m'=11$, $e=\operatorname{ord}_{11}(2)=10$, $\varphi(e)=4$ and $s_*=\lfloor10/4\rfloor+1=3$, so the guaranteed witness satisfies
$$w\le 7\cdot2^{\,2\cdot11^4\cdot5^4}=7\cdot2^{18301250}\approx10^{5509226}.$$

*Modulus $m=10$, residue $r=1$, threshold $B=0$.* The only smaller candidate, $1$, stays on the cycle through $1$, which does not contain $7$; so the least witness is again $11$. Since $10=2\cdot5$ and $q=5$, every odd prime factor of $10$ divides $q$, so the sharper bound of Corollary 6.9 (stated in §1 and proved in §6.9) applies, with $d=4$ and $\alpha=1$:
$$w<7\cdot2^{\,4\cdot10^{\log_25}+6}\approx2.22\cdot10^{255},$$
a number of $256$ digits.

The example shows two things. The bounds concern the witness the proof constructs, not the least witness, and can exceed it by millions of digits. And their size is driven by the odd prime factors of $m$ that do not divide $q$: for $m=11$ the guaranteed bound has about five and a half million decimal digits, while for $m=10=2\cdot5$, where Corollary 6.9 applies, it has $256$.

## 5. Wieferich numbers

Theorem B is stated in §1; its hypothesis on $d$ (a positive integer) is equivalent to: $2^d\equiv1\pmod{qg}$, and every $k$ with $2^k\equiv1\pmod q$ is a multiple of $d$. Call $x$ *trapped* if it lies in the set of Theorem B. By Theorem B the complement of the trapped set is mapped into itself by $\operatorname{Col}_q$; it is a union of residue classes modulo $qg$ (compare the invariant sets of residue classes in Buttsworth and Matthews [BM90]).

*Proof of Theorem B.* It suffices to show that $x$ is trapped whenever $\operatorname{Col}_q(x)$ is. If $x$ is even and $x/2\equiv2^i$, then $x\equiv2^{i+1}$; if $g\mid x/2$ then $g\mid x$. If $x$ is odd, then $\operatorname{Col}_q(x)=qx+1\equiv1\pmod g$, so $g\nmid qx+1$, and therefore $qx+1\equiv2^i\pmod{qg}$ for some $i$. Reducing modulo $q$ gives $2^i\equiv1\pmod q$, so $d\mid i$ and $2^i\equiv1\pmod{qg}$. Hence $qg\mid qx$, and $g\mid x$. $\square$

**Example 5.1.** For $q=21$, $g=3$: the powers of $2$ modulo $21$ are $1,2,4,8,16,11$, so $d=6$, and $2^6=64\equiv1\pmod{63}$. The trapped classes modulo $63$ are $1,2,4,8,16,32$ and the multiples of $3$. The class of $5$ is neither, so no $x\equiv5\pmod{63}$ reaches $1$ under $21x+1$.

**Proposition 5.2 (classification of multipliers).** *Let $q>1$ be odd. The predecessors of $1$ under $\operatorname{Col}_q$ meet every residue class modulo every $m$ if and only if $q$ is not a Wieferich number.*

*Proof.* If $q$ is not a Wieferich number, apply Theorem A with $t=1$. Otherwise let $d=\operatorname{ord}_q(2)$, $2^d=1+qv$ and $g=\gcd(q,v)>1$. Then $qg\mid 2^d-1$, so $2$ has order $d$ modulo $qg$, and Theorem B applies to $t=1$, which is trapped. At most $d+q$ classes modulo $qg$ are trapped, and $d+q<2q<qg$ because $d<q$ and $g\ge3$. So some class modulo $qg$ contains no predecessor of $1$. $\square$

Every element of that class has an orbit avoiding $1$. Call $q$ a *Crandall number* if $\operatorname{Col}_q$ has an orbit avoiding $1$ [Mor12, §9.7]. The argument recovers the theorem of Franco and Pomerance [FP95] that every Wieferich number is a Crandall number. Their proof, like Crandall's argument for $1093$ [Cra78], shows that the odd numbers $x$ for which $qx+1$ is a power of $2$ have no odd predecessors. These $x$ are $(2^{kd}-1)/q$, hence multiples of $g$, so they lie in the trapped set. Theorem B extends this dead end to an explicit union of residue classes closed under taking predecessors; we do not claim it is new.

The converse fails, and Theorem A explains how. Crandall showed that $5$, $181$ and $1093$ are Crandall numbers [Cra78; Mor12, §9.7]: for $5$ and $181$ through cycles, with least odd elements $13$ and $27$. Neither $5$ nor $181$ is a Wieferich number. So by Theorem A, for these two multipliers no residue class consists entirely of numbers whose orbits avoid $1$: such orbits can be exhibited by cycles, but not by congruences.

For a Wieferich number $q$ and a target outside the trapped set, this paper does not determine which residue classes its predecessors meet.

## 6. Proof of Theorem A

**Plan.** By Lemma 6.1 below, it suffices to find a word $\omega$ of length $\ell$ with $s$ ones, an exponent $E\ge0$ and a number $w>B$ with $q^{s}w+\kappa(\omega)=2^{\ell+E}t$ and $w\equiv r\pmod m$. Write $m=2^\alpha m_qm'$ as in §6.2. The congruence splits into three parts, each handled by one idea. Modulo $2^\alpha$, the first $\alpha$ letters of $\omega$ determine $w$ (Lemma 6.2). Modulo $m'$, the maps $S_0$ and $S_1$ are bijections whose compositions include every translation, so any class can be steered to any other (Lemma 6.3). Modulo powers of $q$, the powers of $2$ fill every class that is $1$ modulo $q$, and this is where the hypothesis that $q$ is not a Wieferich number is used (Lemmas 6.4 and 6.5). The word is chosen first, to meet the conditions modulo $2^\alpha$, $m'$ and $q^{K+1}$; the exponent $E$ is chosen last, to meet the condition modulo $q^{s+\beta}$, which depends on the word. §6.1–6.6 prove the lemmas, §6.7 shows that a witness exists, §6.8–6.9 make this effective, and §6.11 replaces the word of Lemma 6.3 by one with fewer odd steps, which proves Theorem A.

The case $m=1$ is immediate: take $w=2^kt$ with $2^{k-1}\le B<2^k$, or $k=0$ when $B=0$. Assume $m\ge2$, and fix $d,u$ with $2^d=1+qu$, $\gcd(q,u)=1$; we may take $d=\operatorname{ord}_q(2)\le q$.

The Lean file certifies the statements: the definitions and hypotheses of Appendix A, and the conclusions of Theorems A and B. The proof below is written for the reader and need not follow the Lean proof step by step; the table gives the nearest Lean declarations for each step. The Lean proof does not use Lemma 6.3: it takes the word $\omega_0$ from a covering (Lemma 6.10(b) with Lemma 6.13) from the start, as §6.11 does, and so has no separate counterpart of the first bound of §6.9; that bound is the case $s=m-1$ of `predecessor_bound` (Appendix A).

| Step | Statement | Nearest Lean declarations |
| --- | --- | --- |
| Encoding | Lemmas 6.1, 6.1′ | `integrality`, `offset_append`, `offset_le_pow` |
| Splitting $m$ | §6.2 | `split_two_power`, `split_coprime` |
| 2-adic part | Lemma 6.2 | `parity_prefix`, `prefix_mod`, `follow_prefix` |
| Part modulo $m'$ | §6.4, Lemma 6.10 | `backWord_iff`, `ones_surj`, `backWord_spread`, `sparse_word` |
| $q$-adic part | Lemmas 6.4, 6.5 | `lift_exponent`, `order_iff`, `unit_power_cover` |
| Joining and the exponent | Lemma 6.6, §6.7 | `padic_word`, `word_exists_s`, `exponent_lemma` |
| Witness and size | §6.7–6.8, Proposition 6.8 | `witness_exists`, `witness_size` |
| Size of the exponent | §6.9, §6.11 | `exponent_bound_s` |
| Sumset covering | Lemma 6.13 | `TS.chowla`, `TS.growth`, `TS.covers`, `covers_of_growth`, `covers_fin` |
| Assembly | Theorem A | `predecessor_bound_core`, `predecessor_bound`, `predecessor_bound_phi` |

### 6.1 Parity words

A *word* is a finite sequence of letters $0$ and $1$. Letter $\varepsilon$ acts by $S_\varepsilon(x)=(q^\varepsilon x+\varepsilon)/2$: halving for $0$, and $x\mapsto qx+1$ followed by halving for $1$. A word $\omega=\varepsilon_1\cdots\varepsilon_\ell$ acts by applying $S_{\varepsilon_1}$ first. Let $s(\omega)$ be its number of ones and define its *offset* by $\kappa(\varnothing)=0$ and $\kappa(\varepsilon\,\omega')=q^{\,s(\omega')}\varepsilon+2\,\kappa(\omega')$. Composing the affine maps gives

$$S_\omega(x)=\frac{q^{s(\omega)}x+\kappa(\omega)}{2^\ell},\qquad \kappa(\omega\omega')=q^{s(\omega')}\kappa(\omega)+2^{|\omega|}\kappa(\omega').$$

**Lemma 6.1.** *Let $\omega=\varepsilon_1\cdots\varepsilon_\ell$ have $s$ ones, and let $x\in\mathbb N$. The following are equivalent:*

*(a) $2^\ell\mid q^{s}x+\kappa(\omega)$;*

*(b) for $0\le i<\ell$ the value $x_i=S_{\varepsilon_1\cdots\varepsilon_i}(x)$ is an integer with $x_i\equiv\varepsilon_{i+1}\pmod 2$ (so $x_{i+1}=S_{x_i\bmod 2}(x_i)$ is the accelerated map applied to $x_i$).*

*In that case $S_\omega(x)\in\mathbb N$ and $\operatorname{Col}_q^{\ell+s}(x)=S_\omega(x)$; in particular $x\to S_\omega(x)$.*

*Proof.* Induction on $\ell$; for $\ell=0$ both conditions hold trivially. Let $\ell\ge1$, $\omega=\varepsilon\omega'$ with $\varepsilon=\varepsilon_1$, and $s'=s(\omega')$, so $s=s'+\varepsilon$. From the definition of $\kappa$,
$$q^sx+\kappa(\omega)=q^{s'}\bigl(q^{\varepsilon}x+\varepsilon\bigr)+2\kappa(\omega').\tag{6.1}$$
Since $q^{s'}$ is odd, the right side is even if and only if $q^\varepsilon x+\varepsilon$ is even, that is, if and only if $x\equiv\varepsilon\pmod2$. So both (a) and (b) force $x\equiv\varepsilon\pmod 2$, and we may assume it. Then $q^\varepsilon x+\varepsilon=2S_\varepsilon(x)$ with $S_\varepsilon(x)\in\mathbb N$, and (6.1) becomes $q^sx+\kappa(\omega)=2\bigl(q^{s'}S_\varepsilon(x)+\kappa(\omega')\bigr)$. Hence (a) holds for $x,\omega$ if and only if $2^{\ell-1}\mid q^{s'}S_\varepsilon(x)+\kappa(\omega')$, i.e. (a) holds for $S_\varepsilon(x),\omega'$; and (b) holds for $x,\omega$ if and only if (b) holds for $S_\varepsilon(x),\omega'$. The induction hypothesis gives the equivalence. Finally $S_0(x)=\operatorname{Col}_q(x)$ for even $x$ and $S_1(x)=\operatorname{Col}_q^2(x)$ for odd $x$, so each letter costs $1+\varepsilon_i$ steps of $\operatorname{Col}_q$, $\ell+s$ in total. $\square$

Direction (b)$\Rightarrow$(a) is what gives the first claim of Lemma 6.2; direction (a)$\Rightarrow$(b) is what turns a solution of the equation below into an actual orbit.

**Lemma 6.1′ (size of the offset).** *For every word $\omega$ of length $\ell$ with $s$ ones, $\kappa(\omega)\le q^s2^\ell$.*

*Proof.* By induction on $\ell$; the case $\omega=\varnothing$ is $0\le1$. For $\omega=\varepsilon\omega'$, with $s'=s(\omega')$ and $\ell'=|\omega'|$, we have $\kappa(\omega)=q^{s'}\varepsilon+2\kappa(\omega')\le q^{s'}\varepsilon+q^{s'}2^{\ell'+1}$. If $\varepsilon=0$ this equals $q^{s}2^{\ell}$. If $\varepsilon=1$, then $s=s'+1$ and $1+2^{\ell'+1}\le q\,2^{\ell'+1}$ because $q\ge2$. $\square$

A parity word is a parity vector in the sense of Terras [Ter76], Everett [Eve77] and Lagarias [Lag85]; Wirsching and Monks use equivalent back-tracing vectors, which record the number of halvings between odd steps, and the affine formula and concatenation rule above are [Wir98, Lemma 2.13, Corollary 2.10] in that language (numbering as cited in [Mon06]). It suffices to find a word $\omega$, an exponent $E$ and a $w$ with

$$q^{s}w+\kappa(\omega)=2^{\ell+E}t,\qquad w\equiv r\pmod m,$$

since then $w\to 2^Et\to t$.

### 6.2 Splitting the modulus

Write $m=2^\alpha m_qm'$ with $m_q,m'$ odd, every prime of $m_q$ dividing $q$, and $\gcd(m',q)=1$. Let $\beta$ be the least integer with $m_q\mid q^\beta$. Then $2^\beta\le m_q$: $\beta$ is at most the largest exponent $k$ of a prime $p$ in $m_q$, since $v_p(q)\ge1$, and $2^k\le p^k\le m_q$. Let $\operatorname{ord}_{m'}(2)=e_qe'$ with $\gcd(e',q)=1$ and every prime of $e_q$ dividing $q$, and let $K$ be the least integer with $e_q\mid q^K$; as for $\beta$, $2^K\le e_q$. Then $2^{q^Ke'}\equiv1\pmod{m'}$.

### 6.3 The 2-adic part

**Lemma 6.2.** *Let $\sigma$ be the first $\alpha$ letters of the parity sequence of $r$ under $x\mapsto S_{x \bmod 2}(x)$. Then $2^\alpha\mid q^{s(\sigma)}r+\kappa(\sigma)$. Moreover, if $\omega=\sigma U$ is any word beginning with $\sigma$, of length $\ell$ with $s$ ones, and $2^\ell\mid q^{s}w+\kappa(\omega)$, then $w\equiv r\pmod{2^\alpha}$.*

*Proof.* The first claim is $S_\sigma(r)\in\mathbb N$. For the second, the concatenation rule gives $q^{s}w+\kappa(\sigma U)=q^{s(U)}\bigl(q^{s(\sigma)}w+\kappa(\sigma)\bigr)+2^\alpha \kappa(U)$. Since $2^\alpha\mid2^\ell$ and $q$ is odd, $2^\alpha\mid q^{s(\sigma)}w+\kappa(\sigma)$. Subtracting the first claim gives $q^{s(\sigma)}(w-r)\equiv0\pmod{2^\alpha}$, and $q$ is odd. $\square$

### 6.4 The part modulo $m'$

Since $2$ and $q$ are invertible modulo $m'$, the maps $S_0$ and $S_1$, defined on $\mathbb Z/m'$ by the same formulas using the inverse of $2$, are bijections. The formula for $S_\omega$ in §6.1 is an identity over $\mathbb Z[1/2]$, so it also holds on $\mathbb Z/m'$: a congruence $q^{s}z+\kappa(\omega)\equiv2^\ell y\pmod{m'}$ says exactly that $S_\omega(z)=y$ in $\mathbb Z/m'$.

**Lemma 6.3.** *For all $x,y\in\mathbb Z/m'$ some word of length at most $m'-1$ sends $x$ to $y$.* (For $m'=1$ this is the empty word.)

*Proof.* Here, unlike for words, $S_\varepsilon S_{\varepsilon'}$ denotes composition: apply $S_{\varepsilon'}$ first, so $S_0S_1=S_{10}$. Every permutation $\pi$ of a finite set satisfies $\pi^{-1}=\pi^{N-1}$ with $N$ its order, so the set of maps $S_\omega$ (positive words only) is already the group generated by $S_0,S_1$; in particular a translation in that group is realised by a word. Now

$$S_0S_1(x)=\frac{qx+1}{4},\qquad S_1S_0(x)=\frac{qx+2}{4},$$

so $S_1S_0\circ(S_0S_1)^{-1}$ is translation by $1/4$ (if $y=(qx+1)/4$ then $(qx+2)/4=y+1/4$), and $1/4$ has additive order $m'$; its powers are all translations, so every $y$ is reachable from every $x$. Let $R_k$ be the set reachable from $x$ within $k$ letters. If $R_{k+1}=R_k$, then $R_k$ is closed under $S_0$ and $S_1$, hence everything. So $|R_k|$ grows by at least one until $R_k=\mathbb Z/m'$, which happens by $k=m'-1$. $\square$

For $q=3$, where $S_0$ and $S_1$ are $x\mapsto x/2$ and $x\mapsto(3x+1)/2$, the group they generate modulo $m'$ is determined in [MMMM13, Theorem 3.1]: it is generated by $x\mapsto x+1$, $x\mapsto2x$ and $x\mapsto3x$, so it consists of all maps $x\mapsto2^a3^bx+c$ and in particular contains every translation, which is the idea of the proof above. That translation by $1$ lies in the group is due to [Mon06], as recorded in [MMMM13, §3].

### 6.5 The $q$-adic part

**Lemma 6.4.** *If $q$ is odd and $\gcd(q,u)=1$, then $(1+qu)^{q^K}=1+q^{K+1}u_K$ with $\gcd(q,u_K)=1$. Consequently $(1+qu)^a\equiv1\pmod{q^{K+1}}$ if and only if $q^K\mid a$.*

*Proof.* Let $j\ge1$ and $\gcd(q,v)=1$. By the binomial theorem, $(1+q^jv)^q=1+q^{j+1}v+\binom q2q^{2j}v^2+\cdots$. Since $q$ is odd, $q\mid\binom q2$, so the second term is divisible by $q^{2j+1}$, and the terms from the third on by $q^{3j}$; as $j\ge1$, all are divisible by $q^{j+2}$. Hence $(1+q^jv)^q=1+q^{j+1}v'$ with $v'\equiv v\pmod q$, so $\gcd(q,v')=1$. Induction gives the first claim.

For the second claim we show, by induction on $K$, that for all $j\ge1$ and $\gcd(q,v)=1$: $(1+q^jv)^a\equiv1\pmod{q^{j+K}}$ if and only if $q^K\mid a$. The case $K=0$ is trivial, and "if" follows by the same binomial computation applied with $j$ in place of $1$ (the first claim is the case $j=1$, $v=u$). Let $K\ge1$. Modulo $q^{j+1}$ we have $(1+q^jv)^a\equiv1+aq^jv$, since the other terms are divisible by $q^{2j}$. So the congruence forces $q\mid av$, hence $q\mid a$. Write $a=qa'$. Then $(1+q^jv)^a=(1+q^{j+1}v')^{a'}$, and the claim for $K-1$ and $j+1$ gives $q^{K-1}\mid a'$, that is, $q^K\mid a$. The case $j=1$, $v=u$ is the second claim. (The argument does not use that $q$ is prime. This is why it proceeds by induction rather than through the order of $1+qu$: for composite $q$, knowing that this order divides $q^K$ but not $q^{K-1}$ would not by itself determine it.) $\square$

**Lemma 6.5.** *The powers $2^{da}$, $0\le a<q^K$, are exactly the $q^K$ classes modulo $q^{K+1}$ that are $\equiv1\pmod q$.*

*Proof.* Each $2^{da}$ is $\equiv1\pmod q$, since $2^d=1+qu$. If $2^{da}\equiv2^{db}\pmod{q^{K+1}}$ with $0\le b\le a<q^K$, then $(1+qu)^{a-b}\equiv1\pmod{q^{K+1}}$ (2 is a unit), so $q^K\mid a-b$ by Lemma 6.4, hence $a=b$. Thus the $q^K$ powers are distinct; the units $\equiv1\pmod q$ modulo $q^{K+1}$ are exactly $q^K$ in number. $\square$

**Corollary 6.5′ (order of $2$).** *If $d=\operatorname{ord}_q(2)$, then for every $J\ge0$ the order of $2$ modulo $q^{J+1}$ is $dq^J$, and for $x$ with $x\equiv1\pmod q$ the solutions $E\ge0$ of $2^E\equiv x\pmod{q^{J+1}}$ form exactly one class modulo $dq^J$, all of whose elements are multiples of $d$.*

*Proof.* Lemma 6.4 with $K=J$ gives $2^{dq^J}=(1+qu)^{q^J}\equiv1\pmod{q^{J+1}}$. Conversely, if $2^E\equiv1\pmod{q^{J+1}}$ then $2^E\equiv1\pmod q$, so $d\mid E$ because $d$ is the order modulo $q$; writing $E=da$, $(1+qu)^a\equiv1\pmod{q^{J+1}}$ and Lemma 6.4 gives $q^J\mid a$, so $dq^J\mid E$. For the second claim, Lemma 6.5 at level $J$ gives some $E=da$ with $2^E\equiv x$; the full solution set is then $E+dq^J\mathbb N$ (intersected with $E\ge0$), since $2$ is a unit of order $dq^J$. $\square$

The hypothesis $d=\operatorname{ord}_q(2)$ is needed here, though not in Lemmas 6.4 and 6.5: for $q=3$ the pair $d=4$, $u=5$ satisfies $2^d=1+qu$, $\gcd(q,u)=1$, but $\operatorname{ord}_9(2)=6\ne4\cdot3$. This is why §6 fixes $d=\operatorname{ord}_q(2)$, which is allowed by the proof of Lemma 2.1.

Combined with $t\equiv2^i$: every class modulo $q^{K+1}$ that is a power of $2$ modulo $q$ is $2^\nu$ for some $0\le \nu<dq^K$. Indeed, if $x\equiv2^i\pmod q$ with $0\le i<d$, then $x2^{-i}\equiv1\pmod q$, so $x2^{-i}\equiv2^{da}$ for some $0\le a<q^K$, and $x\equiv2^{da+i}$ with $0\le da+i<dq^K$. For $q=3$ this is the classical fact that $2$ is a primitive root modulo every power of $3$, used by Monks [Mon06]; for general $q$ the condition that $q$ is not a Wieferich number is exactly what this step needs.

### 6.6 Joining the conditions

**Lemma 6.6.** *For every $z\in\mathbb N$ there is a word $U$, of the form $\omega_0\,1^{K+1}\,0^\nu$ with $|\omega_0|\le m'-1$ and $\nu<dq^K$, such that*

$$q^{s(U)}z+\kappa(U)\equiv 2^{|U|}t\pmod{q^{K+1}m'}.$$

*Proof.* Modulo $q^{K+1}$: since $s(U)\ge K+1$, the term $q^{s(U)}z$ vanishes. By the concatenation rule, $\kappa(U)\equiv 2^{|\omega_0|}\kappa(1^{K+1})\pmod{q^{K+1}}$, because the ones after $\omega_0$ kill $q^{K+1}\kappa(\omega_0)$ and $\kappa(0^\nu)=0$. So the condition is $\kappa(1^{K+1})\equiv 2^{K+1+\nu}t$, independent of $\omega_0$. Now $\kappa(1^{K+1})=\sum_{i=0}^{K}2^iq^{K-i}\equiv2^K\pmod q$, so $\kappa(1^{K+1})(2^{K+1}t)^{-1}$ is congruent to a power of $2$ modulo $q$: since $t\equiv2^i\pmod q$ for some $i$ and $\kappa(1^{K+1})\equiv2^K$, it is $\equiv2^{-1-i}\pmod q$. The remark after Lemma 6.5, applied modulo $q^{K+1}$, then gives $\nu$ with $\kappa(1^{K+1})(2^{K+1}t)^{-1}\equiv2^\nu\pmod{q^{K+1}}$, which is the required congruence.

Modulo $m'$: the condition says $S_U(z)\equiv t$. With $\nu$ fixed, $S_{1^{K+1}0^\nu}$ is a bijection of $\mathbb Z/m'$; let $y$ be the preimage of $t$. Lemma 6.3 gives $\omega_0$ with $S_{\omega_0}(z)\equiv y$. $\square$

### 6.7 Existence of a witness

Let $q^{s(\sigma)}r+\kappa(\sigma)=2^\alpha z$ with $\sigma$ from Lemma 6.2, take $U$ from Lemma 6.6, and put $\omega=\sigma U$, with $s$ ones and length $\ell$. Then $Y=q^sr+\kappa(\omega)=2^\alpha\bigl(q^{s(U)}z+\kappa(U)\bigr)$ satisfies $Y\equiv2^\ell t\pmod{q^{K+1}m'}$. We seek $E$ with

$$2^{\ell+E}t\equiv Y\pmod{q^{s+\beta}m'}.\tag{$*$}$$

Modulo $m'$ this holds whenever $\operatorname{ord}_{m'}(2)\mid E$. Modulo $q^{s+\beta}$, let $j=s+\beta-1$, so $j\ge K$, and let $y\equiv Y(2^\ell t)^{-1}\pmod{q^{j+1}}$; then $y\equiv1\pmod{q^{K+1}}$. By Corollary 6.5′ with $J=j$, $2^E\equiv y\pmod{q^{j+1}}$ exactly for $E$ in one class $E_0\bmod dq^j$. Moreover $dq^K\mid E_0$: reducing modulo $q^{K+1}$ gives $2^{E_0}\equiv y\equiv1\pmod{q^{K+1}}$, so $dq^K\mid E_0$ by Corollary 6.5′ with $J=K$ (this holds for every representative, as $dq^K\mid dq^j$). The two conditions are compatible: $\operatorname{ord}_{m'}(2)=e_qe'$ with $e_q\mid q^K$ and $\gcd(e',q)=1$, so $\gcd(dq^j,e_qe')$ divides $dq^K$, which divides $E_0$. To see this, $\gcd(dq^j,e_qe')$ divides $\gcd(dq^j,e_q)\cdot\gcd(dq^j,e')$; the first factor divides $e_q\mid q^K$, and the second divides $d$, because $\gcd(q,e')=1$ gives $\gcd(dq^j,e')=\gcd(d,e')$. By the Chinese remainder theorem, $(*)$ holds for every $E$ in one class modulo

$$\Lambda=\operatorname{lcm}\bigl(dq^j,\operatorname{ord}_{m'}(2)\bigr)=\operatorname{lcm}(q^Ke',\,dq^j),$$

the two expressions agreeing because $e_q\mid q^K\mid q^j$. In particular $(*)$ holds for arbitrarily large $E$.

For such $E$, $(*)$ gives $q^s\mid2^{\ell+E}t-\kappa(\omega)$, and since $\kappa(\omega)\le q^s2^\ell$ by Lemma 6.1′, the number

$$w=\frac{2^{\ell+E}t-\kappa(\omega)}{q^s}$$

is an integer, and it exceeds $B$ as soon as $2^{\ell+E}\ge q^s(B+1+2^\ell)$, which holds for all large $E$ in the class. From $(*)$, $q^s(w-r)\equiv0\pmod{q^{s+\beta}m'}$, so $w\equiv r\pmod{q^\beta m'}$, and $m_q\mid q^\beta$ gives $w\equiv r\pmod{m_qm'}$. Lemma 6.2 gives $w\equiv r\pmod{2^\alpha}$, so $w\equiv r\pmod m$, and Lemma 6.1 gives $w\to2^Et\to t$. This proves Theorem A without the bound.

### 6.8 Making it effective

**Proposition 6.8 (size of the witness).** *Let $\sigma$, $U=\omega_0\,1^{K+1}0^\nu$ and $\omega=\sigma U$ be as in §6.7, with $s$ ones and length $\ell$, and put $j=s+\beta-1$ and $\Lambda=\operatorname{lcm}(q^Ke',\,dq^j)$. Then there is a witness $w$ for $r$ modulo $m$ above $B$ with*

$$w<(B+1)\,t\,2^{\Lambda+\ell+1},\qquad \Lambda\le e'dq^{\,s+\beta-1},$$

*where $s=s(\sigma)+s(\omega_0)+K+1\le\alpha+s(\omega_0)+K+1$ and $\ell=\alpha+|\omega_0|+K+1+\nu$ with $\nu<dq^K$.*

*Proof.* Since $2^\ell\le q^s(B+1+2^\ell)$, there is $h\ge0$ with $q^s(B+1+2^\ell)\le2^{\ell+h}<2q^s(B+1+2^\ell)$. Let $E$ be the least element with $E\ge h$ of the class modulo $\Lambda$ found in §6.7, so $E\le h+\Lambda-1$, and define $w$ as there. Then

$$w\ge \frac{q^s(B+1+2^\ell)-q^s2^\ell}{q^s}=B+1,\qquad w\le\frac{2^{\ell+E}t}{q^s}<2^{\Lambda}(B+1+2^\ell)\,t\le(B+1)\,t\,2^{\Lambda+\ell+1}.$$

Finally $q^Ke'$ and $dq^j$ both divide $e'dq^j$, because $K\le j$, so $\Lambda\le e'dq^j$. $\square$

Every bound on the witness is a calculation from Proposition 6.8: one bounds $s$, $\ell$ and $\Lambda$ for the word that was chosen. Of these only $s$ enters the exponent essentially, through the factor $q^{s}$ in $\Lambda$; $\ell$, $d$, $e'$ and $q^K$ are polynomial in $m$, and $s$ depends on the number of odd steps in $\omega_0$.

### 6.9 The size of the bound

To bound $s$, $\ell$ and $\Lambda$ for an arbitrary word chosen as in §6.7 we use four elementary facts. (i) An order is at most its modulus, so $d\le q$, $e_q\le e_qe'=\operatorname{ord}_{m'}(2)\le m'$ and $e'\le m'$. (ii) $|\omega_0|\le m'-1$ and $\nu<dq^K$, so $\ell\le\alpha+m'+K+dq^K$ and $s\le\alpha+m'+K$, hence $j+1=s+\beta\le\alpha+\beta+m'+K$. (iii) $2^{\alpha+\beta+K}\le 2^\alpha m_qe_q\le m$, and since $q\le2^L$, every $x$ with $2^x\le m$ has $q^x\le m^L$; in particular $q^{\alpha+\beta+K}\le m^L$ and $q^K\le m^L$. (iv) Both $q^Ke'$ and $dq^j$ divide $e'dq^j$, because $K\le j$; so $\Lambda\le e'dq^j$.

Hence

$$\Lambda\le e'dq^j\le m'\,q^{j+1}\le m'\cdot q^{\alpha+\beta+K}\cdot q^{m'}\le m^{L+1}q^m.$$

For the length, $\alpha+K\le\log_2m\le m$ and $m'\le m$, so $\ell+1\le 3m+1+qm^L$. Since $q\ge3$ we have $L\ge2$, and $mq^m\ge2q^2\ge6q$, so $m^{L+1}q^m\ge 6qm^L\ge qm^L+3m+1$. Thus $\ell+1\le m^{L+1}q^m$ as well, and $\Lambda+\ell+1\le 2m^{L+1}q^m$. By Proposition 6.8, under the hypotheses of Theorem A there is, for all $m\ge1$ and $r,B\in\mathbb N$, a witness $w$ with $B<w\le(B+1)\,t\,2^{2m^{L+1}q^m}$ (for $m=1$ see the start of §6). This is the first effective form of Theorem A; §6.11 improves it to the bound stated in §1.

*Remark (explanation; not used in the proof).* The double exponential has one source: the word $\omega_0$ of Lemma 6.3 may need up to about $m'$ odd steps, and each odd step raises the $q$-adic precision that the exponent $E$ must cover by a factor $q$, so that $\Lambda\le e'dq^{s+\beta-1}$ in Proposition 6.8. Only the number of odd steps matters: if $\omega_0$ could always be taken with $O(\log m')$ odd steps, then $q^s$ would be polynomial in $m$, and the bound would be $(B+1)\,t\,2^{\mathrm{poly}(m)}$. When $m'=1$ no such steps are needed, and the same computation gives a much smaller bound (Corollary 6.9). §6.10 shows that for two families of $m'$ with $m'>1$ a bounded or logarithmic number of odd steps suffices, and §6.11 shows that $s_*=\lfloor(m'-1)/\varphi(e)\rfloor+1$ odd steps suffice for every $m'$.

Two observations on how one might reduce the number of odd steps. First, the quantitative route of [MMMM13] is not cheaper. Their Lemma 4.3 builds the translation $x\mapsto x+1$ from the two branches using the inverse of $S_1$, which as a positive word costs $f-1$ further odd steps, where $f$ is the order of $S_1$ on $\mathbb Z/m'$; this gives about $(m'-1)f$ odd steps against the $m'-1$ of Lemma 6.3. Second, inverses can be avoided altogether: two words with the same numbers of ones and the same length act with the same slope, so they differ by a translation (Lemma 6.10 below makes this explicit). A class $y$ is then reached from $z$ with $s$ odd steps when $y-q^sh_0z\in H+qH+\dots+q^{s-1}H$ for some $h_0\in H=\langle2\rangle\subseteq(\mathbb Z/m')^\times$, and the question becomes how small $s$ can be for this sumset to cover $\mathbb Z/m'$. §6.10 treats two families of $m'$, and §6.11 shows that $s=s_*$ suffices for every $m'$ (Lemma 6.13). Whether $O(\log m')$ suffices for every $m'$ we do not know.

**Corollary 6.9 (moduli without other odd primes).** *Let $q$ be odd and not a Wieferich number, let $t\ge1$ satisfy $t\equiv2^i\pmod q$ for some $i\ge0$, and let $d=\operatorname{ord}_q(2)$. Let $m\ge2$, $m=2^\alpha m_q$, so that every odd prime factor of $m$ divides $q$. Then for all $r,B\in\mathbb N$ some $w\equiv r\pmod m$ with*

$$B<w<(B+1)\,t\,2^{\,d\,m^{\log_2 q}+\alpha+d+1}$$

*reaches $t$.*

*Proof.* Here $m'=1$, so $\operatorname{ord}_{m'}(2)=1$, $K=0$ and $e'=1$. In Lemma 6.6, $\omega_0$ is empty and $U=1\,0^\nu$ with $\nu<d$, so $\ell\le\alpha+d$ and $s\le\alpha+1$. Hence $j=s+\beta-1\le\alpha+\beta$ and $\Lambda=dq^j\le dq^{\alpha+\beta}$. Now $q^\alpha=(2^\alpha)^{\log_2q}$, and $2^\beta\le m_q$ gives $q^\beta\le m_q^{\log_2 q}$, so $q^{\alpha+\beta}\le m^{\log_2q}$. Proposition 6.8 gives $w<(B+1)\,t\,2^{\Lambda+\ell+1}$. $\square$

The exponent is polynomial in $m$: for $3x+1$ and $m=2^\alpha$ it is at most $2m^{\log_2 3}+\alpha+3$. For $\alpha=0$ and $q$ a prime power it is linear: $\beta$ is then the least integer with $m_q\mid q^\beta$, so $q^\beta<q\,m_q$ and $\Lambda\le dq^\beta<dq\,m$ (for $m=q^a$, $\beta=a$ and $\Lambda\le dm$). Propositions 4.3 and 4.5 are sharper there. For $\alpha>0$ the superlinear factor comes, in this proof, from the prefix $\sigma$ of Lemma 6.2: it is fixed by $r\bmod 2^\alpha$, may consist of $\alpha$ ones, and each one costs a factor $q$ of precision. The witnesses of Proposition 4.3 cannot help here: they are one odd step from $t$, and for large $k$ all of them lie in the single class $-q^{-1}\bmod 2^\alpha$, so reaching other classes modulo $2^\alpha$ needs a longer path, which is what $\sigma$ provides. This cost is forced only for witnesses of the form used here, a word followed by halvings; it is not a lower bound. We do not know whether an exponent linear in $m$ holds for these moduli, in particular for powers of $2$. Corollary 6.9 is proved here and is not part of the Lean file.

### 6.10 Fewer odd steps for special moduli

By Proposition 6.8 the only essential cost is the number of odd steps in $\omega_0$. Lemma 6.3 gives up to $m'-1$ of them for every $m'$. This section shows that for two families of $m'$ far fewer suffice.

**Lemma 6.10 (words with a prescribed number of ones).** *Let $m'$ be odd and prime to $q$, let $e=\operatorname{ord}_{m'}(2)$ and $H=\langle2\rangle\subseteq(\mathbb Z/m')^\times$.*

*(a) Let $\omega$ be a word of length $\ell$ with $s$ ones, and let the $k$-th one be the $C_k$-th letter counted from the end, so that $\ell\ge C_1>\dots>C_s\ge1$. Then on $\mathbb Z/m'$*

$$S_\omega(z)=q^s2^{-\ell}z+\sum_{k=1}^{s}q^{s-k}2^{-C_k}.$$

*Conversely every sequence $\ell\ge C_1>\dots>C_s\ge1$ comes from exactly one word.*

*(b) For all $h_0,h_1,\dots,h_s\in H$ there is a word $\omega$ with exactly $s$ ones and $|\omega|\le(s+1)e-1$ such that $S_\omega(z)=q^sh_0z+\sum_{k=1}^{s}q^{s-k}h_k$ for all $z\in\mathbb Z/m'$.*

*Proof.* (a) By induction from $\kappa(\varepsilon\omega')=q^{s(\omega')}\varepsilon+2\kappa(\omega')$ one gets $\kappa(\omega)=\sum_{k=1}^sq^{s-k}2^{i_k-1}$, where $i_k=\ell-C_k+1$ is the position of the $k$-th one: a leading one is the first one and contributes $q^{s-1}$, and every letter of $\omega'$ moves one place to the right, which doubles its contribution. Dividing by $2^\ell$ in $S_\omega=(q^sx+\kappa(\omega))/2^\ell$ gives the formula, and the positions of the ones determine the word.

(b) Put $C_{s+1}=0$ and choose, for $k=s,s-1,\dots,1$, an integer $C_k\in[C_{k+1}+1,\,C_{k+1}+e]$ with $2^{-C_k}\equiv h_k\pmod{m'}$; this is possible because $H=\{2^{-c}:c\in I\}$ for every interval $I$ of $e$ consecutive integers. Then $C_1\le se$. Choose $\ell\in[C_1,\,C_1+e-1]$ with $2^{-\ell}\equiv h_0$ and apply (a). $\square$

**Proposition 6.11 (prime power $m'$ with $2$ a primitive root).** *Let $m'=p^r$ with $p$ an odd prime and $2$ a primitive root modulo $p^r$, and let $\gcd(m',q)=1$. Then for all $z,y\in\mathbb Z/m'$ there is a word $\omega_0$ with exactly two ones and $|\omega_0|\le3\varphi(m')-1$ such that $S_{\omega_0}(z)=y$ in $\mathbb Z/m'$. Consequently, for every $m$ with this $m'$ in §6.2, Theorem A holds with the bound*

$$B<w\le(B+1)\,t\,2^{\,2q^3m^{L+1}}.$$

*Proof.* Here $H=(\mathbb Z/m')^\times$ and $e=\varphi(m')$. Put $c=y-q^2z$. Since $p\ge3$ there is $h_2\in\{1,\dots,p-1\}$ with $h_2\not\equiv c\pmod p$; then $h_2$ and $c-h_2$ are units modulo $m'$. Let $h_1=q^{-1}(c-h_2)$, a unit, and $h_0=1$. Lemma 6.10(b) with $s=2$ gives a word $\omega_0$ with two ones and $|\omega_0|\le3e-1$ with $S_{\omega_0}(z)=q^2z+qh_1+h_2=y$.

For the bound, take $\omega_0$ from this word in Lemma 6.6 instead of the word of Lemma 6.3; the proof of Lemma 6.6 uses only $S_{\omega_0}(z)\equiv y$ and that $\omega_0$ precedes $1^{K+1}$. Then $s=s(\sigma)+s(\omega_0)+K+1\le\alpha+K+3$, so $j=s+\beta-1\le\alpha+\beta+K+2$ and $q^j\le q^2m^L$ by fact (iii) of §6.9. By Proposition 6.8, $\Lambda\le e'dq^j\le m'\cdot q\cdot q^2m^L\le q^3m^{L+1}$, and $\ell\le\alpha+K+3m'+dq^K\le4m+qm^L$, so $\Lambda+\ell+1\le q^3m^{L+1}+(q+5)m^L\le2q^3m^{L+1}$. $\square$

For $q=3$ (so $L=2$) this gives $(B+1)\,t\,2^{54m^3}$ whenever $m'$ is a prime power with $2$ a primitive root, for instance $m=2^\alpha3^kp^r$ with $p\in\{5,11,13,19,\dots\}$. For $q=3$ and targets in classes prime to $p$ the case of one odd step is [MMMM13, Theorem 4.4]; Proposition 6.11 allows every target class, at the price of a second odd step.

**Proposition 6.12 (bounded index of $q$ modulo $\langle2\rangle$).** *Let $m'>1$ be odd and prime to $q$, let $e=\operatorname{ord}_{m'}(2)$ and $H=\langle2\rangle\subseteq(\mathbb Z/m')^\times$, let $\lambda\ge1$ be the least integer with $q^\lambda\in H$, and put $s_0=\lceil\log_2(m'+1)\rceil$ and $n=\lambda s_0$. Then for all $z,y\in\mathbb Z/m'$ there is a word $\omega_0$ with exactly $n$ ones and $|\omega_0|\le(n+1)e-1$ such that $S_{\omega_0}(z)=y$. Consequently, for every $m$ with this $m'$ in §6.2, Theorem A holds with the bound*

$$B<w\le(B+1)\,t\,2^{\,2q^{2\lambda+1}m^{(\lambda+1)L+1}}.$$

*In particular $\lambda=1$ when $q\in\langle2\rangle\bmod m'$, and the bound is $2^{2q^3m^{2L+1}}$.*

*Proof.* The integer $\lambda$ exists, divides $\varphi(m')/e$ (it is the order of $q$ in $(\mathbb Z/m')^\times/H$), and so $\lambda e\le\varphi(m')<m'$. Let $c\in\{1,\dots,m'\}$ be the class of $y-q^nz$, with $m'$ in place of $0$. Write $c_0=c$ and $c_r=m'$ for $1\le r<\lambda$. Each $c_r<2^{s_0}$ has at most $s_0$ binary digits, so $c_r=\sum_i2^{j_i}$ with at most $s_0$ terms. Split terms by $2^j=2^{j-1}+2^{j-1}$, valid in $\mathbb Z/m'$ with exponents read modulo $e$ (a term $2^0$ is first written as $2^e$, which is allowed as $e\ge2$), until $c_r$ is a sum of exactly $s_0$ terms $2^{j_{r,0}},\dots,2^{j_{r,s_0-1}}$ modulo $m'$. For $0\le r<\lambda$ and $0\le u<s_0$ put $i=r+\lambda u$, so that $i$ runs once through $0,\dots,n-1$, and
$$h_{n-i}=q^{-\lambda u}\,2^{\,j_{r,u}}\in H,$$
using $q^\lambda\in H$. Then $q^{i}h_{n-i}=q^{r}\,2^{j_{r,u}}$, hence $\sum_{k=1}^{n}q^{n-k}h_k=\sum_{r=0}^{\lambda-1}q^rc_r\equiv c\pmod{m'}$, because $c_r\equiv0$ for $r\ge1$. Lemma 6.10(b) with $h_0=1$ gives a word $\omega_0$ with exactly $n$ ones and $|\omega_0|\le(n+1)e-1$ and $S_{\omega_0}(z)=q^nz+c\equiv y$.

For the bound, as in Proposition 6.11: the number of ones in Proposition 6.8 is $s=s(\sigma)+n+K+1\le\alpha+\lambda s_0+K+1$, so $j=s+\beta-1\le\alpha+\beta+K+\lambda s_0$, and $s_0<\log_2m'+2$ gives $q^{\lambda s_0}<q^{2\lambda}m'^{\lambda\log_2q}\le q^{2\lambda}m'^{\lambda L}$. By fact (iii) of §6.9, $q^{\alpha+\beta+K}\le m^L$, so Proposition 6.8 gives $\Lambda\le e'dq^j\le m'\cdot q\cdot m^L\cdot q^{2\lambda}m'^{\lambda L}\le q^{2\lambda+1}m^{(\lambda+1)L+1}$. For the length, $(n+1)e\le s_0\lambda e+e\le(s_0+1)m'\le3m^2$, so $\ell+1\le(q+5)m^L$, and $\Lambda+\ell+1\le2q^{2\lambda+1}m^{(\lambda+1)L+1}$. $\square$

The bound is polynomial in $m$ whenever $\lambda$ is bounded. For $\lambda$ unbounded, or when $\lambda e$ is comparable to $m'$, the saving over Lemma 6.3 disappears. Proposition 6.12 applies, for instance, to $m'=2^k-1$ when $q\equiv2^a\pmod{m'}$ and $\gcd(m',q)=1$, although there $e=k$ is tiny.

### 6.11 Covering by sumsets: proof of Theorem A

Lemma 6.10(b) reduces the choice of $\omega_0$ in Lemma 6.6 to a covering problem. With $h_0=1$, a word with exactly $s$ ones sends $z$ to $y$ in $\mathbb Z/m'$ as soon as

$$y-q^sz\in H+qH+\dots+q^{s-1}H,\qquad H=\langle2\rangle\subseteq(\mathbb Z/m')^\times,$$

since $\sum_{k=1}^{s}q^{s-k}h_k$ runs over this sumset as $h_1,\dots,h_s$ run over $H$. We show that the sumset is all of $\mathbb Z/m'$ once $s\varphi(e)\ge m'-1$. The tool is Chowla's extension of the Cauchy–Davenport theorem to composite moduli.

**Theorem C (Chowla [Cho35]).** *Let $n\ge1$ and let $A,D\subseteq\mathbb Z/n$ be nonempty, with $0\in D$ and every nonzero element of $D$ a unit modulo $n$. Then $|A+D|\ge\min\bigl(n,\,|A|+|D|-1\bigr)$.*

The Lean file proves this statement from scratch (`TS.chowla`); in the text we cite it.

**Lemma 6.13 (covering).** *Let $m'>1$ be odd and prime to $q$, let $e=\operatorname{ord}_{m'}(2)$ and $H=\langle2\rangle$. For $s\ge0$ put $A_s=\sum_{k=0}^{s-1}q^kH\subseteq\mathbb Z/m'$, with $A_0=\{0\}$. Then $|A_s|\ge\min\bigl(m',\,1+s\varphi(e)\bigr)$. In particular $A_s=\mathbb Z/m'$ for every $s\ge s_*$.*

*Proof.* Since $m'>1$ is odd, $e\ge2$. Let $G$ consist of $0$ and the integers $i$ with $0<i<e$ and $\gcd(i,e)=1$; as $e\ge2$, $|G|=1+\varphi(e)$. Put $D_k=\{q^k(2^i-1):i\in G\}$.

(i) *$D_k$ has $1+\varphi(e)$ elements.* If $q^k(2^i-1)\equiv q^k(2^{i'}-1)$ with $i,i'\in G$, then $2^i\equiv2^{i'}$ because $q$ is a unit, so $i=i'$ because $0\le i,i'<e$.

(ii) *$0\in D_k$, and every other element is a unit.* The element for $i=0$ is $0$. Let $0<i<e$ with $\gcd(i,e)=1$, and suppose a prime $p$ divides $m'$ and $2^i-1$. Then $\operatorname{ord}_p(2)$ divides $i$, and it divides $e$ because $2^e\equiv1\pmod p$; so it divides $\gcd(i,e)=1$, and $p\mid 2-1$, which is impossible. So $2^i-1$ is a unit, and so is $q^k(2^i-1)$.

(iii) *Induction.* Since $q^k2^i=q^k+q^k(2^i-1)$, we have $q^kH\supseteq q^k+D_k$, hence $A_{k+1}=A_k+q^kH\supseteq q^k+(A_k+D_k)$. A translate has the same size, so Theorem C gives $|A_{k+1}|\ge|A_k+D_k|\ge\min\bigl(m',|A_k|+\varphi(e)\bigr)$. With $|A_0|=1$ this gives the claim. Finally, $s\ge s_*$ implies $1+s\varphi(e)\ge m'$. $\square$

*Remark.* The same induction shows that for $m'>1$ already $s=\lceil(m'-1)/\varphi(e)\rceil$ suffices, which is $s_*-1$ when $\varphi(e)\mid m'-1$ (e.g. $m'=3$); we keep $s_*$, which is $\ge1$ for all $m'$ and is the value in the Lean statement.

*Proof of Theorem A.* If $m=1$, see the start of §6. Let $m\ge2$. If $m'=1$, every word sends $z$ to $y$ in $\mathbb Z/1$, so take for $\omega_0$ in Lemma 6.6 the one-letter word $1$; then $s(\omega_0)=1=s_*$ and $|\omega_0|=1=(s_*+1)e-1$ (here $e=1$). (The empty word would also do and gives the smaller bound of Corollary 6.9; the word $1$ only lets both cases share one computation.) If $m'>1$, Lemma 6.13 and Lemma 6.10(b) with $h_0=1$ give, for the $z$ and $y$ of the proof of Lemma 6.6, a word $\omega_0$ with exactly $s_*$ ones, $|\omega_0|\le(s_*+1)e-1$ and $S_{\omega_0}(z)=y$. The proof of Lemma 6.6 uses only $S_{\omega_0}(z)\equiv y\pmod{m'}$ and that $\omega_0$ precedes $1^{K+1}$, so §6.7 and Proposition 6.8 apply with this $\omega_0$.

Now $s=s(\sigma)+s_*+K+1\le\alpha+K+s_*+1$, so $j+1=s+\beta\le(\alpha+\beta+K)+s_*+1$. With facts (i), (iii) and (iv) of §6.9,

$$\Lambda\le e'dq^j\le m'\,q^{j+1}\le m'\cdot q^{\alpha+\beta+K}\cdot q^{s_*+1}\le m^{L+1}q^{s_*+1}.$$

For the length, $\ell=\alpha+|\omega_0|+K+1+\nu$ with $\nu\le dq^K-1$, $dq^K\le qm^L$ and $\alpha+K\le\log_2m\le m$, so $\ell+1\le 2m+(s_*+1)m'+qm^L$, using $\alpha+K+2\le m+2\le 2m$. Put $Q=q^{s_*+1}$. As $s_*\ge1$ and $q\ge3$, $Q\ge q^2\ge3q$ and $Q\ge3^{s_*+1}\ge3(s_*+1)$, so each of $2m$, $(s_*+1)m'$ and $qm^L$ is at most $m^{L+1}Q/3$ (for $2m$ use $6\le m^LQ$, which holds as $m\ge2$, $L\ge2$, $Q\ge9$). Hence $\ell+1\le m^{L+1}q^{s_*+1}$, and Proposition 6.8 gives $w<(B+1)\,t\,2^{\Lambda+\ell+1}\le(B+1)\,t\,2^{2m^{L+1}q^{s_*+1}}$. $\square$

**Corollary 6.14 (number of steps).** *Let $m\ge2$. The witness $w$ constructed in the proof of Theorem A satisfies $\operatorname{Col}_q^N(w)=t$ with $N=\ell+s+E$; exactly $s$ of these $N$ steps are odd steps $x\mapsto qx+1$, and the other $N-s=\ell+E$ are halvings, where*

$$s\le\log_2m+s_*+1,\qquad N\le 2m^{L+1}q^{s_*+1}+(L+1)\,s+\log_2(B+2).$$

*Proof.* By Lemma 6.1, $w$ reaches $S_\omega(w)=2^Et$ by applying the letters of $\omega$; a letter $0$ is one halving and a letter $1$ is one odd step followed by one halving, so this takes $\ell+s$ steps, $s$ of them odd. Then $E$ halvings lead from $2^Et$ to $t$. For the bound on $s$: $s(\sigma)\le\alpha$ and $\alpha+K\le\log_2m$. For $N$: in the proof of Proposition 6.8, $E\le h+\Lambda-1$ and $2^{\ell+h}<2q^s(B+1+2^\ell)\le 2^{\ell+1}q^s(B+2)$, so $h<1+s\log_2q+\log_2(B+2)\le1+sL+\log_2(B+2)$. Hence $N\le\ell+s+h+\Lambda-1<(\Lambda+\ell+1)+(L+1)s+\log_2(B+2)-1$, and $\Lambda+\ell+1\le2m^{L+1}q^{s_*+1}$. The number of halvings, $N-s$, obeys the same bound as $N$. $\square$

The orbit of $w$ may pass through $t$ before step $N$ (for instance if $t$ lies on a cycle and the path goes once around it), so $N$ is an upper bound for the first time the orbit of $w$ reaches $t$, not necessarily that time.

For $3x+1$ the number of odd steps here, at most $\log_2m+s_*+1$ with $s_*=\lfloor(m'-1)/\varphi(\operatorname{ord}_{m'}(2))\rfloor+1$, may be compared with the bound $2(b-1)f+n+1$ of [MMMM13, Theorem 4.1], where $b=m'$; the constructions differ, and neither bound is claimed to be optimal. Corollary 6.14 is proved here and is not part of the Lean file, which states only that $w$ reaches $t$.

## 7. Scope

Theorem A is a statement about the backward tree, residue class by residue class. It does not bound stopping times, exclude nontrivial cycles, or exclude divergent orbits, and §4 shows that it holds for $5x+1$, where cycles avoiding $1$ exist. Lower bounds on the length of nontrivial $3x+1$ cycles, obtained from linear forms in logarithms [Ste78, SdW05], come from size estimates, and the results of [Tao22] concern how small orbits become. Theorem A neither implies nor contradicts them.

The double exponential in Theorem A comes only from the odd prime factors of $m$ that do not divide $q$ (§6.9). When every prime factor of $m$ divides $q$, Propositions 4.3 and 4.5 give a single exponential, $(B+1)\,t\,2^{d(m+1)}$. When $m$ has no other odd prime factors, Corollary 6.9 gives an exponent polynomial in $m$, of degree $\log_2q$. For the two families of §6.10 the exponent is also polynomial (in Proposition 6.12 for bounded $\lambda$). Theorem A is verified in Lean; the other entries are proved in the text only. The following table collects the exponents of $2$ in the bounds on the witness.

| moduli $m$ | exponent of $2$ | source |
| --- | --- | --- |
| all $m$ | $2m^{L+1}q^{s_*+1}$, $s_*=\lfloor(m'-1)/\varphi(e)\rfloor+1$ | Theorem A |
| all $m$ | $2m^{L+1}q^{m}$ | §6.9 |
| odd $m$, every prime factor of $m$ divides $q$ | $d(m+1)$ | Propositions 4.3, 4.5 |
| $m=2^\alpha m_q$ | $d\,m^{\log_2q}+\alpha+d+1$ | Corollary 6.9 |
| $m'=p^r$, $2$ a primitive root mod $p^r$ | $2q^3m^{L+1}$ | Proposition 6.11 |
| $q^\lambda\in\langle2\rangle\bmod m'$, $\lambda$ least | $2q^{2\lambda+1}m^{(\lambda+1)L+1}$ | Proposition 6.12 |

We do not know whether a linear exponent holds for powers of $2$ or for mixed moduli $2^\alpha m_q$, or whether every modulus admits a single exponential. By Proposition 6.8, a single exponential for all moduli would follow if the word $\omega_0$ of Lemma 6.3 could always be replaced by a word with $O(\log m')$ odd steps; Lemma 6.13 gives $s_*$ odd steps, and the Remark after §6.9 and §6.10 say what else is known about this.


The bounds are bounds on this proof, not estimates of the least witness. As a heuristic observation, not used anywhere: for $5x+1$, $t=1$ and $B=0$, a computation of the backward tree of $1$ by inverse search, discarding every number above a fixed cap, finds a predecessor in every class modulo $2^\alpha$ for $\alpha\le8$ and modulo $5^a$ for $a\le4$, all below $2^{22}$, whereas Proposition 4.3 gives about $2^{2500}$ for $m=625$. Because the search is truncated, the numbers found are upper bounds for the least witnesses: a witness below the cap can be reachable only through an intermediate value above it. For the same reason a class not found below the cap is no evidence that none exists; with cap $2^{34}$ some classes modulo $512$ were not found, with cap $2^{38}$ all were, the worst needing about $2^{23.6}$. This suggests that the least witness may grow only polynomially in $m$; we make no claim to that effect.

## References

- [And00] P. Andaloro, On total stopping times under 3x+1 iteration, *Fibonacci Quart.* 38 (2000), 73–78.
- [AL95] D. Applegate and J. C. Lagarias, Density bounds for the 3x+1 problem. II. Krasikov inequalities, *Math. Comp.* 64 (1995), 427–438.
- [AL95b] D. Applegate and J. C. Lagarias, The distribution of 3x+1 trees, *Experiment. Math.* 4 (1995), 193–209.
- [BM90] R. N. Buttsworth and K. R. Matthews, On some Markov matrices arising from the generalized Collatz mapping, *Acta Arith.* 55 (1990), 43–57.
- [Cad84] C. C. Cadogan, A note on the 3x+1 problem, *Caribbean J. Math.* 3 (1984), 69–72.
- [Cho35] S. Chowla, A theorem on the addition of residue classes: application to the number $\Gamma(k)$ in Waring's problem, *Proc. Indian Acad. Sci. Sect. A* 2 (1935), 242–243. [REF-CHECK: one source gives *Q. J. Math.* (O.S.) 8 (1937), 99–102; confirm from the original.]
- [Cra78] R. E. Crandall, On the "3x+1" problem, *Math. Comp.* 32 (1978), 1281–1292.
- [Eve77] C. J. Everett, Iteration of the number-theoretic function f(2n) = n, f(2n+1) = 3n+2, *Adv. Math.* 25 (1977), 42–45.
- [FP95] Z. Franco and C. Pomerance, On a conjecture of Crandall concerning the qx+1 problem, *Math. Comp.* 64 (1995), 1333–1336.
- [KL03] I. Krasikov and J. C. Lagarias, Bounds for the 3x+1 problem using difference inequalities, *Acta Arith.* 109 (2003), 237–258.
- [KZ87] I. Korec and Š. Znám, A note on the 3x+1 problem, *Amer. Math. Monthly* 94 (1987), 771–772.
- [Lag85] J. C. Lagarias, The 3x+1 problem and its generalizations, *Amer. Math. Monthly* 92 (1985), 3–23.
- [Maz26] L. Mazur, Positive lower density of Collatz predecessors, manuscript, version 1.0 (September 6, 2026), ProofAtlas, https://www.proofatlas.ai/papers/positive-lower-density-collatz-predecessors/paper-v1.pdf.
- [MMMM13] K. Monks, K. G. Monks, K. M. Monks and M. Monks, Strongly sufficient sets and the distribution of arithmetic sequences in the 3x+1 graph, *Discrete Math.* 313 (2013), 468–489.
- [Mon06] K. M. Monks, The sufficiency of arithmetic progressions for the 3x+1 conjecture, *Proc. Amer. Math. Soc.* 134 (2006), 2861–2872.
- [Mor12] P. Moree, Artin's primitive root conjecture – a survey, *Integers* 12A (2012), #A13; arXiv:math/0412262.
- [OEIS] OEIS Foundation Inc., The On-Line Encyclopedia of Integer Sequences, sequences A182297 and A077816, https://oeis.org/A182297 (accessed November 2026).
- [SdW05] J. Simons and B. de Weger, Theoretical and computational bounds for m-cycles of the 3n+1-problem, *Acta Arith.* 117 (2005), 51–70.
- [Ste78] R. P. Steiner, A theorem on the Syracuse problem, in *Proc. 7th Manitoba Conf. on Numerical Mathematics and Computing (1977)*, Congr. Numer. 20, Utilitas Math., Winnipeg (1978), 553–559.
- [Ste81] R. P. Steiner, On the "QX+1 problem," Q odd, *Fibonacci Quart.* 19 (1981), 285–288.
- [Tao22] T. Tao, Almost all orbits of the Collatz map attain almost bounded values, *Forum Math. Pi* 10 (2022), e12.
- [Ter76] R. Terras, A stopping time problem on the positive integers, *Acta Arith.* 30 (1976), 241–252.
- [Wie09] A. Wieferich, Zum letzten Fermat'schen Theorem, *J. Reine Angew. Math.* 136 (1909), 293–302. [REF-CHECK]
- [Wir98] G. J. Wirsching, *The Dynamical System Generated by the 3n+1 Function*, Lecture Notes in Math. 1681, Springer, 1998.

## Appendix A. Formal statements

The Lean file is `qx+1.lean`. The axioms reported for `predecessor_bound` and `predecessor_bound_phi` are `propext`, `Classical.choice` and `Quot.sound`; `trapped_of_iter` uses `propext` and `Quot.sound`. The use of `Classical.choice` comes from Lean's core library and proof automation, not from the mathematics: the bounds are explicit numerical expressions, and the natural-language proof in §§5–6 is effective. It is checked with Lean v4.35.0, uses only the core library, and contains no `sorry`.

The file uses the paper's symbols: $q$ the multiplier, $m$ the modulus, $m'$ the largest divisor of $m$ coprime to $2q$, $m = 2^\alpha A m'$ with $A \mid q^k$, $s$ the number of odd steps, $e = \operatorname{ord}_{m'}(2)$, and $qg$ the modulus of the trapped set. `D` is a period of $2$ modulo $m'$; it has no paper symbol. Auxiliary declarations for the covering argument live in the sub-namespace `TS`.

Definitions:

```lean
def collatz (n : Nat) : Nat := if n % 2 = 0 then n / 2 else q * n + 1
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter f k (f n)
def Reaches (n v : Nat) : Prop := ∃ k, iter (collatz q) k n = v
class NonWieferich (q : Nat) : Prop where
  one_lt : 1 < q
  unit : ∃ d u, 2 ^ d = 1 + q * u ∧ Nat.Coprime q u
def Trapped (qg g x : Nat) : Prop := (∃ k, x % qg = 2 ^ k % qg) ∨ x % g = 0
def wsum (q : Nat) : List Nat → Nat
  | [] => 0
  | i :: is => q ^ is.length * 2 ^ i + wsum q is
def Covers (q m' s : Nat) : Prop :=
  ∀ x, x < m' → ∃ I : List Nat, I.length = s ∧ wsum q I % m' = x % m'
def TS.card (m' : Nat) (S : Nat → Bool) : Nat := (List.range m').countP S
def TS.phi (e : Nat) : Nat := TS.card e (fun i => Nat.gcd i e == 1)
```

`Covers q m' s` says that every class modulo $m'$ is $\sum_{j<s} q^j 2^{i_j}$, i.e. $H + qH + \dots + q^{s-1}H = \mathbb{Z}/m'$ with $H = \langle 2\rangle$ and every summand in $H$. `TS.phi` is Euler's function.

Theorem A, `predecessor_bound`, for any decomposition and any covering length $s$:

```lean
theorem predecessor_bound (q : Nat) [NonWieferich q] (L : Nat) (hqL : q ≤ 2 ^ L)
    (m : Nat) (hm : 1 ≤ m) (α A m' k s : Nat) (hmA : m = 2 ^ α * A * m')
    (hAb : A ∣ q ^ k) (hbA : 2 ^ k ≤ A) (hM : Nat.Coprime m' (2 * q)) (hcov : Covers q m' s)
    (t : Nat) (ht0 : 1 ≤ t) (ht : ∃ i, t % q = 2 ^ i % q) (r B : Nat) :
    ∃ w : Nat, B < w ∧ Reaches q w t ∧ w % m = r % m ∧
      w ≤ (B + 1) * t * 2 ^ (2 * m ^ (L + 1) * q ^ (s + 1))
```

Theorem A for every $m$, `predecessor_bound_phi`, with $m'$ the coprime part, $e$ the order of $2$ modulo $m'$, and $s = \lfloor (m'-1)/\varphi(e)\rfloor + 1$:

```lean
theorem predecessor_bound_phi (q : Nat) [NonWieferich q] (L : Nat) (hqL : q ≤ 2 ^ L)
    (m : Nat) (hm : 1 ≤ m) (t : Nat) (ht0 : 1 ≤ t) (ht : ∃ i, t % q = 2 ^ i % q) (r B : Nat) :
    ∃ m' e : Nat, m' ∣ m ∧ Nat.Coprime m' (2 * q) ∧
      (∀ g, g ∣ m → Nat.Coprime g (2 * q) → g ∣ m') ∧
      0 < e ∧ 2 ^ e % m' = 1 % m' ∧ (∀ i, 0 < i → i < e → 2 ^ i % m' ≠ 1 % m') ∧
      ∃ w : Nat, B < w ∧ Reaches q w t ∧ w % m = r % m ∧
        w ≤ (B + 1) * t * 2 ^ (2 * m ^ (L + 1) * q ^ ((m' - 1) / TS.phi e + 2))
```

Since $\varphi(e) \ge 1$, the exponent of $q$ is at most $m'+1$; since $e > \log_2 m'$ and $\varphi(n) \ge \sqrt{n/2}$, it is $O(m'/\sqrt{\log m'})$. This is Theorem A. The exponent $2m^{L+1}q^m$ of §6.9 is that of `predecessor_bound` with $s=m-1$, which is a covering length: for $m'=1$ every $s$ is, and for $m'>1$ Lemma 6.13 applies, since $s\ge m'-1$ gives $1+s\varphi(e)\ge m'$.

Theorem B, `trapped_of_iter`:

```lean
theorem trapped_of_iter (q g d t : Nat) (hq : 0 < q) (hg : 1 < g) (hgq : g ∣ q)
    (hQ : 2 ^ d % (q * g) = 1 % (q * g))
    (hmin : ∀ k, 2 ^ k % q = 1 % q → d ∣ k)
    (ht : Trapped (q * g) g t) : ∀ k x, iter (collatz q) k x = t → Trapped (q * g) g x
```
