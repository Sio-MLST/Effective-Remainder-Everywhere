# Reaching Every Residue

Backward orbits of $qx+1$ maps and their closure in the profinite integers.

For an odd $q > 1$ let $\operatorname{Col}_q$ halve even numbers and send odd $x$ to $qx+1$. For a target $t \ge 1$ let $R_q(t)$ be the set of all $x$ whose orbit reaches $t$. The target $t$ can be anywhere: inside a cycle, outside every cycle, on a divergent orbit or on a convergent one. Nothing below depends on what the forward orbit of $t$ does.

**Result.** For every odd $q > 1$ and every $t \ge 1$, exactly one of two things happens, and a finite computation on a residue graph decides which.

* **Reaching every residue (Theorem A).** For every modulus $m$, residue $r$ and bound $B$ there is $w \equiv r \pmod m$ with $w > B$ and $w \to t$, with an explicit bound on the least such $w$. Equivalently $R_q(t)$ is dense in $\widehat{\mathbb{Z}}$, and the closure has Haar measure $1$.
* **Finite-depth trap (Theorem B).** Every backward chain of odd steps has bounded length, $|R_q(t) \bmod 2^n| \le (n+1)^{\kappa+1}$, and the closure has Haar measure $0$.

The criterion (Proposition 1) is the existence of a directed path of length $\kappa$ from $t \bmod N_q$ in a finite graph $\mathcal{G}_q$ on residues modulo $N_q = q\,u_q$. The numbers $u_q$ and $\kappa$ come from $d = \operatorname{ord}_q(2)$ and $u = (2^d - 1)/q$, and are defined in `generalAB.md`, §1.

## Examples

* $q = 5$. Here $d = 4$, $u = 3$, $\kappa = 0$, and the criterion reduces to $t \bmod 5 \in \langle 2 \rangle$, which is every unit. So $t = 13$ and $t = 17$ both reach every residue, as does every $t$ not divisible by $5$.
* $q = 7$. Here $d = 3$, $\kappa = 0$, and the criterion is $t \bmod 7 \in \{1, 2, 4\}$. The targets $t = 9, 11, 15, 16$ qualify; $t = 13$ and $t = 17$ do not and fall under Theorem B.
* $q = 21$. Here $d = 6$, $u = 3$, $\gcd(q, u) = 3$, so $\kappa = 1$ and the path in $\mathcal{G}_{21}$ has length one. Among small targets the criterion holds for $t = 11, 22, 23, 25, 29, 37, 43, 44, 46, 50, 53, 58$.
* $q = 55$. Here $d = 20$, $\kappa = 1$, and $t = 13$ and $t = 17$ qualify.

The odd $q > 1$ with $\gcd(q, u) > 1$ (Wieferich numbers in the sense of Franco and Pomerance) begin $21, 39, 55, 57, 105, 111, 147, 155, 165, 171, \dots$ For these $\kappa \ge 1$ and the path in $\mathcal{G}_q$ has positive length. They are treated by the same theorem as every other $q$, with no separate case.

(The example lists above were computed directly from the definitions in `generalAB.md`; they are not part of the Lean formalization.)

## Formal verification

The integer and finite-modulus statements (Proposition 1, Theorems A and B with every explicit bound) are formalized as `general_prop1`, `general_theorem_A` and `general_theorem_B`, using only Lean 4.35 core with no Mathlib. The toolchain is `leanprover/lean4:v4.35.0`.

The recorded Lean 4.35 build output of the formalization shows `Build completed successfully (45 jobs)`, and `#print axioms` reports `[propext, Quot.sound]` for these theorems. In particular the proof does not use `Classical.choice` in Lean 4.35. The profinite ring $\widehat{\mathbb{Z}}$ and its Haar measure are not in Lean 4.35 core; the measure statements follow from the formalized ones in a few lines (`generalAB.md`, §6).

A compiler confirms that the proof is correct, but not that the formal statement says what the paper says. To check that, a reader needs the definitions `collatz`, `iter` and `Reaches` and the statements of the three theorems.

## Files

* `generalAB.md`: the paper (Proposition 1, Theorem A, Theorem B).
* `SUPPLEMENTS.md`: sharper bounds for special moduli, corollaries, examples and open questions. Not formalized in Lean 4.35.
* `qx+1.lean`: Lean source (single file).

## What this does not establish

These are statements about backward orbits only. Nothing here bears on forward orbits, on cycles beyond those in $R_q(t)$, or on the Collatz conjecture.
