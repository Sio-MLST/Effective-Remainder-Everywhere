For every odd $q>1$ and every target $t\ge 1$, the backward orbit $R_q(t)$ of the map $\mathrm{Col}_q$ ($x\mapsto x/2$ for even $x$, $x\mapsto qx+1$ for odd $x$) is either dense in the profinite integers $\widehat{\mathbb{Z}}$ or a Haar-null set, and no other case occurs. The target may lie anywhere, on a cycle or off it, and nothing is assumed about its forward orbit. Which case holds is decided by a directed path of length $\kappa$ in a finite graph on the residues modulo $N_q$, where $\kappa$ and $N_q$ are computed from the order of $2$ modulo $q$. In the dense case every residue class modulo every $m$ contains a predecessor of $t$, with an explicit bound on its size (Theorem A). In the null case every chain of odd steps has length at most $\kappa$, and $R_q(t)$ meets at most $(n+1)^{\kappa+1}$ classes modulo $2^n$ (Theorem B). The proofs are constructive: the witnesses in Theorem A are built by explicit finite procedures, and the dichotomy is decided by a finite computation. This can be read off the proofs themselves; as a machine check, the integer and finite-modulus statements are also formalized in Lean 4.35 core without Mathlib. The Haar-measure conclusions follow from them in a few lines and are not formalized. The results concern backward orbits only: they say nothing about forward orbits or the Collatz conjecture.

The parameters are $d = \mathrm{ord}_q(2)$ and $u = (2^d - 1)/q$; $u_q$ is the part of $u$ made of primes dividing $q$, $N_q = q\,u_q$, and $\kappa$ is the least $k \ge 0$ with $u_q \mid q^k$ (`paper.md`, §1).

## Examples

* $q = 5$: $d = 4$, $u = 3$, $\kappa = 0$. The criterion is $t \bmod 5 \in \langle 2 \rangle$, which is every unit, so every $t$ not divisible by $5$ (for instance $t = 13$, $t = 17$) reaches every residue.
* $q = 7$: $d = 3$, $\kappa = 0$. The criterion is $t \bmod 7 \in \{1, 2, 4\}$. The targets $t = 9, 11, 15, 16$ qualify; $t = 13$ and $t = 17$ fall under Theorem B.
* $q = 21$: $d = 6$, $u = 3$, $\gcd(q, u) = 3$, so $\kappa = 1$. Among small targets the criterion holds for $t = 11, 22, 23, 25, 29, 37, 43, 44, 46, 50, 53, 58$.
* $q = 55$: $d = 20$, $\kappa = 1$; $t = 13$ and $t = 17$ qualify.

The odd $q$ with $\kappa \ge 1$, that is $\gcd(q, u) > 1$, begin $21, 39, 55, 57, 105, 111, 147, 155, 165, 171, \dots$ They are covered by the same theorem as every other $q$.

(These lists were computed from the definitions; they are not part of the formalization.)

## Checking the proof

The folder `lean/` is a Lean 4.35 project (toolchain `leanprover/lean4:v4.35.0`, Lean core only, no Mathlib). Build it with

```
cd lean
lake build
```

The root file `lean/Collatz.lean` ends with `#print axioms` for the main statements:

| Paper | Lean 4.35 |
| --- | --- |
| Proposition 1 | `Collatz.general_prop1` |
| Theorem A | `Collatz.general_theorem_A` |
| Theorem B | `Collatz.general_theorem_B` |

In Lean 4.35 these report only `[propext, Quot.sound]`; in particular `Classical.choice` is not used. A compiler confirms the proofs, not that the formal statements say what the paper says: to check that, read the definitions `collatz`, `iter` and `Reaches` and the three statements above. `paper.md` ends with a table matching each section to its Lean 4.35 modules.

## Files

* `paper.md`: the paper (Proposition 1, Theorem A, Theorem B, and the profinite derivation).
* `SUPPLEMENTS.md`: sharper bounds for special moduli, corollaries, a worked example and open questions. Not formalized in Lean 4.35.
* `lean/`: the Lean 4.35 formalization.
