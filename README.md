# Effective Remainder Everywhere

Let $N \ge 1$, let $w$ be a natural number not divisible by $3$, and let $r$ be any residue. Then some natural number $n \equiv r \pmod N$ has a Collatz orbit that reaches $w$, and $n$ can be chosen no larger than $w \cdot 2^{2^{48N^4}}$. Taking $N$ to be a larger modulus gives infinitely many such $n$ in every residue class.

The predecessor tree for any $w$ coprime with 3 is dense in $\widehat{\mathbb{Z}}$.

This repository contains the paper (PDF and LaTeX source) and a Lean 4 formalization of the result. This README explains what the result says, why the bound matters, and how the proof is organised. It does not replace the paper.

## What the result says

The Collatz rule sends an even $n$ to $n/2$ and an odd $n$ to $3n+1$. Write $n \rightsquigarrow w$ if repeated application of this rule starting from $n$ reaches $w$. The question is which numbers reach a given $w$, and how they are distributed among residue classes.

The condition $3 \nmid w$ is needed. A number of the form $3m+1$ is never a multiple of $3$, so the only way to reach a multiple of $3$ is by doubling. If $3 \mid w$, every number that reaches $w$ is also a multiple of $3$, and the statement fails for $N = 3$ and $r = 1$.

The theorem says that the predecessors of $w$ are not confined to any residue class. For every $N$ and every $r$ there is a predecessor in that class. Corollary 1.2 of the paper gives infinitely many, by applying the bounded form to a larger modulus.

This is not the Collatz conjecture. It does not say that every number reaches $1$, and it does not bound how long any orbit takes. It also does not depend on it: only the backward tree of $w$ is at issue, so the statement holds whatever the forward orbits do. Indeed the same proof carries over to the $5x+1$ map, whose forward behaviour is entirely different.

## What the bound does and does not say

The bound $n \le w \cdot 2^{2^{48N^4}}$ limits the numerical size of the witness $n$. It does not limit the number of steps in its orbit, and it does not say that $n$ is the smallest witness in its class.

Smaller witnesses often exist. For example, with $N = 7$ and $w = 11$, the number $7$ is a witness: $7 \to 22 \to 11$, and $7 \equiv 0 \pmod 7$. The construction in the paper does not find this witness. It finds some witness, which may be much larger. The bound says only that the least witness is at most the stated value, so that a search over $n$ in increasing order is guaranteed to terminate.

The bound is an explicit formula and is very large. Thepaper does not claim that it is close to optimal.

## Earlier version

An earlier version of this work proved the existence of witnesses in every residue class, with a lower bound on $n$ but no upper bound. This version adds an explicit upper bound and uses a different argument for the part of the modulus coprime to $6$. The paper contains a note on the relationship between the two versions.

## How the proof is organised

### Splitting the modulus

Write $N = 2^a \cdot 3^b \cdot M$, where $\gcd(M, 6) = 1$. The factor $2^a \cdot 3^b$ and the factor $M$ are handled by different methods.

### The $2$- and $3$-parts: parity words

Running the shortcut map $T$ (which halves even numbers and sends odd $n$ to $(3n+1)/2$) forward along a chosen pattern of even and odd steps is an invertible way to pass information between congruences. A suitable pattern turns a congruence modulo $2^a \cdot 3^b$ into a congruence for a single natural number $m$ that reaches $w$, modulo $3^{j+b} M$.

### The $M$-part: fibres of the backward closure

For $M$ coprime to $6$, the backward moves $n \mapsto 2n$ and $n \mapsto (n-1)/3$ act on residues modulo $M$ in a reversible way, because $2$ and $3$ are units modulo $M$. The paper defines a closure of $w$ under these moves, and for each class $a$ modulo $3^{K+1}$ a *fibre*: the set of residues modulo $M$ of closure points lying in that class.

Several facts follow. Fibres over live residues (those not divisible by $3$) all have the same size, because doubling carries one fibre into another and $2$ generates the live residues modulo a power of $3$. The fibres stabilise as $K$ grows. Each backward move carries one fibre onto another by an affine map $t \mapsto \lambda t + \mu$.

### Stabilizers and the minimal period

A map of residues modulo $M$ is a *stabilizer* if it carries the full fibre structure onto itself. Several explicit affine maps are stabilizers, including multiplication by a power of $2$ and a loop map built from the backward moves. Composing and conjugating these gives translations.

Call $d$ a *translation period* if $t \mapsto t + d$ is a stabilizer. The translation periods form a subgroup of the integers, so they are the multiples of a least positive period $q$, and $q$ divides $M$. If $q > 1$, the powers of $4$ modulo $q$ would have to be rigid in a way that contradicts the structure of powers of $4$ modulo powers of $3$. Hence $q = 1$, and translation by $1$ is a stabilizer.

Translation by $1$ then shows that the fibre over $1$ is the whole of $\mathbb{Z}/M\mathbb{Z}$. Since all live fibres have equal size, every fibre is full.

### Hitting a prescribed residue

Once every residue modulo $M$ is available in the right class, the remaining step is to choose a power of $2$ that lands the target in a prescribed class modulo $3^{K+1} M$. The exponent lemma controls the size of that power. Its bound is what produces the explicit estimate $w \cdot 2^{2^{48N^4}}$ for $n$.

## Formal verification

The file `Effective_Remainder_Everywhere_2026-11-01.lean` uses only Lean's core library and imports nothing. It was checked with Lean 4.35.0. Other versions have not been tested.

The main statement is `ERE.effective_remainder_everywhere`, and the infinitude statement is `ERE.remainder_infinitely_often`. To check the file, run:

```
lean Effective_Remainder_Everywhere_2026-11-01.lean
```

The file ends with `#print axioms` commands for both theorems. They report only `propext`, `Classical.choice` and `Quot.sound`, the standard axioms of Lean's core logic.

A compiler confirms that the proof is correct, but not that the formal statement says what the paper says. To check that, a reader needs only the definitions `collatz`, `iter` and `Reaches` and the statement of `effective_remainder_everywhere`, which together take a few lines.

The paper states the SHA-256 hash of this file. Use `sha256sum` to confirm that your copy matches it.

## Files

- `Effective_Remainder_Everywhere_2026-11-01.pdf`: the paper.
- `Effective_Remainder_Everywhere_2026-11-01.tex`: the LaTeX source.
- `Effective_Remainder_Everywhere_2026-11-01.lean`: the Lean 4 formalization.

- `ERE 5x+1.lean` proves the analogue for $w$ with $5 \nmid w$ and moduli $N$ with $3 \nmid N$ for the $5x+1$ problem.

The hypothesis $3 \nmid N$ is an artefact of the period argument (the order of $2$ modulo $3^c$ introduces a factor the $5$-power induction does not control) and is expected to be removable. It will be folded into the main text once the caveat-free proof is complete.

## What this does not establish

The result says that residue classes are not excluded from the predecessors of $w$, with an explicit size bound on the least predecessor in each class. It does not say anything about the Collatz conjecture, about the length of orbits, or about the size of the least predecessor beyond the stated bound.
