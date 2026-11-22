# Verifying the claims of `RESEARCH_NOTES.md`

This file is for a reader who trusts none of the earlier sessions. It lists every claim from the 2026-11-22 session (`RESEARCH_NOTES.md`, and the edits it made to `SUPPLEMENTS_B.md`) with:
- its exact scope;
- its status, using the labels of `SUPPLEMENTS_B.md`;
- the shortest proof step or witness;
- a command that checks it.

The last two sections record what is *not* checked and the blind spots found along the way.

## 0. One command

```
python3 scripts/verify_claims.py            # D1, C1–C5, C8, C10: about 15 s, needs numpy
python3 scripts/verify_claims.py --scan     # + C6: uncapped scan of q ≤ 12000, about 5 s
python3 scripts/verify_claims.py --big      # + C7: q = 221898711, about 17 s, needs numpy and about 1.5 GB RAM
```

Every line prints `PASS <id>`; any failure raises. The IDs below match the script. There are two files:
- `scripts/kappa_trap.py` holds the algorithms. It is about 200 lines; read `depth_sets` and `brute_depth_sets`.
- `scripts/verify_claims.py` holds the assertions.

**How the checks avoid trusting the fast algorithm.** The D-checks compute $\mathcal G_q$ straight from `paper.md` §1, in `definition_depths`. They enumerate $V_q$, compute $a_0(z)$ and $c_0(z) = (2^{a_0} z - 1)/q$, and use the edge rule $z \to z'$ iff $z' \equiv c_0(z) \pmod{u_q}$. They do not use Lemma B7 or the closed form $r^*$. The fast algorithm is accepted only because it matches these definition-level counts.

## 1. Claim table

| ID | Claim (exact scope) | Status | Proof / witness | Check |
|---|---|---|---|---|
| D1 | The fast iteration of RN §1.2 gives the same number of vertices with a path of length $\ge k$, for every $k \le \kappa$, as the definition-level graph, for $q \in \{21, 57, 111, 489, 7959, 10887, 11571\}$ | [C] | direct comparison | `D1[q]` |
| A1 | The iteration of RN §1.2 computes $R_k$ correctly for **every** odd $q$ | [P] from B7 | RN §1.1–1.2. Ingredients: $\mathrm{lcm}(g_0, u'_q) = u_q$; $e_0 \mid d$; B7(1),(2). Read these, about 10 lines. | D1 is evidence, not proof |
| C1 | $\kappa_{\mathrm{trap}}$, $\delta_{\mathrm{dense}}$, $\lvert R_k\rvert$ and $e_0 u_q^*$ for $21, 57, 7959, 10533, 10887, 11571$, as in the RN §1.3 table; also $4536$ and $1512$ for 11571 | [C] | fast algorithm; definition-level agreement for all but 10533 (see D1) | `C1[q]` |
| B10′ | Below $12000$, the odd $q$ with $\kappa_{\mathrm{trap}} \ge 2$ are exactly $7959, 10533, 10887, 11571$; 7959 is the least | [C] | uncapped scan over the 280 odd $q \le 12000$ with $\kappa \ge 2$; it does not assume Rules 1–3 | `C6` (`--scan`) |
| B10✗ | The original B10 (list without 10533) is false | [P] | the witness is 10533, by RN §2's hand proof, so this does not rely on the scan | `C2*` |
| R1 | $\kappa_{\mathrm{trap}}(10533) \ge 2$ | [P] | RN §2. Inputs: $\mathrm{ord}_{3511}(2) = 1755 = 3^3 \cdot 5 \cdot 13$; $v_{3511}(2^{3510} - 1) = 2$; $u_q = 27 \cdot 3511$; $g_0 = q$; $2^{3510} \equiv 1 \pmod{81}$; $\mathrm{ord}_{g_0}(2) = 3510$ | `C2a`–`C2d` |
| R1′ | $\kappa_{\mathrm{trap}}(10533) = 2$ exactly | [C] | fast algorithm only; too large for D1 | `C1[10533]` |
| R2 | The gap in B10's proof is "$p_1 \mid g_0 \Rightarrow p_1 \mid d$", false for a Wieferich $p_1$ | [P] | $3511 \mid g_0$ but $3511 \nmid d = 3510$ | `C2e` |
| R3 | $\kappa_{\mathrm{trap}}(3 \cdot 3511 \cdot 21067) \ge 3$, hence L2 is refuted | [P] | RN §2a. Inputs: $r = 21067$ is prime, $\mathrm{ord}_r(2) = 2 \cdot 3 \cdot 3511$, $r$ not Wieferich; $d = 12323610$; $u_q = 3^3 \cdot 3511^2$; $g_0 = 3 \cdot 3511$; $\kappa = 3$; $2^{3510} \equiv 1 \pmod{3^4 \cdot 3511^2}$ | `C3a`–`C3e`, `C3f3` |
| R3s | The two steps of R3 on actual vertices: $c_0(z_1) \equiv 1 \pmod{9 \cdot 3511}$ and $c_0(z_2) \equiv 0 \pmod 3$ | [C] spot check | 6 random multiples $a$ of 3510, 3 lifts each, and 3 values of $a_2$ per lift, with $c_0$ evaluated from the definition. The hand proof covers all cases; this only catches algebra slips. | `C3f`, `C3f2` |
| R3′ | $\kappa_{\mathrm{trap}}(221898711) = 3$ exactly, with $\lvert R_k\rvert = 332832267, 110912490, 36960300, 24640200$ | [C] | numpy path of the fast algorithm; not checked by D1 | `C7` (`--big`) |
| R4 | $r = 21067$ is the least prime $\equiv 1 \pmod{3511}$ with $3511 \mid \mathrm{ord}_r(2)$ | [C] | exhaustive over $r = 2k \cdot 3511 + 1 < 21067$ | `C3c` |
| R5 | B9 is not tight at 10533: its bound is $1 + \lceil 2/1 \rceil = 3$, but $\kappa_{\mathrm{trap}} = 2$ | [C] | $\delta_3 = v_3(2^{3510} - 1) - 1 = 3$ and $\nu_3 - \alpha_3 = 2$; uses R1′ | `C1[10533]` |
| F1 | Two-prime formula (RN §2b) equals $\kappa_{\mathrm{trap}}$ for all odd $q \le 40000$ with $g_0 = p_0p_1$ (309 cases), and for $10533$, $221898711$ and $36169489893$ | [C] | 1880 cases up to $200000$ also agree (loop C8's code). Patterns covered: $(0,0), (1,0), (2,0), (2,1), (3,1)$; the $\omega_{\mathrm{hi}}=1$ branch is never covered | `C8`, `C8b`, `C9` (`--huge`, about 90 s, about 6 GB) |
| F2 | The same formula for **all** $q$ with $g_0 = p_0p_1$ | lower bound [P\*], upper bound [L+] | RN §2b; the open step is marked ⚠ | read |
| T1 | Truncation to $\tilde u_q$ gives exactly $R_k$ | [C] | equal sizes for every $q \le 10^5$ with a nontrivial truncation (2652 cases; 29395 up to $10^6$); also $q = 3\cdot3511\cdot591701809$ | `C10`, `C11` (`--big`) |
| G1 | $\kappa_{\mathrm{trap}} = L^*$ (general recurrence, RN §2c) | [C] for all $q \le 10^5$ with $\kappa \ge 1$ (11246 cases; 121292 up to $10^6$); proofs [P\*] | natural $q$ reach depth $\le 2$ only | `C10` |
| D4 | $\kappa_{\mathrm{trap}}(4508686487856814609099227) \ge 4$ | [P\*] + definition-level check | explicit path of length 3 to vertex 1 (dead); 1000 random walks never reach length 4 | `python3 scripts/walk_check.py 4508686487856814609099227 1000` |
| M1 | [MMMM13] Thm 3.1 is false as printed; the first counterexample is $b = 95$ ($\lvert\langle 2,3\rangle\rvert = 36 \ne 72$); the first six are $95, 119, 143, 145, 215, 217$ | [C] | quadratic characters: $2$ and $3$ are non-squares mod both $5$ and $19$, which gives index 2 | `C4` |
| M2 | $T_0^{-2} T_{1,q} T_0 T_{1,q}^{-1} T_0 = (x \mapsto x+1)$ on $\mathbb{Z}/b$ for all odd $q$ and $\gcd(b, 2q) = 1$ | [P] | four lines in RN §3.4.1 | `C5d` (numeric sample) |
| M3 | $T_5$ has cycles $\{1,3,8,4,2\}$ (2 of 5 steps red) and $\{13,33,83,208,104,52,26\}$ (3 of 7); $\ln 2/\ln(5 + 1/13) < 3/7 < \ln 2/\ln 5$ | [C] | direct iteration | `C5a`, `C5b` |
| M4 | A red fraction $r$ in the compressed graph is an odd fraction $r/(1+r)$ in the uncompressed graph; the threshold $\ln 2/\ln q$ becomes $\ln 2/\ln(2q)$ | [P] | one line of algebra | `C5c` |
| S1 | Citation facts: definitions in [Mon06] §1 and Thm 1.1; [MMMM13] §6 definition on p. 478; Prop. 6.5 on pp. 482–483 with $m = 2^{60}$ in (c); Thm 4.4 assumes $\gcd(a, p) = 1$; reference entries | [C] read | `pdftotext -layout` on the two PDFs (not in the repo; they were uploaded to the session), then `grep -n "Proposition 6.5\|strongly sufficient\|Theorem 4.4\|^\[8\]"` | manual |

## 2. Not checked (do not cite as established)

- **Proposition 6.5(a),(b) for $q > 3$** need $q$-analogues of [MMMM13] Prop. 6.3(a),(c), which have not been proved.
- **§7 of [MMMM13] (self-duality, folding) for $q > 3$.** Nothing has been checked.
- **Whether [MMMM13] Theorem 4.1 depends on the wrong product form of Thm 3.1.** Not checked.
- **Minimality of 221898711** for $\kappa_{\mathrm{trap}} \ge 3$. Unknown; there is no search below it.
- **L2's weaker form** ($g_0 = p_0 p_1$, $\nu_{p_1} \le \alpha_{p_1} \Rightarrow \kappa_{\mathrm{trap}} \le 2$) is a guess supported by two data points.
- **L5's bound** has one data point (R3′).
- **The 2026-11-21 session log** that Gemini cited is not in the repo, so nothing from it is used.
- **OEIS A182297 and Franco–Pomerance.** Not checked.

## 3. Shortcuts and blind spots found (read before extending the work)

1. **Hand enumerations miss cases.** B10 was "checked once" and missed 10533. A Wieferich prime enters $g_0$ through $\nu_{p_1} \ge 1$, not only through $p_1 \mid d$. Any locking argument ("who locks whom", L6) must allow both routes. The scan (C6) is the safeguard; extend it rather than trust a case split.
2. **Capped scans hide the interesting cases.** Scan 1 ($N_q \le 4 \cdot 10^5$) missed every depth-2 multiplier. The scan in C6 has no cap on $N_q$ or $u_q$, only on $q$.
3. **Where the fast algorithm is checked, and where it isn't.** It is checked against the definitions only up to $u_q = 189$ (and $\lvert V_q\rvert \approx 3 \cdot 10^5$). The large cases (10533, 221898711) rest on A1, the proof that the iteration is correct. A1 is short; read RN §1.1–1.2 against B7. The hand proofs R1 and R3 give the lower bounds independently of A1, so only the *equalities* R1′ and R3′ depend on it.
4. **Never form $2^d - 1$.** Compute $\nu_p$ by raising $k$ while `pow(2, d, p**(k+1)) == 1`, as in `params`. For 221898711, $d \approx 1.2 \cdot 10^7$.
5. **Python sets do not scale past $u_q \sim 10^6$.** Use `depth_sets_np`, which indexes boolean arrays by $b \in [0, u_q)$ and runs one vectorized pass per $a \bmod e_0$. Memory is about $5 u_q$ bytes.
6. **Gemini's drafts.** The numbers usually check out. The framing does not always: "generalizes verbatim", "transfers cleanly", "milliseconds", "confirms L2". Check each such word against a proof.
7. **The primary sources contain errors too.** [MMMM13] Thm 3.1 is wrong as printed (M1). Re-derive a cited structural result before generalizing it.
8. **A vacuous check is worse than none.** A first draft of `verify_claims.py` contained two always-true assertions; they were caught and replaced. When you add a check, make sure it can fail: change an expected value and watch it fail.
