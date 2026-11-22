# Harness contract for the orchestrator

The orchestrator prompt assumes these guarantees. At the start, the orchestrator reports which of them are missing. A missing guarantee is a known gap, never silently degraded.

| # | Guarantee | Who provides it | Default |
|---|---|---|---|
| H1 | A tool-call cap on every worker leg | the spawn API | 10 calls per leg |
| H2 | Read-only tool sets for legs that only ask a question | the spawn API | — |
| H3 | Raw tool logs (calls, outputs, IDs), written as a side effect, not with the worker's tool calls | the harness, or the worker session's event log | — |
| H4 | Skip, timeout and cap counts pulled from raw tool output | the harness's tool wrappers | — |
| H5 | Auditors get read access to H3 and the source tree, and may re-run read-only commands | the spawn API | — |
| H6 | Claim IDs are assigned by the harness, in order of first appearance. After each sheet is submitted, the harness draws which residue is sampled (ID mod 3) from a seed the worker never sees. | the harness | k = 3 |
| H7 | The restart threshold N and the escalation threshold M | the user, or these defaults | N = 3, M = 20 |
| H8 | The state (commit hash or environment) recorded with each result | the harness | — |
| H9 | The user's approval for changes outside the session | the session permissions | — |
| H10 | **Audit budget per stop.** Priority: changes to the record or tests, then the final claim, then direct dependencies of the definition of done, then the sample. Claims over the budget are listed as "unaudited" and carried into the handover. | fixed here | 3 audits per stop |
| H11 | **Dependency edges.** The harness adds an edge wherever one claim's evidence cites another's tool call. The final audit re-derives the final claim's dependencies from its evidence, and an edge that was left out counts as an undisclosed selection, so the verdict is fail. | the harness, plus the final auditor | — |

**Accepted gaps:**
- An edge left out between two intermediate claims, with no shared tool call, is caught only if it lies on the final claim's re-derived path.
- Claims over the budget go unaudited. That is disclosed, not hidden.

**When the worker is another session** (H1 can't be enforced): the auditor reads the worker session's event log for H3. Each orchestrator message is one leg. The cap is reported as unenforced.

All the defaults are starting guesses, not calibrated values.

**Claim line format, for illustration:**
`C4 | observed | scope: inputs 1–500, 12 skipped (timeout) | "PASS 488/488" [tool call t-31] | depends on: C2`
