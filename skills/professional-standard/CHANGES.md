# professional-standard: revision notes

Files in this folder:
- `SKILL.old.md`: the skill as installed before revision, copied unchanged.
- `SKILL.md`: the revised skill.
- `CHANGES.md`: this file.

**Status:** the revision was drafted over four review passes, in which Claude and a second
reviewer critiqued each other's drafts, with a final set of edits. **It has not been tested
on any model.** The cheapest real check is to give the same 2–3 tasks to Claude and Gemini,
with and without each version, and compare whether outputs label claim status, put
evidence next to claims, and avoid the drift patterns listed in the skill.

## Goal

One skill that applies to **any serious work** (not mainly math and code) and to **any
model, agentic or chat-only**, at the same bar. Most of it should read as common sense.
Field-specific advice appears only as brief reminders.

## What was kept from the old skill

| Old idea | Where it lives now | Why kept |
|---|---|---|
| Take the advisor's seat before acting, from memory, before context narrows the view | *Orient before moving* | It is the core mechanism and applies to any model. The reason (context pulls thinking toward the average and toward what's on screen) is stated explicitly, because the instruction loses its force without it. |
| "Let me…" phrases as the cue | *Momentum cues → Action reflex* | Concrete, recognizable trigger. |
| Is it worth doing; would the next step change | *Two-outcome test* | Tightened (see below). |
| When: work done too early gets redone | *Order* | Folded into one line. |
| Locate before searching a range | *Narrow first* | Generalized beyond code and web search. |
| Web search returns the average | *Tool drift* | Moved into the shared drift list so reviewers can spot it too. |
| Don't over-check; recipient checks anyway; models judge "works" better than "good" | *One targeted sanity check* | Kept with its reason attached. |
| Claims must not outrun the work | *Claims and handoff* | Expanded into concrete status labels. |

## What was added, and why

1. **Collaborator stance and mining broken ideas.** From the user's standing brief: be a
   sharp collaborator, not a cheerleader or trivia auditor. When an idea fails, trace why it
   almost worked and give back the exact breaking point. The old skill had neither.
2. **Handoff to a skeptical successor.** The old skill's only handoff advice was "state
   plainly what it does and doesn't do." The revision requires status labels, evidence
   next to each claim, disclosure of shortcuts and blind spots, and results placed where a
   successor will look. Without these, the next session has to re-derive everything.
3. **Prose reflex alongside action reflex.** The old skill guarded only against
   tool-using momentum. Reasoning-only sessions fail in a matching way: certainty without
   evidence, "clearly", regenerating unchanged text. The cue is worded as "certainty with
   no evidence attached" and not as a banned word, so that real checking isn't
   discouraged.
4. **"Keep it silent."** Asking a model to imagine expert advice tends to produce visible
   preambles, which contradicts the ban on padding. The advisor step stays internal.
5. **Shared drift lists (tool drift and reasoning drift).** The central addition. Not every
   model is agentic, but every model can review one that is. A chat-only reviewer who knows
   how tool work goes wrong can catch tunnel vision the tool user misses. The reverse also
   holds. The list includes the reviewer's own typical failure: deferring to output
   because it ran.
6. **The deal (two-way).** Tool users leave runs inspectable by someone who can't re-run
   them (question, command, domain, output). Reasoners mark unexecuted derivations and name
   the falsifying test. Either side reviews direction, assumptions and evidence.
7. **One standard regardless of tools.** "Having tools doesn't excuse skipping thought;
   lacking them doesn't excuse claiming certainty." Status labels include *derived by hand
   (not executed)* so a toolless model can label its result honestly instead of
   overclaiming or apologizing.
8. **Never describe the unseen.** Assertions about files, code or sources that were not
   actually read are a common failure for models with and without tools.
9. **Brief field reminders.** Math, code, empirical work and writing get one line each.
   This keeps the skill general.

## Tightenings

- **Outcome test** (called "two-outcome test" in revision 1): "if every *realistic* outcome leaves your next decisive step
  unchanged, skip it." The earlier wording ("if none changes…") could be gamed by
  inventing a vague "builds confidence" outcome.
- **Delta vs. artifact:** these two rules seemed to conflict. During an exchange, send
  only what changed. A final handoff artifact must be self-contained.
- **Padding vs. intervention:** "Pointing out a wrong direction is not padding." This
  keeps the no-meta-talk rule from silencing a reviewer.
- **De-duplication:** "would the next step change", "check only when it matters" and
  "don't re-run everything" each appeared up to three times across drafts. Each now
  appears once.
- **Tone:** "unfalsified swagger" became "unbacked certainty". Both models follow this
  document, so it should not read as a jab at either.

## Deliberately left out

- Checklists and templates: they invite mechanical compliance and bloat.
- Model-specific instructions: the point is one shared standard.
- References to particular tool names or environments: they would make the skill
  unusable for chat-only models.

## Revision 2 (after external review and user feedback)

| Issue raised | Change | Reason |
|---|---|---|
| "Work out silently" fails for models without private reasoning: they think only in generated tokens. | The advisor step has its concrete prompts back (experts, practices, what excellence looks like, the trap). It runs in private reasoning if there is any, otherwise as a few lines of framing. | The old skill's wording worked because it was concrete. "Silently" assumed a scratchpad. |
| The two-party review protocol is dead weight in solo work. | "How work goes wrong" now opens: "check your own work, a collaborator's, or an earlier session's. Your past self is the other party whenever no one else is." The separate "deal" paragraph is gone; its content moved into *Claims and handoff*. | The skill must work solo or in a group. The drift lists work as a self-check, so they stay. |
| "One sanity check of what you changed, then stop" breaks for proofs and designs, where one premise feeds many steps. | New *Checking* section: check the change **and what depends on it**, then stop. Independent evaluation is a reason to make work checkable, not to leave known breaks. | The old rule fit modular code with tests. Dependents generalize it. |
| Status labels (*proved*, *plausible*, …) fit formal work badly and invite tag clutter. | **Labels removed** (user's call, and the main change). Claims must carry their own evidence instead: checkable proofs, run receipts (command, output, where the record lives: commit, CI run, session log), quotes, kept refutations with their derivation, reasons behind judgment calls, and what wasn't checked. | A successor doesn't trust "[proved]" and re-checks anyway. What saves time is evidence that is quick to inspect, e.g. finding the Lean build output in a session log instead of reinstalling Lean. A bare verdict is vacuous. |
| Full apparatus on every turn vs. "send only the delta". | The full apparatus applies to durable handoffs. In conversation: "back what you say, without ceremony." | It removes the conflict without a rule about when tags apply, since there are no tags now. |
| Field know-how was seen as overfitting. | Kept. Brief field examples aren't a flaw. | User's call. Know-how from one field can still serve as a general illustration. |

**Correction to "Known limits" below:** the first version of this file said length grew
"from about 20 lines to about 105". That compared unwrapped paragraphs with hard-wrapped
lines. By word count: old 665 words, revision 1 856 words, revision 2 987 words.

## Known limits

- Length: see the word counts in Revision 2. A test run should show whether models skim it.
- Items 2 and 7 under "What was added" and the "Tightenings" entries describe revision 1.
  Where they mention status labels, Revision 2 supersedes them.
