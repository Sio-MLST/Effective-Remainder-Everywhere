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

- **Two-outcome test:** "if every *realistic* outcome leaves your next decisive step
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

## Known limits

- Length grew from about 20 lines to about 105. The growth is mostly the drift lists and
  the handoff section. A test run should show whether the extra length pays off or
  whether models skim it.
- Some phrasing ("Two-outcome test" while the text says "every realistic outcome") is a
  label of convenience, not literally two outcomes.
