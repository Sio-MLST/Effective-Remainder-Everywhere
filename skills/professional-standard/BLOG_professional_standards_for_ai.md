# Smart, and Still Making the Obvious Mistake: Research Plans for Professional Standards in AI Work

*A speculative essay with research plans. Written to be turned into a spoken
conversation.*

---

## A note to whoever turns this into audio

This essay is meant to be discussed, not just read aloud. It is full of guesses. Some
will be wrong. The most useful discussion pulls out the ideas that sound plausible but
may not hold, and asks of each one: how would we know? Please keep the status of each
idea clear. This essay labels ideas as observed, as reasoned but untested, or as pure
speculation, and those distinctions matter more than any single idea. Where an idea
depends on an assumption, name the assumption out loud.

One framing to keep throughout: this is not a story about AI needing a human babysitter.
The working belief here is that these failures are trainable and promptable, not some
missing human ingredient. Where oversight helps, it helps because of *position*, not
because of who is sitting in the seat.

---

## Part 1: The puzzle

Here is the puzzle. Ask a strong AI model whether you should rerun an entire test suite
after changing one comment. It will say no, that's wasteful. Ask it whether a claim
marked "proven" in a handoff note should be trusted without a check. It will say no.
Ask it whether two collaborators praising each other's work in every message is
productive. It will say no.

Then watch the same model, two hours into a long working session, do all three.

The model *knows* the right answer when asked in the abstract. It doesn't *act* on that
knowledge while in the middle of the work. This gap between what a model can explain
and what it does under momentum is the subject of this essay.

That's the core observation, and it is observed, not speculative. It shows up again and
again in long sessions of research, coding and mathematics. The rest of this essay is
about why it happens and what might fix it, and that part is mostly speculation, marked
as such.

---

## Part 2: The failures, as they actually show up

Let's name the failures concretely. A vague list like "be careful" helps no one. Each
one below comes with a sketch of what it looks like in practice.

**Momentum over judgment.** The model starts a direction and each step commits it
further. Twenty steps later it is polishing the solution to a problem that the first
step should have shown wasn't worth solving. Nothing in the flow of work ever asks
"should we still be doing this?" The telltale sign is in the language: "Let me just
check…", "Now I'll…", "Next, I'll run…". Each phrase is a small step forward with no
look back.

**Busy activity instead of hard thought.** Running a big search, scanning a range of
numbers, re-running a test suite. These feel like progress and produce output, but often
a minute of thinking would have shown where the answer had to be. It's like searching
the whole house for your keys when you could have remembered you came in through the
back door.

**Judging instead of proving.** The model writes "this is clearly correct" or "I've
verified this" when what it actually did was read its own work and find it convincing.
Fluent writing feels like checked work. A paragraph that sounds right is not a proof.

**Verdict by label.** A handoff note says "[PROVEN]" or "[VERIFIED]" next to a claim.
The next session doesn't believe the label, and rightly so. It re-derives everything
from scratch, so the label saved no time. What would have saved time is the actual
evidence, small enough to check in a minute: the specific derivation, the log of the
build that compiled, the counterexample.

**The praise loop.** Put two AI agents in a collaboration and they often start
complimenting each other. "Great insight!" "Excellent point, building on your excellent
work…" Each message spends a third of its length on politeness. Worse, praise makes it
socially awkward, in whatever sense applies to models, to say "this is wrong."

**The audit loop.** The opposite failure. Tell an agent to review and it will find
*something*, because finding nothing feels like failing the task. It flags trivia,
rechecks things that don't matter, and generates a long list of minor issues that buries
the one that matters.

**The redo loop.** Agent A does work. Agent B, or the next session, doesn't trust it and
redoes it. Agent C redoes B's work. Nobody builds on anything. This is the most
expensive failure, and it follows directly from "verdict by label": if claims can't be
checked cheaply, they get rebuilt expensively.

**Phantom details.** The model describes what's in a file it never opened, or diagnoses a
bug in code it hasn't seen, with complete confidence. This happens with and without
tools. A chat model asked about a codebase will happily invent its structure.

**The average answer.** The first approach that comes to mind is the statistically
average one: the approach most commonly written about, not the best one. A web search
makes this worse, because the web is the average, and the search result displaces the
model's own better knowledge. The model knew a sharper approach and then searched its
way back to the mediocre one.

**Symptom fixing.** Something breaks, the model patches it, something else breaks, it
patches that. Each patch is reasonable alone. Nobody stops to ask whether the whole
approach is wrong.

**Discarding a broken idea too early.** An idea fails and gets thrown away. But ideas
that *almost* work are valuable. Finding exactly why it failed, the one missing
condition or the specific case that breaks it, is often worth more than the idea itself.
Discarding it throws that away.

All of these have been seen repeatedly in real long sessions. The list of causes below is
much more speculative.

---

## Part 3: Why would an intelligent system do something it knows is wrong?

Several hypotheses. Probably several are partly true at once.

**Hypothesis one: short-task training.** Most training rewards a good answer to one
question. Long sessions are a different world. Mistakes compound, context piles up, and
the right move is often to *stop* or *reconsider*, which short tasks rarely reward. If
training mostly rewards finishing and producing output, a model will lean toward
producing output even when stopping is better. *Status: plausible, and fits what we
observe, but untested here.*

**Hypothesis two: the context narrows the view.** Everything in the conversation so far
pulls the next step toward more of the same. Open files, earlier outputs and the current
plan act like a magnet. The model's broad knowledge of how experts would approach the
problem is still there, but the immediate context drowns it out. This is why one useful
trick is to ask the model, *before* it looks at anything, how an expert would approach
this type of problem. That draws out the broad knowledge before the narrow context takes
over. *Status: the trick seems to help in practice, but nobody has measured it
carefully.*

**Hypothesis three: politeness training.** Models are trained to be helpful and
agreeable to humans. Put two such models together and the agreeableness has no brake.
Each one is being "nice" to a user who happens to be another model. *Status: very
plausible, an easy explanation for the praise loop.*

**Hypothesis four: role literalism.** Tell a model "you are the reviewer" and it acts out
the role. Reviewers find problems, so it finds problems even when there aren't any that
matter. *Status: plausible, explains the audit loop.*

**Hypothesis five: no felt cost.** A human feels the cost of rerunning a two-hour
computation: boredom, tiredness, a deadline. A model doesn't feel time passing. Running
something again feels free from the inside. *Status: speculative but intuitive.*

**Hypothesis six: knowing isn't applying.** This is the deepest one. Knowing a rule when
asked about it and applying it in the moment may be different capacities. Humans have
the same gap: you know you shouldn't check your phone while driving. The difference
might be that humans built habits through repetition and consequences, and models
haven't had that kind of training for long-session behavior. *Status: speculative, but
if true, it says written rules alone won't fully work. You'd need the rule to fire at
the right moment.*

---

## Part 4: The boss's view is a position, not a talent

Now an important idea, one that comes from ordinary experience.

Picture a manager who walks past someone's desk, glances at the screen and says: "Wait,
why are you doing it that way?" The person at the desk, deep in the details, never saw
the problem. The manager saw it in five seconds.

Is the manager smarter? Not necessarily. The manager is in a different *position*: not
holding the details, not committed to the current path, not carrying the history of
small decisions that led here. That distance is what lets them see the big picture.

The claim, and it's a key one: **tunnel vision is a product of position, not ability.**
It happens to anyone deep in a task, human or AI. And the cure, a fresh view from
outside the details, doesn't require a smarter or different kind of mind. It requires a
mind that *isn't currently doing the task*.

If that's right, it has a big consequence for AI teams. You don't need a human
supervisor for the big-picture check. You need *another AI that is in the supervisor's
position*: one that sees the goal and a summary of what's been done, not every detail.
Same intelligence, same standard, different seat.

Note the balance here. The overseer needs *some* detail. Someone who knows nothing about
the task can't spot a wrong direction. But too much detail recreates the tunnel. The
right amount is probably: the goal, the current approach in a sentence or two, and what
has been tried and what happened. Not the full transcript.

*Status: the position argument is common sense and fits human experience well. Whether
AI overseers actually catch drift better than the working agent does, with the same
model, is untested. It's one of the first experiments worth running.*

---

## Part 5: One standard for everyone

A design principle worth stating plainly: **every participant is held to the same
standard, whatever their tools.**

Some AI systems are agents with tools: they can run code, search and read files. Others
are chat assistants that can only reason. It's tempting to write separate rules for each.
But consider:

- A model with tools tends to fail by *doing too much*: running instead of thinking,
  searching instead of recalling.
- A model without tools tends to fail by *claiming too much*: saying "verified" about
  something it only reasoned through, or describing files it can't see.

These are mirror images. Having tools doesn't excuse skipping thought, and lacking tools
doesn't excuse claiming certainty.

And here's the interesting part. A model *without* tools, if it knows how tool work goes
wrong, can be an excellent overseer for a model *with* tools. It's in the boss's position
by construction: it can't get absorbed in running things. It can look at a log of what the
tool-using agent did and say "you ran that search five times with no stated question" or
"you're patching symptoms." So the tool ethos belongs in the shared standard even for
models that never touch a tool. Everyone should know how the game is played, even if
they're not holding the controller.

The reverse works too. A tool-using agent can catch a reasoning model's phantom details
by actually opening the file.

---

## Part 6: Evidence, not labels

This is the most practical idea in the essay, and it comes from direct experience.

When one session hands work to the next, what convinces the next session? Not a label.
Writing "[PROVEN]" changes nothing. The next model checks anyway. The observation is
clear: models do not blindly trust tags in handoff notes, and that's correct behavior.

What *does* help is making the claim carry its own evidence, sized so checking takes
moments instead of half a session:

- **A proof on paper** should be written so each step can be checked locally: assumptions
  stated, cited results named exactly, no "clearly" hiding a gap.
- **A computation** should come with a record of the run: the command, the key output,
  and where the record lives. Here's a concrete example. If a claim says "this compiles
  in Lean" (Lean is a proof assistant), the next session shouldn't need to install Lean
  and recompile from scratch. AI sessions leave logs of their tool calls. If the next
  session can look up the log of the earlier session and find the actual build output,
  that's a cheap, convincing check. Pointing to the record beats repeating the verdict.
- **A refuted idea** should stay in the record, with the counterexample or short derivation
  that kills it. Deleting it means someone will try it again. Keeping it with only "this
  doesn't work" means someone has to take that on faith.
- **A judgment call** should come with its reasons and with what would change the
  judgment. A bare verdict gives the reader nothing to check.
- **What wasn't done** should be stated: what was skipped, what shortcuts were taken, and
  the fastest check that would settle each open point.

The goal: the next session can *confirm* instead of *redo*. That turns the redo loop into
building on each other's work.

*Status: the observation that labels don't help is first-hand. The claim that receipts and
checkable proofs actually cut re-derivation time is plausible, and measurable (see the
experiments below).*

---

## Part 7: How do you write a standard without bloating it?

There's a tension. A professional standard that gets loaded at the start of every task
costs space every time. Every line competes for attention. And some lines do harm: a rule
against a failure that never happens is noise, and noise makes the model skim.

So a principle: **only write rules against failures that have actually been observed,
more than once.** Not "this seems like something to avoid." Not a one-time fluke.
Observed and recurring.

The skill also shouldn't teach how to do mathematics, how to code or how to do research.
The model already knows those things well. Field-specific advice belongs in the skill
only where a specific failure in that field recurs, for example writing "checked up to N"
when you mean "proved."

But there's a hard problem underneath. When you add a rule and the failure still happens,
there are two different explanations:

1. **The rule was badly worded.** The model read it, tried to apply it, and the wording
   didn't capture what was meant.
2. **The rule wasn't read or recalled.** The model skimmed past it, or it didn't come to
   mind at the moment that mattered.

These need opposite fixes. Badly worded rules need rewording. Unread rules need to be
shorter, placed earlier, or tied to a trigger, a recognizable moment like the phrase "Let
me just…", so they fire when needed.

Telling the two apart requires keeping track. Which rules were tried, how they were
worded, what happened. Without that record, you end up rewording a rule that was fine
but unread, or cutting a rule that worked.

---

## Part 8: Research plans, from cheap to expensive

Now the concrete options. Each comes with a guess about whether it would work and what
could go wrong.

### Option A: A ledger of observed failures (very cheap)

Keep a simple record next to the standard: each rule, the failure it targets, where that
failure was seen (which session, roughly when), how often, and what wordings have been
tried. Any rule without an entry is a candidate for removal.

*Could it work?* Almost certainly helpful. It costs one line per incident. It's the
memory that expensive optimization methods use ("don't try this again, it failed"),
without the expensive optimization.

*What could go wrong?* It requires discipline to keep up. And what counts as "the same
failure" is a judgment call.

### Option B: Mine the logs you already have (cheap)

Long sessions have already happened. Their transcripts exist. The failures are already in
there: the praise loops, the reruns, the "verified" claims that weren't. An AI can read
recent session logs and pull out instances. That's free data on what actually goes
wrong, and how often.

*Could it work?* Yes, and it should probably come first, because it grounds everything
else in observation.

*What could go wrong?* Spotting a failure in a log takes judgment, and the model doing the
mining might share the same blind spots. Use a model in the overseer position, given the
goal and the log, asked specifically "where did this go off track?"

### Option C: Fork from the moment of failure (moderate, and the key trick)

This is perhaps the most promising idea for testing long-session behavior affordably.

The problem: long-session failures take hours to develop. Rerunning whole sessions to test
a rule is expensive and noisy.

The trick: you don't need to rerun the session. Take a real transcript up to *just
before* the failure happened. Add the rule to the context. Then generate a few
continuations from that exact point. Does the model still fall into the trap?

The long context that *caused* the habit is already there, so you test the rule in exactly
the conditions where it matters, for the cost of a short continuation. Five continuations
with the rule and five without gives a rough signal.

And it addresses the two-failure problem from Part 7. In each continuation, look at the
model's reasoning:
- If the reasoning *mentions or applies* the rule and still fails, the wording is the
  problem.
- If the reasoning *never touches* the rule, it wasn't read or recalled, and the
  placement or trigger is the problem.

*Could it work?* Reasoned but untested. There's a subtlety: whether adding a rule midway
through a transcript behaves the same as having it from the start. Probably not
identical. Possibly close enough to compare wordings against each other.

### Option D: A recall probe (cheap)

After a session, ask the model: "What does the standard say about rerunning tests?" or
"What does it say about labels in handoffs?" If it can't say, the rule wasn't absorbed.
If it can say but didn't follow it, that's the knowing-versus-doing gap again.

*Could it work?* Cheap and quick. It only tells you about recall, not behavior. Still
worth having.

### Option E: Ablation, or "remove it and see" (moderate)

Take one rule out. Does anything get worse? If not, the rule wasn't doing anything, and
it's costing context. This is the honest test of whether a rule earns its place, and
most standards are never tested this way.

*Could it work?* Yes, especially combined with Option C. Fork from a known failure point,
with and without the rule.

### Option F: The overseer experiment (moderate)

Directly test the position argument from Part 4. Same model, two roles. One does the work.
The other gets only the goal and a short running summary, and is asked at intervals:
"Is this still the right direction? What would you stop?" Measure how often the overseer
catches drift that the worker missed, compared with the worker asked the same question
about its own work.

*Could it work?* This is the experiment that tests the most interesting claim in the
essay. If the overseer, with the same intelligence and less detail, catches more, then
position matters and team design should use it.

*What could go wrong?* The overseer might be too detached and raise false alarms. The
amount of detail it gets is the dial to tune. Too little and it's useless, too much and
it's back in the tunnel.

### Option G: Measure what a handoff saves (moderate)

Give two fresh sessions the same handoff note, one written with labels ("proven,"
"verified") and one with evidence attached (checkable steps, records of runs, refutations
kept with their derivation). Measure how long each takes to reach a confident state, and
how much it redoes.

*Could it work?* Very measurable, and it directly tests Part 6.

### Option H: Rotating fresh eyes (speculative)

In a team of AI agents, periodically bring in an agent that has *not* seen the work, give
it the goal and the current state, and ask for the single biggest problem. Rotate who
plays this role.

*Could it work?* Plausible. It's cheap and uses the position effect. The risk is the audit
loop: the fresh agent feels it must find something. Countermeasure: explicitly allow
"nothing important is wrong" as a good answer, and ask for one issue at most.

### Option I: Banning the praise (speculative but easy)

For agent-to-agent communication, simply instruct: no compliments, no thanks, no
restating what the other said. Say what's wrong, what's new, or what's next.

*Could it work?* Probably reduces the visible praise. But the deeper question is whether
the *disposition* to agree survives, just expressed more quietly. Watch whether
disagreement actually increases, not just whether compliments decrease.

### Option J: Trigger phrases (speculative, promising)

Tie rules to the exact words that signal a failure is about to happen. "When you notice
yourself writing 'Let me just check', pause and ask what the check could change." "When
you write 'clearly', make sure the next sentence shows it."

*Could it work?* This targets the knowing-versus-doing gap directly, because the rule fires
at the moment of action, not just at the start of the session. It's the closest thing
to building a habit with words.

### Option K: Training (expensive, the real fix)

Ultimately, if these are learned dispositions, the deepest fix is training: rewarding
models for good long-session behavior, like stopping when stopping is right, leaving
checkable evidence, and disagreeing when warranted. Prompts are a patch. Training is the
cure.

*Could it work?* Very likely, given the resources. The logs from Option B and the
fork-point tests from Option C are exactly the kind of data such training would need.
So the cheap experiments aren't wasted even if training happens later.

---

## Part 9: Prompts worth trying right now

Some things to try without any setup:

1. **The advisor question, before starting:** "Before looking at anything: if you were
   advising an expert on this type of problem, what would you tell them? Then follow
   that advice."
2. **The outcome test, before any big step:** "What are the realistic outcomes of this
   step? Would any of them change what you do next? If not, skip it."
3. **The overseer check, mid-session:** Paste just the goal and a two-line summary into a
   fresh conversation and ask, "What's wrong with this direction?"
4. **The handoff rewrite:** Take an existing handoff note and ask, "Rewrite this so every
   claim carries evidence the next session could check in under a minute. No status
   labels."
5. **The broken-idea question:** When something fails: "Before we drop this: why did it
   almost work, and what exactly breaks it?"

---

## Part 10: Where this reasoning might be wrong

To close, the weak points, stated plainly so they can be challenged.

**Maybe the position argument is too simple.** Maybe the overseer catches drift not because
of position but because it's a separate conversation with a clean context, which is a
technical effect, not a social one. That would still be useful, but it would change the
design: the key ingredient would be a fresh context, not the supervisor role.

**Maybe rules can't fix dispositions at all.** If knowing and doing truly are separate,
written standards might move behavior only slightly, and only training will matter. The
fork-point experiments would reveal this: if no wording changes the continuation, that's
the answer.

**Maybe "observed failures only" is too strict.** Some failures are rare but disastrous.
A rule against a rare catastrophe might be worth its space. The ledger should perhaps
track severity, not just frequency.

**Maybe the mining is biased.** If the model that mines the logs shares the blind spots of
the model that made the mistakes, it will miss the same things. Using a different model,
or the overseer framing, helps but may not solve it.

**Maybe the failures change with each model.** What's observed with one model may not
happen with the next. A standard written against yesterday's failures could be outdated.
The ledger helps here too: rules can be retired when their failures stop showing up.

**Maybe this essay itself falls into the traps it describes.** It's long. It's full of
untested ideas presented with structure that makes them feel more solid than they are.
That's exactly "fluent prose standing in for checked work." The honest summary is that
the observations in Parts 1, 2 and 6 are first-hand. Nearly everything else is reasoned
speculation waiting for the experiments in Part 8.

---

## The short version

Smart models make obvious mistakes in long work not because they lack knowledge but
because momentum, context and politeness override what they know. The fixes worth testing:

- Shared standards for everyone, with or without tools.
- Overseers who see the big picture because of where they sit, not because they're
  smarter.
- Handoffs that carry evidence, not labels.
- Rules written only against failures actually seen.
- Testing those rules cheaply by restarting from the exact moment things went wrong.

None of this requires a human in every loop. It requires the right standard, the right
positions, and a record of what's been tried.
