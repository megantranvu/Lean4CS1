# Exercise authoring conventions

*Status: draft. Reference implementation: `FPCourse/T02_InductiveTypes/W05_Lists.lean`.*

These conventions make every week's exercises self-checking, tagged, and auditable
for coverage — importing Software Foundations' organizational discipline without its
autograder or its proof-production stance. They realize the six changes from the
exercise-design analysis.

## 1. The banner

Every exercise opens with a one-line banner:

```text
**[id]** · *competency* · tier N (+ notes) · **level** · target `Name`
```

- **id** — `E<week>.<n>`, e.g. `E5.3`. Stable; cite it in solutions and grading.
- **competency** — one (or more) of the six assessed competencies:
  `specification writing` · `specification reading` · `type-directed derivation` ·
  `counterexample finding` · `decidability identification` · `type reading (free theorems)`.
- **tier** — the verification tier the task lands in (`VERIFICATION_TIERS.md`):
  tier 1 *decide-checkable*, tier 2 *type-guaranteed*, tier 3 *proof-carrying*.
  Note secondary tiers in parentheses, e.g. `tier 1 (+ tier-3 reading)`.
- **level** — `core` (everyone) or `stretch` (optional depth). Aim for ~4 core + ~2
  stretch per week.
- **target** — the Lean name the student must produce, when there is one (`myZip`,
  `headOr`); omit for pure-reading or judgment exercises.

## 2. Acceptance checks (compiler as grader)

Any exercise that asks the student to *build* something ships a fenced `lean` block
of `#guard` checks the student pastes beneath their definition:

```lean
#guard headOr 0 ([] : List Nat) = 0
#guard headOr 0 [7, 8, 9] = 7
```

`#guard` is silent on success and errors on failure, needs no `by` and no proof term,
and evaluates only decidable propositions — so it stays inside "the compiler is the
grader" and the course's no-`sorry` constraint and Part I's rule that a student is
never required to write a proof. The checks live in
the exercise *prose* (a fenced block), never as live code in the instructor file, so
the file keeps compiling and no answer is given away.

Rules for good checks:

- Cover the boundary cases the spec cares about (empty list, shorter/longer, the
  `min`/`max` corner), not just one happy path.
- Keep every check *decidable* — concrete literals with `DecidableEq` element types.
  Avoid `#guard` on an implication or an unbounded `∀`/`∃` unless the domain is a
  finite list (`List.decidableBAll` / `decidableBEx` make bounded quantifiers over a
  literal list decidable).
- For counterexample-finding, phrase the check as the *inequality that must hold*
  (`... ≠ ...`), so a correct witness makes it succeed.

## 3. Checkpoints (immediate reinforcement)

**Every major concept a chapter introduces gets a checkpoint** — each new function,
specification, decidability fact, or invariant, placed in the lesson body immediately
after the concept (not saved for the end block). A checkpoint is a *predict-then-check*
micro-task backed by a live `#eval`, so it compiles and the InfoView shows the answer.
Prompt the student to predict the value **and state why** before reading it. This closes
the feedback-loop gap that SF gets from interleaving, at almost no authoring cost.

**Format — a blockquote callout**, so checkpoints are visually separated from the main
text (mdBook renders a blockquote as a distinct left-bordered box). The prose label goes
in the callout; the live `#eval` follows immediately:

```text
/-! @@@
> **Checkpoint — <concept>.** <one or two sentences: predict what, and why, before
> reading the result>
@@@ -/

#eval <expression>   -- predict first
```

Rules:

- **One concept per checkpoint.** If a section introduces three functions, it gets three
  checkpoints (see Week 6 §6.2: `toList`, `height`, `member`). Bundle multiple `#eval`
  lines under one callout only when they illustrate the *same* concept (e.g. two Booleans
  for one membership test).
- **Bold the concept** in the label (`**Checkpoint — \`map\` preserves length.**`) so the
  book's contents are skimmable.
- Keep the expression **decidable / evaluable** and small; the point is a fast prediction,
  not a computation.
- Predict-then-check phrasing every time: name the spec or fact the student should predict
  *from* (`predict from length_append`), not just "run this."

## 4. Deliverable = the derivation, not the term

For `type-directed derivation` exercises the graded artifact is the **derivation
trace** (Week 2 §2.6 format), not merely a term that compiles. Ask for the
trace explicitly, and give a *first-step hint* naming the introduction/elimination
move to start with, plus an **effort bound** (`~4 trace steps, 3 lines`). The `#guard`
checks confirm the by-product; the trace shows the method.

## 5. No "prove" leak

The course does not assess proof production, so no exercise may say "prove X." Rewrite
any such prompt into one of:

- **spec-writing + instance check** — state the property as a `Prop`, confirm it on
  decidable instances with `#guard`/`decide` (tier 1); or
- **tier-3 reading** — read the *provided* proof (e.g. `List.mem_append`) and explain
  a step, without authoring a proof.

`E5.1` shows the rewrite of the former Week-5 "Prove it using `List.mem_append`."

## 6. Coverage audit

Each week's exercise set should:

- exercise **≥ 4 of the 6 competencies**, and include **at least one
  counterexample-finding** item (the historically under-served competency);
- turn `decide` from *tool-use* ("use decide to verify…") into *judgment* ("does
  decide close this, and why") wherever `decidability identification` is the point;
- span **at least two tiers**, with tier-3 tasks limited to *reading* provided proofs.

A quick per-week audit table (competency × exercise) makes gaps visible; the flat
"5 prose items, no tags" format hid them.

## Fan-out checklist (per remaining week)

1. Banner every exercise (id, competency, tier, level, target).
2. Add `#guard` acceptance blocks to every build exercise; cover boundary cases.
3. Split into core/stretch; add effort bounds + first-step hints to the hard ones.
4. Seed 1–2 predict-then-check checkpoints in the body.
5. Rewrite every "prove" prompt per §5; add a counterexample item if none exists.
6. Run the §6 coverage audit; fill the gaps.
