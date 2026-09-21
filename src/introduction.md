# CS6501, Fall 2026

**Author:** Kevin Sullivan (<sullivan@virginia.edu>)

**Affiliation:** University of Virginia

**Pub Date:** April 15, 2026; updated 3/17/2026 (HSPD)

Draft For Comment

---

CS6501, Fall 2026

The course is in two parts. **Part I** — these 14 weeks — is a course in functional
programming that establishes the foundations for proof construction in predicate logic, set
theory and the theory of relations. **Part II shifts to proof construction itself**, building
directly on those foundations. This web page is
mirrored, modulo updates, by the Lean 4 project at [kevinsullivan/Lean4CS1](https://github.com/kevinsullivan/Lean4CS1).

## Why Lean, as of Fall 2026

There is exploding interest in the use of Lean for both formal mathematics and formal software
specification and verification. Two companion pages record where that stood at the start of this
semester: a [snapshot of fifteen organizations](./lean4-fall-2026.html) working in Lean beyond
research, and [the thirty sources](./lean4-fall-2026-sources.html) behind every figure and claim
in it.

## Design Commitments

Students should emerge fluent in computational and logical types.
Knowledge of proof construction is not an objective of Part I; that is the
subject of Part II. Part I's focus is instead on certified *computation*: writing functions,
stating their *specifications* as propositions, and having the machine
either verify or reject them as correct implementations or not. Except
in particular cases, all proof constructions are automated.

- Propositions are types from Week 0.
- `decide` produces proofs for decidable propositions.
- The logic progression (Bool/Prop → propositional → predicate → set/relation)
  is distributed across all 14 weeks.
- The `Float`/`DecidableEq` lesson appears in Week 7 as a topic.

Among the types introduced in the first thirteen weeks, the core ones —
function types (`→`), product types (`×`), sum types (`⊕`), `Unit`, `Empty`,
and the quantifier types `∀` and `∃` — were chosen precisely because they
are both fundamental programming types *and*, from another perspective,
precisely the logical connectives of the generalized predicate logic of Lean.

Types such as `Option`, `List`, and `BTree` are useful programming types
built on top of that foundation, but the Curry-Howard correspondence itself
lives in the core.  Week 14 does not introduce new material; it reveals that
Part I has established the entire foundation for the proof construction that
Part II takes up. We just flip the orientation from `Type` to `Prop`.  Each  
concept here  — data definitions, specifications, recursion, higher-order
functions, sets, relations, type classes — ports directly to the setting of
proof construction.

## Course Structure

| Unit | Weeks | Theme                                           |
| ---- | ----- | ----------------------------------------------- |
| 1    | 0–3   | Expressions, Functions, Recursion               |
| 2    | 4–7   | Algebraic Datatypes, Lists, Trees, Decidability |
| 3    | 8–9   | Higher-Order Functions, Specifications          |
| 4    | 10    | Sets and Relations                              |
| 5    | 11–12 | Abstract Types, Type Classes                    |
| 6    | 14    | Curry-Howard                                    |

## Building

```bash
lake build        # compile the Lean sources
make convert      # convert .lean → .md
make serve        # serve the book locally
```

## How to Study These Materials

The recommended setup is to view this rendered book alongside the Lean 4
source files in VS Code, with the Lean language server running so that
you see type information and error feedback in real time.

**Step 1 — Clone the repository and open it in VS Code.**

```bash
git clone https://github.com/kevinsullivan/Lean4CS1.git
cd Lean4CS1
code .
```

**Step 2 — Start the local book server.**  In the VS Code terminal
(`Ctrl+\`` or Terminal → New Terminal):

```bash
make serve
```

This builds the book and serves it on port 3000 *inside the container*. VS
Code forwards that to a port on your own machine, which is often a different
number — open the **PORTS** panel and use the **Local Address** it shows.
The server watches for changes and refreshes automatically.

**Step 3 — Open the browser panel inside VS Code.**

1. Open the Command Palette (`Cmd+Shift+P` on macOS, `Ctrl+Shift+P` on Windows/Linux).
2. Type **Simple Browser: Show** and press Enter.
3. Paste the **Local Address** from the **PORTS** panel as the URL.

**Step 4 — Arrange the panels side by side.**  Drag the Simple Browser
tab to the right half of the editor area.  Open the corresponding
`.lean` source file (e.g., `FPCourse/T01_ExpressionsFunctionsRecursion/W00_AlgebraicTypes.lean`)
in the left panel.  You now have the rendered prose on the right and the
live, type-checked Lean source on the left.

**Step 5 — Experiment.**  The most effective way to study is to read
a section in the book, then find the corresponding code in the `.lean`
file, hover over terms to inspect their types, and modify examples to
see what the Lean kernel accepts or rejects.  The exercises at the end
of each chapter are meant to be worked directly in the `.lean` file.

---

Copyright &copy; Kevin Sullivan. 2026.
