-- FPCourse/T01_ExpressionsFunctionsRecursion/W02_FunctionsSpecifications.lean
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Basic

/-! @@@
# Functions and Specifications

## The dual reading of →

The arrow `→` has two readings that are always simultaneously true.

**Computational reading**: `α → β` is the type of functions from `α` to `β`.
A term of this type takes an input of type `α` and returns an output of
type `β`.

**Logical reading**: `P → Q` (where `P Q : Prop`) is the type of proofs
that P *implies* Q.  A term of this type is a function that converts any
proof of P into a proof of Q.

These are not two different symbols.  They are one symbol with two
readings.  A function *is* an implication proof; an implication proof *is*
a function.  This identity is the beginning of the Curry-Howard
correspondence, which we will name explicitly in Week 14.
@@@ -/

namespace W02

/-! @@@
## 2.1  Defining functions
@@@ -/

-- Named function definition
def double (n : Nat) : Nat := n * 2
def square (n : Nat) : Nat := n * n

-- Anonymous function (lambda)
def double' : Nat → Nat := fun n => n * 2

/-! @@@
> **Checkpoint — defining functions.** `double n = n * 2` and `square n = n * n`.
> **Predict** both values below from the definitions, then check.
@@@ -/

#eval double 7    -- predict first
#eval square 6    -- predict first

-- Multi-argument functions are curried by default
def add3 (a b c : Nat) : Nat := a + b + c
-- add3 has type Nat → Nat → Nat → Nat
-- Applying one argument returns a function: Nat → Nat → Nat

-- Evaluation (β-reduction): each application substitutes the argument.
--   add3 1 2 3
--   ↝ (fun a b c => a + b + c) 1 2 3
--   ↝ 1 + 2 + 3                        (three β-reductions)
--   ↝ 6
#eval add3 1 2 3    -- 6
#eval (add3 1) 2 3  -- same: (add3 1) is a Nat → Nat → Nat waiting for two more args

/-! @@@
> **Checkpoint — currying.** `add3 : Nat → Nat → Nat → Nat`, so `(add3 10 20)` is itself
> a function still waiting for one `Nat`. **Predict** the value once the last argument
> arrives, then check.
@@@ -/

#eval (add3 10 20) 30    -- predict first

/-! @@@
## 2.2  → as implication: logical reading

When `P` and `Q` are propositions, `P → Q` is the claim that P implies Q.
A proof of `P → Q` is a function that takes any proof of P and returns a
proof of Q.  This is indistinguishable from an ordinary function — because
it *is* an ordinary function.
@@@ -/

-- A proof of P → Q is a term of type P → Q.
-- Here: "if n + 0 = n, then n = n + 0"
theorem add_zero_comm (n : Nat) : n + 0 = n → n = n + 0 :=
  fun h => h.symm

/-! @@@
> **Checkpoint — `→` as implication.** An implication between *decidable* propositions is
> itself decidable. In `(2 + 0 = 2) → (2 = 2 + 0)` the hypothesis holds and so does the
> conclusion. **Predict** the Boolean — and say why the implication is true — then check.
@@@ -/

#eval decide ((2 + 0 = 2) → (2 = 2 + 0))   -- predict first

-- Universal claims: ∀ n : Nat, P n
-- This is also a function type: (n : Nat) → P n
-- A proof supplies the function.
theorem add_zero_all : ∀ n : Nat, n + 0 = n :=
  Nat.add_zero

/-! @@@
> **Checkpoint — `∀` as a function type.** A proof of `∀ n, n + 0 = n` is a *function*
> sending each `n` to a proof. Over a *finite* list the claim is decidable. **Predict** the
> Boolean below, then check.
@@@ -/

#eval decide (∀ n ∈ ([0, 1, 2, 3] : List Nat), n + 0 = n)   -- predict first

-- The ∀ and → are the same thing: ∀ n, P n is (n : Nat) → P n
-- when P does not mention types not in scope.

/-! @@@
## 2.3  The design recipe

Every function in this course is designed using the following steps.
English descriptions are written as Lean *docstrings* (`/-- ... -/`
placed immediately before a definition) so the tooling surfaces them
in hover text.

| Step | Activity |
|------|----------|
| 0. Description | Write a `/-- docstring -/` saying what the function does in plain English. |
| 1. Signature | Write the name, argument types, and return type. |
| 2. Specification | Write a `∀` proposition over the signature expressing what the output must satisfy. |
| 3. Examples | Write `#eval` checks with `-- expected` comments; once `#eval` is familiar, strengthen to `example : f x = v := rfl`. |
| 4. Template | Write the function body shape from the input types. |
| 5. Code | Fill in the body. |
| 6. Check | Verify the compiler accepts both the definition and the specification. |

The description comes first so you understand *what* before *how*.
The signature must precede the specification — the spec names the
function, so the `def` must exist before the `theorem` can be stated.
@@@ -/

-- Example: doubling a number.

-- Step 0 — Description:
/-- `double'' n` returns twice `n`. -/
-- Step 1 — Signature + Steps 4/5 Template and code:
def double'' (n : Nat) : Nat := n + n

-- Step 3 — Examples (two forms):
-- Form 1: #eval with expected value in comment (explore interactively)
#eval double'' 0    -- 0
#eval double'' 5    -- 10
-- Form 2: rfl-based test (machine-verified; both sides evaluate to the same normal form)
example : double'' 0 = 0  := rfl
example : double'' 5 = 10 := rfl

-- Step 2 — Specification (stated after the def, since it names double''):
--   ∀ n : Nat, double'' n = n + n
-- Step 6 — Check (provided proof):
-- Evaluation: double'' n ↝ n + n (δ-reduction).  Both sides are identical.
theorem double''_spec : ∀ n : Nat, double'' n = n + n :=
  fun _ => rfl

/-! @@@
> **Checkpoint — `double''` and its spec.** `double''_spec` states `double'' n = n + n`.
> **Predict** the value below *from the spec* (not by re-deriving the body), then check.
@@@ -/

#eval double'' 7   -- predict from double''_spec

/-! @@@
## 2.4  Function composition
@@@ -/

-- ∘ is function composition: (f ∘ g) x = f (g x)
def double_then_square : Nat → Nat := square ∘ double

#eval double_then_square 3    -- square (double 3) = square 6 = 36

/-! @@@
> **Checkpoint — function composition.** `(square ∘ double) x = square (double x)` — inner
> function first. **Predict** the value below (double `5`, then square), then check.
@@@ -/

#eval double_then_square 5   -- predict:  square (double 5)

-- Composition and identity satisfy algebraic laws.
-- These are propositions about functions — logical types.
theorem comp_id (f : α → β) : f ∘ id = f := rfl
theorem id_comp (f : α → β) : id ∘ f = f := rfl
theorem comp_assoc (f : γ → δ) (g : β → γ) (h : α → β) :
    (f ∘ g) ∘ h = f ∘ (g ∘ h) := rfl

/-! @@@
## 2.5  Connectives as types

Logical connectives are type constructors.  A proposition built with a
connective has the same structure as a product or sum type in computation.

| Connective | Type constructor | Introduction |
|------------|-----------------|--------------|
| `P ∧ Q` | like `P × Q` | `And.intro : P → Q → P ∧ Q` |
| `P ∨ Q` | like `P ⊕ Q` | `Or.inl : P → P ∨ Q` |
| `¬P` | `P → False` | a function from P to absurdity |
| `P ↔ Q` | `(P → Q) × (Q → P)` | `Iff.intro` |

@@@ -/

-- ∧ introduction: supply proofs of both conjuncts
example : 1 < 2 ∧ 2 < 3 :=
  And.intro (by decide) (by decide)

/-! @@@
> **Checkpoint — `∧` (conjunction).** `1 < 2 ∧ 2 < 3` is true only when *both* conjuncts
> are. **Predict** the Boolean, then check.
@@@ -/

#eval decide (1 < 2 ∧ 2 < 3)   -- predict first

-- ∨ introduction: supply a proof of one disjunct
example : 1 = 1 ∨ 1 = 2 :=
  Or.inl rfl

/-! @@@
> **Checkpoint — `∨` (disjunction).** `1 = 1 ∨ 1 = 2` is true when *at least one* disjunct
> is — here the left. **Predict** the Boolean, then check.
@@@ -/

#eval decide (1 = 1 ∨ 1 = 2)   -- predict first

-- ¬P is P → False
example : ¬ (1 = 2) :=
  by decide

/-! @@@
> **Checkpoint — `¬` (negation).** `¬ (1 = 2)` unfolds to `(1 = 2) → False`; it holds
> exactly when `1 = 2` is false. **Predict** the Boolean, then check.
@@@ -/

#eval decide (¬ (1 = 2))   -- predict first

-- ↔ introduction: supply both directions
example : (1 + 1 = 2) ↔ (2 = 1 + 1) :=
  Iff.intro (fun h => h.symm) (fun h => h.symm)

/-! @@@
> **Checkpoint — `↔` (biconditional).** `(1 + 1 = 2) ↔ (2 = 1 + 1)` needs *both*
> directions to hold. **Predict** the Boolean, then check.
@@@ -/

#eval decide ((1 + 1 = 2) ↔ (2 = 1 + 1))   -- predict first

/-! @@@
## 2.6  Deriving terms from types

A term the compiler accepts is worth little if you found it by trial and error.
`#check` and the red squiggle are an *oracle* — they answer *accepted* or *rejected* —
but an oracle is not a *method*: it never tells you how to *arrive at* a term.
Type-directed derivation is the method.  The structure of the goal *type* dictates the
structure of the *term*, built top-down, each step forced or chosen for a stated
reason.  You should be able to **predict acceptance before you build**.

### Introduction and elimination

Each type constructor comes with a way to *build* a value (introduction) and a way to
*use* one (elimination) — the natural-deduction discipline we name in Week 14.

| Goal / hypothesis | Move | In Lean you write |
|---|---|---|
| goal `A → B` | →I: introduce the argument | `fun (a : A) => ?` — new goal `B`, with `a : A` |
| have `f : A → B`, `a : A` | →E: apply | `f a : B` |
| goal `A × B` | ×I: build a pair | `(?, ?)` — goals `A` and `B` |
| have `p : A × B` | ×E: project / match | `p.1`, `p.2`, or `match p with \| (a, b) => ?` |
| goal `A ⊕ B` | ⊕I: choose a side | `.inl ?` (goal `A`) or `.inr ?` (goal `B`) |
| have `s : A ⊕ B` | ⊕E: case-split | `match s with \| .inl a => ? \| .inr b => ?` |

Read the goal, pick the move its *outermost* constructor licenses, write that much of
the term, and read off the smaller goal(s) that remain.  Recall from §2.5 that `∧`
behaves like `×` and `∨` like `⊕`, so the *same* moves derive proofs of logical claims.

### How Lean shows you the goal

A hole `_` in a term is Lean *printing the goal*: it reports the expected type and the
local context — the "remaining goal" of your derivation.  Try it: `def e : Empty := _`
reports `⊢ Empty`.  In VS Code, type the hole and watch the **InfoView** shrink as you
fill each step.  Use the compiler as a *confirmer* of a step you predicted, not as a
blind search engine.

### The derivation trace

Record a derivation as a short trace.  The trace — not the final term — is the artifact
you are graded on; the final term is its by-product.  `RULE` at each step is one of
`→I`, `→E`, `×I`, `×E`, `⊕I`, `⊕E`, or "use `h`".
@@@ -/

/-! @@@
**Worked derivation 1 — `Nat → Nat`.**
```text
DERIVATION of  addSelf : Nat → Nat
  goal: Nat → Nat
  step 1 [→I]    fun (a : Nat) => ?   ⟶ goal: Nat, with a : Nat
  step 2 [use a] a + a                ⟶ closed (a is the only Nat in scope)
  ∎
```
@@@ -/

def addSelf : Nat → Nat := fun a => a + a

/-! @@@
> **Checkpoint — `addSelf` (derived).** The derivation closed with `a + a`. **Predict**
> `addSelf 21` — the by-product of the trace — then check.
@@@ -/

#eval addSelf 21   -- predict first

/-! @@@
**Worked derivation 2 — `(P → Q) → (Q → R) → (P → R)`.**  Composition; under the logical
reading, transitivity of implication — one derivation certifies both.
```text
  step 1 [→I]  fun (f : P → Q) => ?   ⟶ goal: (Q → R) → (P → R)
  step 2 [→I]  fun (g : Q → R) => ?   ⟶ goal: P → R
  step 3 [→I]  fun (p : P) => ?       ⟶ goal: R, with f, g, p
  step 4 [→E]  f p : Q
  step 5 [→E]  g (f p) : R            ⟶ closed
```
@@@ -/

def compose {P Q R : Type} : (P → Q) → (Q → R) → (P → R) :=
  fun f g p => g (f p)

/-! @@@
> **Checkpoint — `compose` (derived).** `compose f g p = g (f p)`. With `f = (· + 1)` and
> `g = (· * 2)`, **predict** `compose f g 3`, then check.
@@@ -/

#eval compose (fun n => n + 1) (fun n => n * 2) 3   -- predict:  g (f 3)

/-! @@@
**Worked derivation 3 — `A × B → B × A`.**
```text
  step 1 [→I]  fun (p : A × B) => ?   ⟶ goal: B × A, with p : A × B
  step 2 [×E]  p.1 : A,  p.2 : B
  step 3 [×I]  (p.2, p.1) : B × A     ⟶ closed
```
@@@ -/

def swapProd {A B : Type} : A × B → B × A :=
  fun p => (p.2, p.1)

/-! @@@
> **Checkpoint — `swapProd` (derived).** `swapProd (a, b) = (b, a)`. **Predict**
> `swapProd (1, 2)`, then check.
@@@ -/

#eval swapProd (1, 2)   -- predict:  (2, 1)

/-! @@@
**Worked derivation 4 — `A ⊕ B → B ⊕ A`.**  The goal `B ⊕ A` would call for ⊕I, but
which side is right depends on the input — so eliminate the hypothesis first.
```text
  step 1 [→I]  fun (s : A ⊕ B) => ?
  step 2 [⊕E]  match s with .inl a => ? | .inr b => ?   ⟶ two goals B ⊕ A
  step 3 [⊕I]  .inr a   (case inl)    ⟶ closed
  step 4 [⊕I]  .inl b   (case inr)    ⟶ closed
```
@@@ -/

def swapSum {A B : Type} : A ⊕ B → B ⊕ A :=
  fun s => match s with
    | .inl a => .inr a
    | .inr b => .inl b

/-! @@@
> **Checkpoint — `swapSum` (derived).** `swapSum (.inl a) = .inr a` — swapping an `inl`
> lands in `inr`. **Predict** the Boolean below, then check.
@@@ -/

#eval decide (swapSum (Sum.inl 1 : Nat ⊕ Nat) = Sum.inr 1)   -- predict first

/-! @@@
### Grading the trace

A derivation exercise is graded on the **trace**, not merely on whether the term
compiles.  Full credit: (1) name the correct rule at each step; (2) state the remaining
goal after each step; (3) close every goal by a hypothesis in scope.  A term that
compiles but whose trace mis-names a rule or skips a goal is *not* full credit — it may
be correct by luck.

### The inverse direction

Derivation *builds* a term from a type.  Its inverse *reads* a type to learn what
**every** inhabitant must do — *free theorems*, developed in Week 7 (§7.2).  Where a
type is fully polymorphic the derivation is *forced* and the free theorem is *total*:
`∀ α, α → α` has one inhabitant; `∀ α, α → α → α` has exactly two.  Building a term from
a type and reading what every term of a type must do are one skill in two directions.
@@@ -/

/-! @@@
## 2.7  Reading function specifications

When a function's type contains propositions, the type IS the specification.
The examples below show how to read proof-carrying function types.
@@@ -/

-- The type tells you: given a proof that the list is nonempty,
-- return the first element.  No runtime null check needed.
#check List.head   -- (l : List α) → l ≠ [] → α
-- (Actual Lean name may vary; the pattern is the point.)

-- The type tells you: given proofs about the index being in bounds,
-- return the element at that index.
#check List.get    -- (l : List α) → Fin l.length → α
-- Fin n is the type of natural numbers < n.  It IS the bounds proof.

/-! @@@
> **Checkpoint — a proof-carrying type.** `List.head` demands a proof the list is
> nonempty; `by decide` discharges it for a concrete list. **Predict** which element is
> returned below, then check.
@@@ -/

#eval ([10, 20, 30] : List Nat).head (by decide)   -- predict first

/-! @@@
## Exercises

Each exercise carries a banner — `[id] · competency · tier · level · target` — and, where
it asks you to build something, an **acceptance check**: paste it beneath your definition
in your own file and it must succeed.  `#guard` is silent on success and errors on
failure, so the compiler is your grader.  See `EXERCISE_CONVENTIONS.md` for the schema.
Do every **core** exercise; **stretch** exercises go deeper and are optional.

---

**[E2.1]** · *specification writing* · tier 1 · **core** · target `pred'`

Write `pred' : Nat → Nat` returning the predecessor, treating `0` as `0` (`match` on `0`
vs. `n + 1`).  State its specification as a `∀` proposition — *"`pred'` undoes successor:
`∀ n, pred' (n + 1) = n`, with `pred' 0 = 0`"* — then confirm on instances:

```lean
#guard pred' 0 = 0
#guard pred' 1 = 0
#guard pred' 5 = 4
#guard decide (∀ n ∈ ([0, 1, 2, 3, 10] : List Nat), pred' (n + 1) = n) = true
```

---

**[E2.2]** · *counterexample finding* · tier 1 · **core**

A student claims *"`double n = n + 2` for every `n`"* (`double` from §2.1).  It is
**wrong** — the two lines cross at a single point and disagree everywhere else.  Find
inputs where they differ and encode each witness so the check **succeeds** (it confirms
the two sides are unequal):

```lean
#guard double 5 ≠ 5 + 2
#guard double 0 ≠ 0 + 2
```

At which single `n` does `double n = n + 2` accidentally hold?  State the *correct* spec
of `double` in one line.

---

**[E2.3]** · *specification reading* · tier 2 (+ tier-3 reading) · **core**

Use `#check @And.intro` to read its type.  In one sentence each, say what a term of that
type is **computationally** (the constructor that builds a pair of proofs) and
**logically** (a proof of `P ∧ Q` from a proof of `P` and a proof of `Q`).  Then *read*
the provided proof `add_zero_comm := fun h => h.symm` (§2.2) and explain why `.symm`
closes the goal — do **not** author a proof of your own.  One confirmation that
`∧`-introduction lands in a true proposition:

```lean
#guard decide ((1 < 2) ∧ (2 < 3)) = true
```

---

**[E2.4]** · *decidability identification* · tier 1 · **core**

For each proposition, say **whether `decide` can close it and why** (finite domain?
decidable predicate?) *before* checking — the judgment is the point, not the tool-use:

(a) `(2 < 3) ↔ ¬(3 ≤ 2)`  (b) `(True ∧ True) ↔ True`  (c) `(True ∧ False) ↔ False`
(d) `¬ (True ∧ False)`  (e) `∀ n : Nat, n + 0 = n`

```lean
#guard decide ((2 < 3) ↔ ¬(3 ≤ 2)) = true
#guard decide ((True ∧ True) ↔ True) = true
#guard decide ((True ∧ False) ↔ False) = true
#guard decide (¬ (True ∧ False)) = true
-- (e) has no check on purpose: say why decide cannot close an unbounded ∀ over Nat,
--     and what unfolding of ¬ makes (d) the type (True ∧ False) → False.
```

---

**[E2.5]** · *specification writing* · tier 1 · **stretch** · target `max'`

Write `max' : Nat → Nat → Nat` returning the larger of two numbers, then state its
specification as a `Prop`: the result is `≥` **both** inputs *and* equals **one** of them.
Confirm on instances, including the tie `a = b`:

```lean
#guard max' 3 7 = 7
#guard max' 9 4 = 9
#guard max' 5 5 = 5
#guard decide (∀ a ∈ ([0, 3, 7] : List Nat), ∀ b ∈ ([0, 3, 7] : List Nat),
  max' a b ≥ a ∧ max' a b ≥ b ∧ (max' a b = a ∨ max' a b = b)) = true
```

*First step:* the spec is a conjunction of three clauses — write the `∀ a b`
proposition first, then read each clause off the English.  Effort: ~4 lines.

---

Deriving terms (§2.6).  For E2.6–E2.9 the **derivation trace** is the graded artifact;
the term is its by-product.  `RULE` at each step is one of `→I`, `→E`, `×I`, `×E`, `⊕I`,
`⊕E`, or "use `h`".  Recall from §2.5 that `∧` behaves like `×` and `∨` like `⊕`.

**[E2.6]** · *type-directed derivation* · tier 2 · **core** · target `andComm`

Derive `andComm : P ∧ Q → Q ∧ P` (with `P Q : Prop`).  Give the **derivation trace** in
the §2.6 format, then the term; state which rule closes each goal.  Effort: 2 trace steps
after the opening `→I`.  (No `#guard` here: the value is a *proof*, not data, so the trace
alone is graded.)

*First-step hint:* the outermost goal is an arrow `P ∧ Q → Q ∧ P`, so the first move is
forced (`→I`); then eliminate the hypothesis (`×E`) before building the swapped pair
(`×I`).

---

**[E2.7]** · *type-directed derivation* · tier 2 · **stretch** · target `curry`

Derive `curry : (A × B → C) → (A → B → C)` (with `A B C : Type`).  Give the **derivation
trace** then the term.  How many `→I` steps appear before the first elimination, and why?
Effort: ~4 trace steps.

```lean
#guard curry (fun (p : Nat × Nat) => p.1 + p.2) 3 4 = 7
#guard curry (fun (p : Nat × Nat) => p.1 * p.2) 6 7 = 42
```

*First-step hint:* the goal is an arrow into an arrow into an arrow — introduce all three
arguments (`f`, `a`, `b`) before you can build the `A × B` pair to feed `f`.

---

**[E2.8]** · *type-directed derivation* · tier 2 · **core** · target `orElim`

Derive `orElim : (A → C) → (B → C) → (A ⊕ B → C)` (with `A B C : Type`).  Give the
**derivation trace** then the term.  Name the step that must come **before** you can use
either function, and why.  Effort: ~4 trace steps.

```lean
#guard orElim (fun n => n + 1) (fun n => n * 10) (Sum.inl 5 : Nat ⊕ Nat) = 6
#guard orElim (fun n => n + 1) (fun n => n * 10) (Sum.inr 5 : Nat ⊕ Nat) = 50
```

*First-step hint:* after `→I` on the two functions and the sum, the sum's side is
unknown — `⊕E` (`match`) must come before you can apply `f` or `g`.

---

**[E2.9]** · *type-directed derivation · type reading (free theorems)* · tier 2 · **stretch**

Two directions on the same type `(A → B → C) → B → A → C` (with `A B C : Type`), no term
to submit:

(a) **Method:** which introduction- or elimination-step must come **first**, and which
hypothesis closes the final goal?

(b) **Free theorem (previewing Week 7 §7.2):** reading only the type, how many inhabitants
does it have when `A B C` are fully polymorphic, and why can the code not *invent* a `C`?
This is the inverse of (a): where the derivation is forced, the reading is total.
@@@ -/

end W02
