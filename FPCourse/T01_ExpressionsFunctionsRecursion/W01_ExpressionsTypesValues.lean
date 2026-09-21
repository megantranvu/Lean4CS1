-- FPCourse/T01_ExpressionsFunctionsRecursion/W01_ExpressionsTypesValues.lean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Basic

/-! @@@
# Expressions, Types, and Values

## The central idea of this course

Every expression in Lean has a *type*.  Types do two jobs at once.

- **Computational types** classify data: `Nat`, `Bool`, `String`,
  `Nat × Bool`.  A value of a computational type can be evaluated.

- **Logical types** (also called *propositions*) classify *proofs*.
  A value of a logical type is a *proof* that the claim holds.

These two jobs are performed by the same language using the same
syntax.  That identity — programs and proofs living in one world — is
the deepest idea in the course.  You will see it demonstrated in every
week that follows.  By Week 14 you will have a name for it.
@@@ -/

namespace W01

/-! @@@
## 1.1  Computational types
@@@ -/

-- Every literal has a type.  Use #check to inspect it.
#check (42 : Nat)        -- Nat
#check (true : Bool)     -- Bool
#check ("hello" : String)

-- Functions have arrow types.
#check Nat.succ          -- Nat → Nat
#check Nat.add           -- Nat → Nat → Nat

-- #eval evaluates an expression to its normal form by reduction.
-- Nat.succ 7   ↝ 8        (successor of 7, by definition of Nat.succ)
-- Nat.add 3 4  ↝ 7        (addition, by recursive definition of Nat.add)
-- true && false ↝ false   (β-reduction: true && b ↝ b)
#eval Nat.succ 7         -- 8
#eval Nat.add 3 4        -- 7
#eval true && false      -- false  (Bool operations)

/-! @@@
> **Checkpoint — `Nat.add` reduces.** `Nat.add` is defined by recursion, so an application
> reduces to a single normal form.  **Predict** that normal form of `Nat.add 5 4` — before
> reading the result — then check.
@@@ -/

#eval Nat.add 5 4        -- predict first

/-! @@@
> **Checkpoint — Bool operators.** `&&` and `||` are *runnable* two-valued operations
> (β-reduction, not logic).  **Predict** the value of `true && (false || true)`, then check.
@@@ -/

#eval (true && (false || true))   -- predict first

/-! @@@
## 1.2  The Bool / Prop distinction

`Bool` is a two-element computational type: values `true` and `false`.
It is the type of the result of a test you can *run*.

`Prop` is the type of *logical claims*.  A term of type `P : Prop` is
a *proof* that P holds.  `Prop` is not two-valued; some propositions
have no proof (they are false), some have many proofs.

**This is the most important type-level distinction in Lean.**
@@@ -/

-- Bool: a computed result.
#eval (2 == 3 : Bool)       -- false  (uses BEq instance)
#eval (2 < 5 : Bool)        -- true   (uses DecidableLT)

/-! @@@
> **Checkpoint — a `Bool` test.** `==` and `<` on `Nat` return a `Bool` you can *run*.
> **Predict** the value of `(4 == 4 && 2 < 1 : Bool)` — one conjunct is false — then check.
@@@ -/

#eval (4 == 4 && 2 < 1 : Bool)   -- predict first

-- Prop: a logical claim.
#check (2 = 3 : Prop)       -- 2 = 3 : Prop
#check (2 < 5 : Prop)       -- 2 < 5 : Prop
#check (∀ n : Nat, n + 0 = n)   -- Prop
#check (∃ n : Nat, n > 100)     -- Prop

-- A proof of a Prop is a term of that type.
-- `rfl` proves `a = b` when both sides evaluate to the same normal form.
-- Evaluation: 2 + 2 ↝ 4, and the right side is already 4.  Same normal form.
-- Evaluation: Nat.succ 7 ↝ 8, and the right side is already 8.
example : 2 + 2 = 4 := rfl      -- both sides evaluate to 4
example : Nat.succ 7 = 8 := rfl  -- both sides evaluate to 8

/-! @@@
> **Checkpoint — `rfl` and normal forms.** `rfl` proves `a = b` exactly when both sides
> reduce to one normal form.  **Predict** the normal form of `Nat.succ 7`, then check that it
> is the `8` that makes the `example` above type-check.
@@@ -/

#eval Nat.succ 7   -- predict first

/-! @@@
## 1.3  `decide`: mechanically proving decidable propositions

Some propositions are *decidable*: there is an algorithm that always
produces either a proof or a refutation.  For those propositions, the
term `decide` acts as an automatic proof producer.

`decide` is a *term*, not a command.  It inhabits a type `P : Prop`
whenever `P` has a `Decidable` instance and reduces to `true`.  The
compiler checks this at elaboration time.  If `P` reduces to `false`,
the file fails to compile.

This is mechanical verification in its most direct form: the claim is
part of the type, and the compiler certifies it.
@@@ -/

-- Evaluation: `decide` evaluates the decision procedure for the proposition.
-- For each claim, Lean evaluates both sides and checks the result.
-- 2 + 2 ↝ 4, so 2 + 2 = 4 is confirmed.
-- 3 ↝ 3 and 5 ↝ 5, they differ, so ¬(3 = 5) is confirmed.
example : 2 + 2 = 4 := by decide
example : ¬ (3 = 5) := by decide
example : 2 < 100 := by decide
example : 10 % 3 = 1 := by decide

/-! @@@
> **Checkpoint — `decide`.** `decide` certifies a decidable `Prop` by *running* its
> decision procedure.  **Predict** whether `¬ (5 * 5 = 26)` is `true` (what is `5 * 5`?),
> then check.
@@@ -/

#eval decide (¬ (5 * 5 = 26))   -- predict first

-- decide on a list: ∀ over a finite collection is decidable
-- when the predicate is decidable.
example : ∀ x ∈ ([1, 2, 3] : List Nat), x < 10 := by decide
example : ∃ x ∈ ([1, 2, 3] : List Nat), x > 2  := by decide

/-! @@@
> **Checkpoint — `decide` on a finite list.** A *bounded* `∀ x ∈ [...]` over a literal list
> is decidable.  **Predict** the Boolean below — note the bound is `< 3`, and `3` is in the
> list — then check.
@@@ -/

#eval decide (∀ x ∈ ([1, 2, 3] : List Nat), x < 3)   -- predict first (note the 3)

-- If the claim is FALSE, the file will not compile.
-- Uncomment the next line to see the error:
-- example : 2 + 2 = 5 := decide

/-! @@@
## 1.4  Product types

A product type `α × β` pairs a value of type `α` with a value of type `β`.
@@@ -/

def myPair : Nat × Bool := (7, true)

#check myPair.1    -- Nat
#check myPair.2    -- Bool
#eval  myPair.1    -- 7
#eval  myPair.2    -- true

/-! @@@
> **Checkpoint — product projections.** `.1` and `.2` extract the two components.
> **Predict** the *swapped* pair `(myPair.2, myPair.1)` — its type is `Bool × Nat` — then
> check.
@@@ -/

#eval (myPair.2, myPair.1)   -- predict first

-- Nested products
def triple : Nat × Bool × String := (3, false, "hi")
#eval triple.1          -- 3
#eval triple.2.1        -- false
#eval triple.2.2        -- "hi"

/-! @@@
> **Checkpoint — nested products.** `Nat × Bool × String` nests as `Nat × (Bool × String)`,
> so `triple.2` is a pair and `triple.2.1` reaches into it.  **Predict** `triple.2.1`, then
> check.
@@@ -/

#eval triple.2.1   -- predict first

/-! @@@
## 1.5  Proof-carrying types: a first look

Here is a function that divides two natural numbers.  The *type*
of the second argument includes a condition: a proof that the divisor
is nonzero must be supplied by the caller.

```lean
def safeDiv (a : Nat) (b : Nat) (_h : b ≠ 0) : Nat := a / b
```

The type `b ≠ 0` is a proposition — a logical type.  Calling
`safeDiv` does not just pass a number; it passes a *proof* that the
number is nonzero.  The compiler enforces this before the program runs.

This pattern — conditions embedded in types, enforced at compile time —
is what we mean by *proof-carrying types*.  You will see it everywhere
from Week 2 onward.
@@@ -/

-- `_h` is never used in the body: the proof is a *precondition* the caller must
-- supply, not data the computation consumes.  A leading underscore is how Lean
-- marks a binder as deliberately unused.
def safeDiv (a : Nat) (b : Nat) (_h : b ≠ 0) : Nat := a / b

-- To call safeDiv we must supply a proof that the divisor ≠ 0.
-- For a concrete nonzero literal, `decide` produces the proof.
#eval safeDiv 10 2 (by decide)   -- 5
#eval safeDiv 17 3 (by decide)   -- 5

/-! @@@
> **Checkpoint — proof-carrying `safeDiv`.** The third argument `_h : b ≠ 0` is a *proof*
> the caller must supply; `by decide` manufactures it for a concrete nonzero divisor.
> **Predict** `safeDiv 20 4 (by decide)`, then check.  (`by decide` is allowed here — it only
> builds the nonzero proof.)
@@@ -/

#eval safeDiv 20 4 (by decide)   -- predict first


-- Attempting safeDiv 10 0 would require a proof of 0 ≠ 0,
-- which is false.  `decide` would refuse, and the file would
-- not compile.

/-! @@@
## 1.6  Type derivation rules (summary)

| Syntax | Type |
|--------|------|
| `n : Nat` | `Nat` |
| `b : Bool` | `Bool` |
| `(a, b) : α × β` | `α × β` |
| `f : α → β`, `x : α` | `f x : β` |
| `P : Prop`, proof `h : P` | `h : P` |
| `decide` (when `[Decidable P]`) | `P` |

Reading types is the foundational skill of this course.
Every week adds new type constructors to this table.

## Exercises

Each exercise carries a banner — `[id] · competency · tier · level · target` — and,
where it asks you to build something, an **acceptance check**: paste it beneath your
definition in your own file and it must succeed.  `#guard` is silent on success and
errors on failure, so the compiler is your grader.  See `EXERCISE_CONVENTIONS.md` for
the schema.  Do every **core** exercise; **stretch** exercises go deeper and are
optional.

---

**[E1.1]** · *type reading (free theorems)* · tier 2 · **core**

Use `#check` on `Nat.add`, `Nat.mul`, and `String.append`.  For each, write in plain
English what the type says the function does, whether it is *curried*, and how many
arguments it takes.  Then read one type you were *not* given a body for: a function of
type `∀ α, α → α → α`, polymorphic in `α`.  State one thing every inhabitant can do with
its two inputs and one thing it **cannot** do (can it manufacture a fresh `α`? compare
the two?).  This previews the free theorems of Week 7 (§7.2).  No code to submit.

---

**[E1.2]** · *specification writing* · tier 1 · **core** · target `myStrNat`

Define a product type pairing a `String` with a `Nat`, and a value
`myStrNat : String × Nat := ("lean", 4)`.  Then **state, as a `Prop`**, the specification
*"the first component is `\"lean\"` and the second is positive,"* and confirm it on your
instance.  The projections `.1` and `.2` are your spec vocabulary (§1.4).

```lean
-- def MyStrNatSpec : Prop := myStrNat.1 = "lean" ∧ myStrNat.2 > 0
#guard myStrNat.1 = "lean"
#guard myStrNat.2 = 4
#guard decide (myStrNat.1 = "lean" ∧ myStrNat.2 > 0) = true
```

---

**[E1.3]** · *decidability identification* · tier 1 · **core**

For each proposition, say **whether `decide` can close it and why** — is it atomic or
built from connectives (`∧`, `¬`), and does its type carry a decision procedure? — *then*
check only the ones that are decidable:

(a) `17 * 23 = 391`  (b) `100 < 200 ∧ 200 < 300`  (c) `¬ (5 * 5 = 26)`
(d) `(1.0 : Float) = 1.0`

```lean
#guard decide (17 * 23 = 391) = true
#guard decide (100 < 200 ∧ 200 < 300) = true
#guard decide (¬ (5 * 5 = 26)) = true
-- (d) has no check on purpose: say why `decide` cannot close Float equality.
--     (Hint: what would DecidableEq Float have to certify about NaN?  §1.2, revisited Week 7.)
```

#eval decide Float.NaN
---

**[E1.4]** · *counterexample finding* · tier 1 · **core** · target `subCancelCex`

A student claims *"for all naturals `a b`, `a - b + b = a`."*  On `Nat`, subtraction is
**truncated** (`3 - 5 = 0`), so the claim is **wrong**.  Find concrete inputs witnessing
the mismatch and encode the witness as the *inequality that must hold*, so the check
**succeeds**:

```lean
#guard 3 - 5 + 5 ≠ 3
```

*First-step hint:* pick `a < b` so the subtraction underflows to `0`.  Then state, in one
line, the side condition under which the original equation **does** hold.  Effort: 1 line.

---

**[E1.5]** · *type-directed derivation* · tier 2 · **stretch** · target `swapPair`

Derive `swapPair : Nat × Bool → Bool × Nat` (swap the two components).  Produce a
**derivation trace** in the Week 2 §2.6 format — the trace is the graded artifact — then
the `def`.  *First-step hint:* the input is a product, so *eliminate* it with `.1` and
`.2` (×-elimination), then *introduce* the target pair in swapped order (×-introduction).
Effort: ~3 trace steps, 1 line of code.  (The trace format is introduced next week; this
previews it.)

```lean
#guard swapPair (7, true) = (true, 7)
#guard swapPair (0, false) = (false, 0)
```

---

**[E1.6]** · *specification reading* · tier 3 (reading) · **stretch**

Read the proof-carrying type of `safeDiv` (§1.5): `(a b : Nat) → (_h : b ≠ 0) → Nat`.  Do
**not** author any proof.  Explain (a) what the caller must supply beyond two numbers, and
(b) why `safeDiv 10 0 (by decide)` fails to compile — trace the failure to the proof
obligation `0 ≠ 0` that has no inhabitant.  Then confirm the two working calls:

```lean
#guard safeDiv 10 2 (by decide) = 5
#guard safeDiv 17 3 (by decide) = 5
```
@@@ -/

end W01
