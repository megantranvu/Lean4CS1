-- FPCourse/T02_InductiveTypes/W04_AlgebraicDatatypes.lean
import Mathlib.Data.Option.Basic
import Mathlib.Logic.Basic

/-! @@@
# Algebraic Datatypes

## Sum types and product types

Lean's `inductive` keyword lets us define new types by listing their
*constructors*.  The resulting type is either a *sum* (one of several
alternatives) or a *product* (bundling several fields) — or both.

These are called *algebraic* datatypes because they obey the same
algebraic laws as sums and products of numbers: a type with `n` values
of type A and `m` values of type B as alternatives has `n + m` values.
@@@ -/

namespace W04

/-! @@@
## 4.1  Enumeration types (pure sums)
@@@ -/

inductive Direction where
  | North | South | East | West
deriving Repr, DecidableEq

#eval Direction.North      -- Direction.North
example : Direction.North ≠ Direction.South := by decide

/-! @@@
> **Checkpoint — `Direction` has `DecidableEq`.** `deriving DecidableEq` makes every pair
> of constructors comparable, so `decide` can settle any (in)equality between them.
> **Predict** the Boolean below — are `North` and `South` distinct? — then check.
@@@ -/

#eval decide (Direction.North ≠ Direction.South)   -- predict first

/-! @@@
## 4.2  Record types (pure products)
@@@ -/

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }

/-! @@@
> **Checkpoint — record projection.** A record bundles named fields; projection reads one
> back. **Predict** the value of `origin.x` from the definition of `origin`, then check.
@@@ -/

#eval origin.x   -- predict first

/-! @@@
## 4.3  Option: the prototypical proof-carrying type

`Option α` is either `none` (no value) or `some a` (a value `a : α`).
It is Lean's answer to null.

But notice: `Option.get` does not simply hope the value is present.
Its type *requires* a proof:

```lean
def Option.get : (o : Option α) → o.isSome = true → α
```

The caller must supply evidence before the function will run.
This is the proof-carrying pattern from Week 1, now applied to a
realistic data type.
@@@ -/

-- Option.get requires a proof.
def safeHead (xs : List α) (h : xs ≠ []) : α :=
  xs.head h

-- For concrete lists, `decide` produces the proof.
#eval safeHead [1, 2, 3] (by decide)    -- 1

-- Option.map: lift a function into an optional context
-- Specification: ∀ f o, (Option.map f o).isSome = o.isSome
theorem option_map_isSome (f : α → β) :
    ∀ o : Option α, (Option.map f o).isSome = o.isSome :=
  fun o => Option.recOn o rfl (fun _ => rfl)

/-! @@@
> **Checkpoint — `Option.map` preserves `isSome`.** By `option_map_isSome`, mapping can
> neither create nor destroy the value's presence. **Predict** both Booleans, then check.
@@@ -/

#eval (Option.map (· + 1) (some 3)).isSome              -- predict from option_map_isSome
#eval (Option.map (· + 1) (none : Option Nat)).isSome   -- predict

/-! @@@
## 4.4  ∀ and ∃ in datatype specifications

When we define a new type, its specifications typically quantify over
all values of that type.  Here is the vocabulary:

| Symbol | Reading | Introduction form |
|--------|---------|-------------------|
| `∀ x : T, P x` | "for all x of type T, P holds of x" | supply a function `fun x => proof_of_P_x` |
| `∃ x : T, P x` | "there exists x of type T such that P holds" | `⟨witness, proof⟩` |

@@@ -/

-- ∀ example: a property of all options
theorem none_map_always_none (f : α → β) :
    Option.map f none = none :=
  rfl

/-! @@@
> **Checkpoint — `Option.map` of `none`.** `none_map_always_none` says mapping any `f`
> over `none` yields `none`. **Predict** the value below (not just its `isSome`), then check.
@@@ -/

#eval (Option.map (· + 1) (none : Option Nat))   -- predict from none_map_always_none

-- ∃ example: witness a specific value satisfying a property
example : ∃ n : Nat, n > 100 := ⟨101, by decide⟩

private def factorial' : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial' n

example : ∃ n : Nat, factorial' n > 1000 :=
  ⟨7, by decide⟩

/-! @@@
> **Checkpoint — witnessing `∃`.** The proof above offers `7` as the witness. **Predict**
> the Boolean below — is `factorial' 7` really over `1000`? — then check the witness works.
@@@ -/

#eval decide (factorial' 7 > 1000)   -- predict first

/-! @@@
## 4.5  Recursive types: expressions

A *recursive* inductive type refers to itself in its constructor
arguments.  This is how we build trees, lists, and other inductively
structured data.
@@@ -/

inductive Expr where
  | num  : Int → Expr
  | add  : Expr → Expr → Expr
  | mul  : Expr → Expr → Expr
  | neg  : Expr → Expr
deriving Repr

-- Evaluation by structural recursion on Expr.
-- The function is named `eval` deliberately: it IS evaluation —
-- the process of reducing an expression tree to its integer value.
def Expr.eval : Expr → Int
  | .num n    => n
  | .add e₁ e₂ => e₁.eval + e₂.eval
  | .mul e₁ e₂ => e₁.eval * e₂.eval
  | .neg e    => -e.eval

-- Evaluation trace: Expr.eval (.add (.num 3) (.mul (.num 4) (.num 5)))
--   ↝ (.num 3).eval + (.mul (.num 4) (.num 5)).eval    -- add clause
--   ↝ 3 + (.mul (.num 4) (.num 5)).eval                -- num clause
--   ↝ 3 + ((.num 4).eval * (.num 5).eval)              -- mul clause
--   ↝ 3 + (4 * 5)                                      -- num clause ×2
--   ↝ 3 + 20 ↝ 23                                      -- arithmetic
#eval Expr.eval (.add (.num 3) (.mul (.num 4) (.num 5)))  -- 23

/-! @@@
> **Checkpoint — `Expr.eval` on `neg`.** `eval` recurses into subexpressions; the `neg`
> clause negates its operand's value. **Predict** the integer below, then check.
@@@ -/

#eval Expr.eval (.neg (.add (.num 2) (.num 3)))   -- predict first

-- Specification: eval distributes over add.
-- Evaluation: (.add e₁ e₂).eval ↝ e₁.eval + e₂.eval by the add clause.
-- Both sides are definitionally equal, so rfl applies.
theorem eval_add (e₁ e₂ : Expr) :
    (Expr.add e₁ e₂).eval = e₁.eval + e₂.eval :=
  rfl

/-! @@@
> **Checkpoint — `eval_add`.** `eval_add` states `(add e₁ e₂).eval = e₁.eval + e₂.eval`,
> and it holds by `rfl`. **Predict** the Boolean below *from that spec* (not by computing),
> then check.
@@@ -/

#eval decide (Expr.eval (.add (.num 3) (.num 4)) = Expr.eval (.num 3) + Expr.eval (.num 4))   -- predict from eval_add

/-! @@@
## 4.6  The template principle

Every inductive type `T` has a corresponding *elimination principle*:
to define a function from `T`, provide one clause per constructor.
The types of the clauses are determined by the constructor signatures.

For `Expr`:
- A clause for `num n` — has access to `n : Int`
- A clause for `add e₁ e₂` — has access to both subexpressions and
  their recursively computed results
- A clause for `mul e₁ e₂` — same
- A clause for `neg e` — access to `e` and its result

This is the *template principle*: the type tells you the shape of the
function.

## Exercises

Each exercise carries a banner — `[id] · competency · tier · level · target` — and,
where it asks you to build something, an **acceptance check**: paste it beneath your
definition in your own file and it must succeed.  `#guard` is silent on success and
errors on failure, so the compiler is your grader.  See `EXERCISE_CONVENTIONS.md` for
the schema.  Do every **core** exercise; **stretch** exercises go deeper and are
optional.

---

**[E4.1]** · *type-directed derivation* · tier 2 · **core** · target `numSides`

Define `inductive Shape` with `Circle (radius : Float)`, `Rectangle (width height :
Float)`, and `Triangle (base height : Float)`.  Then derive `numSides : Shape → Nat`,
the count of straight sides (`Circle` 0, `Triangle` 3, `Rectangle` 4).  The graded
artifact is a **derivation trace** (Week 2 §2.6): show how the template principle (§4.6)
forces one clause per constructor and fixes the data each clause may use.  *First-step
hint:* eliminate the `Shape` argument with a `match` — its three constructors give three
clauses.  Effort: ~3 trace steps, 5 lines of code.

```lean
#guard numSides (Shape.Circle 5.0) = 0
#guard numSides (Shape.Rectangle 2.0 3.0) = 4
#guard numSides (Shape.Triangle 1.0 1.0) = 3
```

---

**[E4.2]** · *specification writing* · tier 1 (+ decidability identification) · **core** · target `area`, `AreaCircleSpec`

Define `area : Shape → Float` (`Circle r ↦ Float.pi * r * r`, `Rectangle w h ↦ w * h`,
`Triangle b h ↦ 0.5 * b * h`).  State the circle specification as a `Prop`:

```lean
-- def AreaCircleSpec : Prop := ∀ r : Float, area (Shape.Circle r) = Float.pi * r * r
```

Then answer in one line: **why does this exercise ship no `#guard` acceptance check for
`area`?**  Name the type class `#guard`/`decide` needs and the type (see §4.2 and the
Float discussion) that lacks it.  The judgment — not a passing check — is the deliverable
here.

---

**[E4.3]** · *counterexample finding* · tier 1 · **core** · target `mulNotSum`

A student claims *"`Expr.eval (.mul a b) = Expr.eval a + Expr.eval b`"* — confusing `mul`
with `add`.  It is **wrong**.  Find a concrete `mul` expression witnessing the mismatch
and encode it as the inequality that must hold, so the check **succeeds**:

```lean
#guard Expr.eval (.mul (.num 3) (.num 4)) ≠ Expr.eval (.num 3) + Expr.eval (.num 4)
```

Then state the *correct* one-line spec for `mul` (the `eval_mul` analogue of `eval_add`,
§4.5).

---

**[E4.4]** · *specification writing* · tier 1 · **core** · target `MyExpr`, `MyExpr.eval`

The `Expr` of §4.5 has no subtraction.  Define your own `inductive MyExpr` with at least
`num : Int → MyExpr`, `add : MyExpr → MyExpr → MyExpr`, and `sub : MyExpr → MyExpr →
MyExpr`; give `MyExpr.eval : MyExpr → Int` extending §4.5 with a `sub` clause.  State the
subtraction spec as a ∀ proposition — `∀ a b, (MyExpr.sub a b).eval = a.eval - b.eval` —
then confirm it on instances (mind the negative-result boundary):

```lean
#guard MyExpr.eval (.sub (.num 10) (.num 3)) = 7
#guard MyExpr.eval (.sub (.num 3) (.num 10)) = -7
#guard MyExpr.eval (.add (.num 5) (.sub (.num 2) (.num 8))) = -1
```

*First-step hint:* copy the four `Expr.eval` clauses of §4.5 and add `.sub a b ↦ a.eval -
b.eval`.  Effort: ~6 lines of code.

---

**[E4.5]** · *specification writing (∃ witness)* · tier 1 · **stretch** · target `answer`

Rewrite the old "prove there exists an `Expr` that evaluates to 42" *without* producing a
proof.  Define a witness `answer : Expr` and let the compiler confirm it (tier 1); the
existential `∃ e : Expr, Expr.eval e = 42` is then witnessed by `⟨answer, by decide⟩` —
which you *read*, not author.

```lean
#guard Expr.eval answer = 42
```

*First-step hint:* any tree of `num`/`add`/`mul`/`neg` whose value is 42 works — e.g.
combine `add` and `mul` of `num`s.

---

**[E4.6]** · *type reading (free theorems)* · tier 2 · **stretch**

Look **only** at the type `Option.map : (α → β) → Option α → Option β`, polymorphic in
`α` and `β`.  Without running anything, state two things *every* inhabitant must satisfy
(does it ever turn `none` into a `some`?  can it manufacture a `β` when handed `none`?)
and one thing it *cannot* do.  Relate your answer to `option_map_isSome` (§4.3): the spec
you read there is one of these free theorems.  No code to submit.
@@@ -/

end W04
