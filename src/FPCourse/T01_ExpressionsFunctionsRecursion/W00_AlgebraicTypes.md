```lean
-- FPCourse/T01_ExpressionsFunctionsRecursion/W00_AlgebraicTypes.lean
import Mathlib.Logic.Basic
import Mathlib.Data.Bool.Basic
```

# Computation and Reasoning

When we write, we write about something. The something
could be almost anything, real or imaginary: characters
in a story or game, numbers in an arithmetic puzzle, the
salinity of a parcel of ocean measured on a 10km x 10km x
1k grid. We can call these distinct domains of discourse,
or just domains, for short.

The writing itself, on the other hand, is strictly made
up of symbolic expressions. If the writing is a novel, a
poem, a market report, these expressions are written in
some *natural language*, the kind of language people learn
to speak.
What's magical is that our mind interprets
the symbols as *meaning*

A *type* defines and classifies a collection of values. For
our purposes, any value has exactly one type, and types thus
strictly partition values into such classes.

`Nat` classifies the natural numbers.
`Bool` classifies `true` and `false`.  When you encounter a type, ask:
*what values of this type can exist?*

This course is organized around six kinds of types.  These types are
sufficient to support a broad range of programming needs.  Moreover, we will
see that the logical analogs of these types provide a basis for expressing
mathematical propositions in the language we can call higher-order predicate
logic.

This is not an analogy.  It is the same language, read two ways.

| Constructor | Computational reading | Logical reading |
|---|---|---|
| Basic type | Atomic data | Atomic proposition |
| `α → β` | Function from α to β | α IMPLIES β (α → β)|
| `α × β` | Pair: α bundled with β | α AND β (α ∧ β) |
| `α ⊕ β` | Choice: α OR β (as data) | α OR β (α ∨ β) |
| `Empty` | Uninhabited | Logically False — no proof exists |
| `α → Empty` | α itself is uninhabited | Negation: (¬α) |

By the end of this week you will have seen all six in both readings.
You will have one vocabulary — *types and their inhabitants* — that
covers both.  You do not need two languages.  You are learning one.
```lean
namespace W00
```

## 0.1  Basic Types: the atoms of computation and logic

**Why basic types?**  Before you can build anything, you need raw
material — types that are not constructed from anything else.  Basic
types are your atoms: given to you, not derived.

You encounter them by name: `Nat`, `Bool`, `String`.  Their values
are listed explicitly and cannot be broken down further.
```lean
-- Nat: the type of natural numbers.  Values: 0, 1, 2, 3, ...
#check (0 : Nat)
#check (42 : Nat)
#eval 2 + 3        -- 5
#eval 10 - 3       -- 7 (natural number subtraction, floors at 0)

-- Bool: two values.
#check (true : Bool)
#check (false : Bool)
#eval true && false  -- false
#eval true || false  -- true

-- String: sequences of characters.
#check ("hello" : String)
#eval "hello" ++ ", world"   -- "hello, world"
#eval "hello".length          -- 5
```

> **Checkpoint — `Nat` subtraction floors at 0.** Subtraction on `Nat` is *truncated*: it
> never produces a negative number.  **Predict** the value of `3 - 10` — it is not `-7` —
> before reading it.
```lean
#eval 3 - 10   -- predict first (truncated subtraction)
```

> **Checkpoint — `Bool` connectives.** `&&`, `||`, and `!` are ordinary computations on
> `Bool` values.  **Predict** the result of `(false || true) && !false`, then check.
```lean
#eval (false || true) && !false   -- predict first
```

> **Checkpoint — `String` length after concatenation.** `++` joins two strings and
> `.length` counts characters.  **Predict** the length of `"hello" ++ ", world"` — remember
> to count the comma and the space — before reading it.
```lean
#eval ("hello" ++ ", world").length   -- predict firstw
```

**The Lean notional machine.**  Think of Lean as a machine with one job:
given an expression, apply reduction rules one step at a time until no
further reduction is possible.  The irreducible result is the *normal form*.

```
  expression  ──→  Lean kernel  ──→  normal form
   (source)        (evaluates)       (irreducible value)
```

Every `#eval` you write invokes this machine.

Each `#eval` above is a chain of named reductions:

| Expression | Reduction steps | Normal form |
|------------|----------------|-------------|
| `2 + 3` | one arithmetic step | `5` |
| `10 - 3` | one arithmetic step | `7` |
| `true && false` | `true && b ↝ b` (definition of `&&`) | `false` |
| `"hello" ++ ", world"` | string concat definition | `"hello, world"` |
| `"hello".length` | list length definition | `5` |

The symbol `↝` means *reduces to in one step*.  You will see it used
throughout this course whenever a specific reduction rule is being named.

`#check e` inspects the *type* of `e` without evaluating it.  Types are
checked statically at elaboration time; values are produced dynamically
at evaluation time.  Both happen before you see any output.

An *expression* is any piece of Lean text that has a type and can be
evaluated to a normal form.

### The same question, two registers

We can ask of any type: *what are its inhabitants?*

| Type | Sample inhabitants |
|------|--------------------|
| `Nat` | `0`, `1`, `2`, `42` |
| `Bool` | `true`, `false` |
| `String` | `""`, `"hi"`, `"hello, world"` |

We can ask the identical question of *propositions*:

| Proposition (type) | Inhabitants |
|--------------------|-------------|
| `1 + 1 = 2` | exactly one: the proof `rfl` |
| `1 + 1 = 5` | none — it is false |
| `True` | exactly one: `True.intro` |
| `False` | none — it is false |

A proposition with at least one inhabitant is *true*.  A proposition
with no inhabitant is *false*.  In Lean, propositions are encoded as types.
```lean
-- Proofs are terms.  `rfl` inhabits `1 + 1 = 2` the way `42` inhabits `Nat`.
example : 1 + 1 = 2 := rfl   -- Evaluation: 1+1 ↝ 2, same as the right side
example : True      := True.intro

-- `decide` evaluates a decision procedure to produce a proof automatically.
example : 7 * 6 = 42       := by decide  -- Evaluation: 7*6 ↝ 42 ✓
example : 2 + 2 ≠ 5        := by decide  -- Evaluation: 2+2 ↝ 4 ≠ 5 ✓
example : 100 < 200         := by decide  -- Evaluation: comparison ↝ true ✓

-- `#check` works on proofs too.
#check (rfl : 1 + 1 = 2)    -- the type IS the proposition
#check (True.intro : True)
```

**Evaluation.**  `rfl` proves `a = b` when `a` and `b` *evaluate to the
same normal form*.  `1 + 1 = 2` holds by `rfl` because both sides reduce
to `2` — the equality is *definitional*, certified by computation.

**Evaluation.**  `decide` works by evaluating a *decision procedure*
for the proposition, an operation that determines if the proposition is
true or false and that returns the corresponding Boolean answer.
For `7 * 6 = 42`, Lean evaluates `7 * 6` to `42`,
confirms both sides are the same, and constructs the proof automatically.
If evaluation had produced `false`, the file would not compile — the
proof term would be absent, and the type would be uninhabited.

`decide` can only handle propositions for which evaluation terminates —
*decidable* propositions.  Concrete arithmetic is decidable; universal
claims over all natural numbers are not.  We return to this in Week 7.
> **Checkpoint — `decide` evaluates a decision procedure.** For a decidable proposition,
> `decide` runs its decision procedure and returns a `Bool`.  **Predict** `decide (7 * 6 = 42)`
> — does `7 * 6` reach the same normal form as `42`? — then check.
```lean
#eval decide (7 * 6 = 42)   -- predict first
```

> **Checkpoint — a false proposition has no proof.** `2 + 2 = 5` is uninhabited, so its
> decision procedure returns `false` (and the file would not compile if you tried to prove
> it).  **Predict** `decide (2 + 2 = 5)` before reading it.
```lean
#eval decide (2 + 2 = 5)   -- predict first (an uninhabited proposition)
```

## 0.2  Function Types: `α → β`

**Why function types?**  Every transformation in programming — mapping,
filtering, converting, composing — is a function.  Functions are also
how you prove implications: a proof of `P → Q` is literally a function
from proofs of `P` to proofs of `Q`.  Mastering `→` unlocks both.

```
  α → β

  ┌───┐           ┌───┐
  │ α │  ──f──→   │ β │
  └───┘  (apply)  └───┘

  Build:  fun a => ...   (introduce a function)
  Use:    f a            (apply it to an argument; β-reduction fires)
```

The arrow type `α → β` is the type of **functions** from `α` to `β`.
A value of type `α → β` takes any input of type `α` and produces an
output of type `β`.

Functions are the most fundamental type constructor.  Many other
constructs — recursion, type classes, proofs — ultimately reduce to
functions.
```lean
-- Defining functions with `def`:
def double  : Nat → Nat    := fun n => n * 2
def isZero  : Nat → Bool   := fun n => n == 0
def negate  : Bool → Bool  := fun b => !b
def greet   : String → String := fun name => "Hello, " ++ name

-- Evaluation: applying a function substitutes the argument for the parameter.
-- This substitution step is called β-reduction.
-- double 7 ↝ 7 * 2 ↝ 14        (β-reduction, then arithmetic)
-- isZero 0 ↝ 0 == 0 ↝ true      (β-reduction, then BEq)
-- greet "Alice" ↝ "Hello, " ++ "Alice" ↝ "Hello, Alice"
#eval double 7         -- 14
#eval isZero 0         -- true
#eval isZero 5         -- false
#eval greet "Alice"    -- "Hello, Alice"
```

> **Checkpoint — β-reduction (`double`).** `double n ↝ n * 2`: applying the function
> substitutes the argument for the parameter, then arithmetic fires.  **Predict** `double 21`
> from that rule, then check.
```lean
#eval double 21   -- predict first

-- Multi-argument functions are *curried*:
-- `Nat → Nat → Nat` means `Nat → (Nat → Nat)`.
-- Applying one argument returns a function waiting for the second.
def add : Nat → Nat → Nat := fun a b => a + b

#eval add 3 4          -- 7   (apply both arguments)
#eval (add 3) 4        -- 7   (same: add 3 is itself a Nat → Nat)
```

> **Checkpoint — currying and partial application (`add`).** `add : Nat → Nat → Nat` is
> `Nat → (Nat → Nat)`, so `add 40` is itself a function awaiting one more argument.
> **Predict** `(add 40) 2`, then check.
```lean
#eval (add 40) 2   -- predict first

-- Named argument style (equivalent, more readable for multi-arg):
def max' (a b : Nat) : Nat := if a ≥ b then a else b

#eval max' 5 3         -- 5
#eval max' 2 8         -- 8
```

> **Checkpoint — `max'` at the tie boundary.** `max'` is `if a ≥ b then a else b`, and `≥`
> includes equality.  **Predict** `max' 7 7` — which branch fires when the arguments are
> equal? — then check.
```lean
#eval max' 7 7   -- predict first (the a = b boundary)
```

### The logical reading: implication

When `P` and `Q` are propositions, `P → Q` is the type of proofs that
**P implies Q**.  A proof of `P → Q` is a *function*: given any proof
of `P`, it returns a proof of `Q`.

This is not a metaphor.  The same keyword (`fun`), the same syntax
(`fun h => ...`), the same application rule — a proof of `P → Q`
literally IS a function.

**The identity function is simultaneously**:
- *Computational*: given any value, return it.
- *Logical*: if P holds then P holds (reflexivity of implication).
```lean
-- Computational: identity function for data.
def myId (a : α) : α := a
#eval myId 42       -- 42
#eval myId "hello"  -- "hello"

-- Logical: if P holds, then P holds.
theorem p_implies_p (P : Prop) (h : P) : P := h
-- This IS the identity function, applied to a proof.

-- Implication is transitive: if P → Q and Q → R, then P → R.
-- Computation: function composition.
-- Logic: hypothetical syllogism.
theorem implies_trans (P Q R : Prop)
    (hpq : P → Q) (hqr : Q → R) : P → R :=
  fun hp => hqr (hpq hp)

-- The proof IS function composition: hqr ∘ hpq.
-- Compare with the computational version:
def compose (f : β → γ) (g : α → β) : α → γ := fun a => f (g a)

-- Their structures are identical.  The only difference is that
-- P, Q, R range over Prop instead of Type.
```

## 0.3  Product Types: `α × β`

**Why product types?**  Real programs combine data: a point has an x
coordinate AND a y coordinate; a database record has a name AND an age
AND an address.  Whenever you need to carry multiple pieces of data
simultaneously, you reach for a product.

```
  α × β

  ┌──────────────┐
  │  .1  :  α    │   ← first component
  │  .2  :  β    │   ← second component
  └──────────────┘

  Build:  (a, b)   or   ⟨a, b⟩
  Use:    p.1, p.2       (projections; ι-reduction fires)
```

A **product type** `α × β` bundles a value of type `α` with a value of
type `β`.  To *build* a product you must supply BOTH components.  To
*use* a product you project out whichever component you need.

Products are how data is *aggregated*: a 2D point is an x AND a y;
a person record is a name AND an age AND a city.
```lean
-- Building and projecting products:
def myPair : Nat × Bool := (7, true)
#eval myPair.1    -- 7       (first component)
#eval myPair.2    -- true    (second component)

-- Anonymous constructor ⟨_, _⟩ is equivalent to (_, _) for products:
def myPoint : Float × Float := ⟨3.0, 4.0⟩

-- Nested products (right-associative by default):
def myTriple : Nat × String × Bool := (42, "hello", false)
#eval myTriple.1        -- 42
#eval myTriple.2.1      -- "hello"
#eval myTriple.2.2      -- false
```

> **Checkpoint — projecting a nested product.** In `(1, "two", true) : Nat × String × Bool`
> the middle field is reached with `.2.1` (products are right-associative).  **Predict**
> `(1, "two", true).2.1`, then check.
```lean
#eval (1, "two", true).2.1   -- predict first

-- A function that takes a product and swaps its components:
def swap (p : α × β) : β × α := (p.2, p.1)
#eval swap (1, "one")    -- ("one", 1)
#eval swap (true, 42)    -- (42, true)
```

> **Checkpoint — `swap` exchanges the components.** `swap (p : α × β) : β × α` returns
> `(p.2, p.1)` — the component *types* swap along with the values.  **Predict** `swap (99, "z")`,
> then check.
```lean
#eval swap (99, "z")   -- predict first

-- Products in function signatures (named arguments are sugar for products):
def hypotenuse (legs : Float × Float) : Float :=
  Float.sqrt (legs.1 ^ 2 + legs.2 ^ 2)
#eval hypotenuse (3.0, 4.0)   -- 5.0
```

### The logical reading: conjunction (AND)

In logic, `P ∧ Q` holds when **both** P holds **and** Q holds.  A proof
of `P ∧ Q` is a pair: a proof of P together with a proof of Q.

`And` in Lean is literally a structure with two fields.  It IS a product
type, specialized to the case where the components are proofs.

| Product | And (conjunction) |
|---------|--------------------|
| `α × β` | `P ∧ Q` |
| `(a, b) : α × β` | `⟨h₁, h₂⟩ : P ∧ Q` |
| `p.1 : α` | `h.left : P` |
| `p.2 : β` | `h.right : Q` |
```lean
-- Proving a conjunction: supply both halves.
example : 2 < 3 ∧ 3 < 4 := ⟨by decide, by decide⟩

-- Or: explicit constructor.
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := And.intro rfl rfl

-- Extracting from a conjunction:
theorem use_left  (h : P ∧ Q) : P := h.left
theorem use_right (h : P ∧ Q) : Q := h.right

-- Commutativity: if P ∧ Q then Q ∧ P.
-- Computation: swap the pair.
-- Logic: swap the conjunction.
-- Evaluation: ⟨h.right, h.left⟩ ↝ ⟨proof-of-Q, proof-of-P⟩  (projections reduce)
theorem and_comm' (h : P ∧ Q) : Q ∧ P :=
  ⟨h.right, h.left⟩   -- this IS the swap function applied to proofs

-- Three-way conjunction:
example : 1 < 2 ∧ 2 < 3 ∧ 3 < 4 := by decide
```

> **Checkpoint — conjunction is a product, and it is decidable.** A proof of `P ∧ Q` is a
> pair of proofs; when `P` and `Q` are each decidable, so is `P ∧ Q`.  **Predict**
> `decide (2 < 3 ∧ 3 < 4)`, then check.
```lean
#eval decide (2 < 3 ∧ 3 < 4)   -- predict first
```

## 0.4  Sum Types: `Sum α β` (written `α ⊕ β`)

**Why sum types?**  Real programs handle alternatives: a network request
either succeeds OR fails; a command is either add OR remove OR update;
a shape is a circle OR a rectangle OR a triangle.  Sums capture this
structure in the type — and pattern-matching forces you to handle every
case.

```
  α ⊕ β

  ┌──────────────────────────┐
  │  Sum.inl (a : α)         │   ← "I have an α"
  │    OR                    │
  │  Sum.inr (b : β)         │   ← "I have a β"
  └──────────────────────────┘

  Build:  Sum.inl a   or   Sum.inr b
  Use:    match s with | Sum.inl a => ... | Sum.inr b => ...
```

A **sum type** `α ⊕ β` carries either a value of type `α` **or** a
value of type `β`.  It represents a *choice* or *variant*: you get one
kind of thing or the other, and the tag `inl`/`inr` tells you which.

Sums are how programs handle **alternatives**: a result is either a
successful value or an error; a shape is a circle or a rectangle or a
triangle.
```lean
-- Sum has two constructors: inl (left) and inr (right).
def aNum  : Nat ⊕ String := Sum.inl 42
def aStr  : Nat ⊕ String := Sum.inr "error"

-- To USE a sum, you must handle BOTH cases:
def describeNatOrStr (s : Nat ⊕ String) : String :=
  match s with
  | Sum.inl n => "a number: " ++ toString n
  | Sum.inr e => "a string: " ++ e

#eval describeNatOrStr aNum    -- "a number: 42"
#eval describeNatOrStr aStr    -- "a string: error"
```

> **Checkpoint — eliminating a sum (`describeNatOrStr`).** `match` must handle both `inl`
> and `inr`; the tag chooses the branch.  **Predict** `describeNatOrStr (Sum.inr "oops")`,
> then check.
```lean
#eval describeNatOrStr (Sum.inr "oops")   -- predict first

-- The canonical programming sum: Option.
-- Option α represents either a value (some a) or absence (none).
-- It is a sum: Unit ⊕ α, roughly.
def safeDivide (a b : Nat) : Option Nat :=
  if b = 0 then none else some (a / b)

#eval safeDivide 10 2   -- some 5
#eval safeDivide 10 0   -- none

-- Using an Option:
def showResult (r : Option Nat) : String :=
  match r with
  | none   => "no result"
  | some n => "result: " ++ toString n

#eval showResult (safeDivide 10 2)    -- "result: 5"
#eval showResult (safeDivide 10 0)    -- "no result"
```

> **Checkpoint — `Option` guards a partial operation (`safeDivide`).** `safeDivide` returns
> `none` exactly when the divisor is `0`, and `some` otherwise — the two arms of a sum.
> **Predict** both values below (which one is `none`?), then check.
```lean
#eval safeDivide 20 4   -- predict first
#eval safeDivide 7 0    -- predict first
```

### The logical reading: disjunction (OR)

In logic, `P ∨ Q` holds when **at least one** of P or Q holds.  A proof
of `P ∨ Q` is either a proof of P (tagged `Or.inl`) or a proof of Q
(tagged `Or.inr`).

`Or` IS a sum type, specialized to propositions.

| Sum | Or (disjunction) |
|-----|------------------|
| `α ⊕ β` | `P ∨ Q` |
| `Sum.inl (a : α)` | `Or.inl (h : P)` |
| `Sum.inr (b : β)` | `Or.inr (h : Q)` |
| `match s with \| inl a => ... \| inr b => ...` | `match h with \| inl h => ... \| inr h => ...` |

To *prove* a disjunction, pick one side and prove it.
To *use* a disjunction, case-split on which side holds (just like `match`).
```lean
-- Proving a disjunction: choose a side.
example : 1 = 1 ∨ 1 = 2 := Or.inl rfl      -- left side
example : 1 = 2 ∨ 1 = 1 := Or.inr rfl      -- right side
example : 3 < 4 ∨ 4 < 3 := by decide       -- decide picks the right side

-- Using a disjunction: case analysis.
theorem or_comm' (h : P ∨ Q) : Q ∨ P :=
  match h with
  | Or.inl hp => Or.inr hp   -- had P; now tag it as inr
  | Or.inr hq => Or.inl hq   -- had Q; now tag it as inl
-- This IS `swap` applied to proofs of disjuncts.

-- Disjunction from an implication:
theorem or_weaken (h : P) : P ∨ Q := Or.inl h
```

> **Checkpoint — disjunction is a sum, and it is decidable.** A proof of `P ∨ Q` tags one
> side; `decide` finds a true side when one exists.  **Predict** `decide (3 < 4 ∨ 4 < 3)` —
> which disjunct holds? — then check.
```lean
#eval decide (3 < 4 ∨ 4 < 3)   -- predict first
```

## 0.5  The Empty Type: `Empty` and `False`

**Why an empty type?**  Sometimes a situation is genuinely impossible:
a division by zero that your types have already ruled out; a branch of
a proof that leads to contradiction.  When you can prove a situation is
impossible, the empty type lets you discharge it cleanly — the type
system certifies the branch is unreachable.

The **empty type** has no constructors and no values.  It is impossible
to produce a term of this type.

In computation: `Empty` represents a branch that can never be reached.
A function returning `Empty` can never actually return.  Pattern-matching
on a value of type `Empty` needs **zero** branches — vacuously complete.

In logic: `False` is the proposition with no proof.  A proposition that
cannot be proved is *false*.

`Empty : Type` and `False : Prop` are the same idea in two universes.
```lean
-- `Empty` has no constructors — you cannot produce a value of it.
-- But you CAN write a function FROM Empty (with no cases to handle):
def fromEmpty (e : Empty) : α := nomatch e

-- In logic: `False → P` (ex falso quodlibet — from absurdity, anything).
theorem ex_falso {P : Prop} (h : False) : P := False.elim h

-- Why is this useful?  Because it discharges impossible cases.
-- If a case leads to `False`, the rest of the goal becomes irrelevant.
example (h : 2 + 2 = 5) : "pigs fly" = "pigs fly" :=
  absurd h (by decide)   -- decide proves ¬(2+2=5); absurd closes the goal

-- `absurd : P → ¬P → Q`
-- Given a proof of P and a proof of ¬P, produce anything.
-- This is the logical short-circuit: contradiction → done.
```

The power of the empty type: every impossible case reduces to one.

When your program reaches a state that "cannot happen," the right tool
is to prove it is `False` and use `False.elim` (or `absurd`) to discharge
the goal.  The program does not crash; it never reaches that branch at all,
because the type system certified the branch is unreachable.

`nomatch e` is Lean's syntax for pattern-matching on a value of a type
with no constructors: the match is exhaustive with zero branches.
> **Checkpoint — `False` has no proof.** `False` (like `Empty`) is uninhabited, so its
> decision procedure returns `false`.  **Predict** `decide False`, and say why no `#eval`
> could ever print a *proof* of it.
```lean
#eval decide False   -- predict first
```

## 0.6  Functions to Empty: `α → Empty` and `¬P`

**Why functions to empty?**  Ruling out a case is as important as
handling one.  When you write a precondition `h : n ≠ 0`, you are
carrying a function `(n = 0) → False` — proof that passing in a
zero is impossible.  Negation is not a primitive added to the language;
it falls out of the function arrow and the empty type that you already
have.

The most surprising type constructor: **a function whose codomain is
the empty type**.

A value of type `α → Empty` is a function that, if given an `α`, would
produce an `Empty`.  But `Empty` has no values — so such a function can
never complete its job.  This means: if such a function *exists*, then
`α` itself must have had no values to pass in.  The function *proves*
that `α` is uninhabited.

In computation: `α → Empty` certifies that `α` has no values.

In logic: `¬P` is **defined** as `P → False`.  A proof of `¬P` is a
function: given any proof of `P`, produce a proof of `False`.  Since
`False` has no proofs, the function can never fire — which means P has
no proofs, i.e., P is false.

Negation is not a primitive.  It IS the function arrow, aimed at `False`.
```lean
-- ¬P unfolds to P → False:
#print Not   -- def Not (a : Prop) : Prop := a → False

-- Every proof of ¬P is a function P → False.
-- `decide` constructs this function automatically for decidable cases.
example : ¬ (1 = 2)  := by decide
example : ¬ (3 > 5)  := by decide
example : ¬ (0 = 1)  := by decide
```

> **Checkpoint — `¬P` is `P → False`.** `decide` builds the function `¬(1 = 2)` automatically
> because the equality is decidably false.  **Predict** `decide (¬ (1 = 2))`, then check.
```lean
#eval decide (¬ (1 = 2))   -- predict first

-- Negation from definitions:
-- ¬(1 = 2) means (1 = 2) → False.
-- 1 and 2 have different normal forms, so the Eq constructor cannot apply;
-- Lean sees there are zero cases to match, so `nomatch` closes the goal.
theorem one_ne_two : ¬ (1 = 2) := fun h => nomatch h

-- Contradiction: if P and ¬P both hold, everything follows.
theorem contradiction {P Q : Prop} (h : P) (hne : ¬P) : Q :=
  False.elim (hne h)   -- hne h : False, then ex falso

-- Double negation introduction (the direction that holds constructively):
-- "If P holds, then P is not contradictory."
theorem not_not_intro (h : P) : ¬¬P :=
  fun hnp => hnp h    -- hnp : ¬P = P → False; apply it to h : P

-- Example: ¬(P ∧ ¬P) — no proposition and its negation can both hold.
theorem not_and_not (h : P ∧ ¬P) : False :=
  h.right h.left      -- apply ¬P (= h.right) to P (= h.left)
```

> **Checkpoint — no `P` and `¬P` together.** `not_and_not` says `P ∧ ¬P` is contradictory;
> on a concrete decidable `P` the whole negation is checkable.  **Predict**
> `decide (¬ ((3 < 4) ∧ ¬(3 < 4)))`, then check.
```lean
#eval decide (¬ ((3 < 4) ∧ ¬(3 < 4)))   -- predict first
```

## 0.7  The Six Constructors Together

Here is the complete picture.  Every type you will write in this course
is built from some combination of these six.  Every proposition you will
reason about is expressed by some combination of these six.

| Constructor | Computational | Logical |
|-------------|---------------|---------|
| Basic type | `Nat`, `Bool`, `String`, ... | Atomic proposition `P : Prop` |
| `α → β` | Function: transform α into β | Implication: α proves β |
| `α × β` | Product: carry BOTH α and β | Conjunction: BOTH α and β |
| `α ⊕ β` | Sum: carry ONE OF α or β | Disjunction: ONE OF α or β |
| `Empty` / `False` | No value exists | No proof exists |
| `α → Empty` / `¬α` | α is uninhabited | α is contradictory |

The question "what inhabits this type?" has two flavors:
- Computational types (`Type`): inhabitants are *data*.
- Logical types (`Prop`): inhabitants are *proofs*.

But the **constructors are shared**.  Products bundle data AND proofs
the same way.  Sums tag data AND proofs the same way.  Functions
transform data AND convert proofs the same way.  The empty type
represents impossible data AND impossible proofs.

```lean
-- All six constructors demonstrated side by side:

-- Product / And        (data is built with `def`; a proof of a Prop uses `theorem`)
def dataPair      : Nat × Bool := ⟨5, true⟩
theorem proofPair : 2 < 3 ∧ 3 < 4 := ⟨by decide, by decide⟩

-- Sum / Or
def dataSum       : Nat ⊕ Bool  := Sum.inl 7
theorem proofDisj : 2 < 3 ∨ 3 < 2 := Or.inl (by decide)

-- Function / Implication
def dataFun       : Nat → Nat   := fun n => n + 1
theorem proofImpl : 2 < 3 → 2 ≤ 3 := fun h => Nat.le_of_lt h

-- Negation / Uninhabited
theorem proofNeg  : ¬ (1 = 2) := by decide

-- Empty type: a function from Empty returns anything
def fromImpossible (e : Empty) : Nat × Bool × String := nomatch e
```

> **Checkpoint — the six constructors, combined and decidable.** This proposition wires
> together `∧`, `∨`, and `¬` over decidable atoms.  **Predict**
> `decide ((2 < 3 ∧ 3 < 4) ∨ ¬(1 = 1))` — is the left disjunct already enough? — then check.
```lean
#eval decide ((2 < 3 ∧ 3 < 4) ∨ ¬(1 = 1))   -- predict first
```

## 0.8  Challenges in programming with algebraic types

Understanding the six constructors is not yet fluency.  The challenge is
knowing **which constructor fits each situation**.

Here are the fundamental design questions:

**Use a product when** you need to carry multiple pieces of data at once.
A point is x AND y.  A function's return type is a product when it returns
two things.  A precondition bundled with a return value is a product of
data and proof.

**Use a sum when** data has multiple, mutually exclusive forms.  An API
result is success OR error.  A command is add OR remove OR update.
Pattern-matching IS elimination of a sum — you must handle every case.

**Use a function when** you want to defer or parameterize computation.
A callback, a comparator, a predicate — these are function-type arguments.

**Use negation (function to False) when** you need to *rule out* a case.
A precondition `h : x ≠ 0` is `(x = 0) → False`.  It certifies the
impossible before the program runs.

**Use Empty/False when** a branch cannot exist.  The type system then
verifies you never reach it; `nomatch` or `False.elim` closes the goal.

The payoff: once you have the right type, the program often writes itself.
The type tells you what constructors to use; the exhaustiveness checker
tells you which cases remain.  Types are not just documentation —
they are your co-programmer.

## Exercises

Each exercise carries a banner — `[id] · competency · tier · level · target` — and,
where it asks you to build something, an **acceptance check**: paste it beneath your
definition in your own file and it must succeed.  `#guard` is silent on success and
errors on failure, so the compiler is your grader.  See `EXERCISE_CONVENTIONS.md` for
the schema.  Do every **core** exercise; **stretch** exercises go deeper and are
optional.

---

**[E0.1]** · *decidability identification* · tier 1 · **core**

For each claim, say **whether `decide` can close it and why** (finite domain? decidable
predicate?) and **which of the six constructors** (§0.7) the proposition uses — *then*
check it.  The judgment is the point, not the tool-use:

(a) `2 < 3 ∧ 3 < 4`   (b) `2 < 3 ∨ 3 < 2`   (c) `¬ (2 = 3)`   (d) `¬ (2 < 3 ∧ 3 < 2)`

```lean
#guard decide (2 < 3 ∧ 3 < 4) = true
#guard decide (2 < 3 ∨ 3 < 2) = true
#guard decide (¬ (2 = 3)) = true
#guard decide (¬ (2 < 3 ∧ 3 < 2)) = true
```

Every atom here is a decidable comparison over concrete `Nat`s, so each connective stays
decidable.

---

**[E0.2]** · *type-directed derivation* · tier 2 · **core** · target `twice`

Derive `twice : (α → α) → α → α` that applies its function twice (`twice f x = f (f x)`).
Produce a **derivation trace** in the Week 2 §2.6 format — the trace is the graded
artifact — then the `def`.  *First-step hint:* the type is two nested arrows, so `→I`
twice introduces `f : α → α` and `x : α`; the only way to reach the goal `α` is to apply
`f`, and applying it once leaves another `α` to feed back in.  Effort: ~3 trace steps,
2 lines of code.

```lean
#guard twice (· * 2) 3 = 12
#guard twice (fun b => !b) false = false
#guard twice (· + 1) 0 = 2
```

When `α` is a `Prop`, read `(P → P) → P → P` aloud: what does `twice` say logically?

---

**[E0.3]** · *specification writing (+ type reading)* · tier 1 · **core** · target `mapOption`

Build `mapOption : (α → β) → Option α → Option β` with a `match`: apply `f` under `some`,
pass `none` through.  State its spec in one line — *"`some a ↦ some (f a)`, and `none ↦ none`"* —
then confirm on instances.  Which **two** of the six constructors does the *type* of
`mapOption` use?  Effort: one `match`, ~3 lines.

```lean
#guard mapOption (· * 2) (some 5) = some 10
#guard mapOption (· * 2) (none : Option Nat) = none
#guard mapOption (fun b => !b) (some true) = some false
```

---

**[E0.4]** · *counterexample finding* · tier 1 · **core**

A student claims *"`Nat` subtraction is invertible: `(a - b) + b = a` for all `a b : Nat`."*
It is **wrong** — subtraction on `Nat` is truncated (§0.1).  Find concrete inputs
witnessing the failure and encode the witness so the check **succeeds** (it confirms the
two sides differ):

```lean
#guard (3 - 10) + 10 ≠ 3
```

Then state, in one line, the *side condition* on `a` and `b` under which `(a - b) + b = a`
does hold.

---

**[E0.5]** · *specification reading* · tier 3 (+ tier-1 check) · **stretch**

Read the **provided** proof of `not_and_not` (§0.6): `fun h => h.right h.left`.  It shows
that `P ∧ ¬P` is contradictory.  In one or two sentences, name the *type* of `h.left`, the
*type* of `h.right`, and explain why applying `h.right` to `h.left` produces `False` — do
**not** author a new proof.  As a decidable by-product on a concrete `P`, confirm:

```lean
#guard decide (¬ ((3 < 4) ∧ ¬(3 < 4))) = true
```

In one line: which tier does the *general* statement `not_and_not` live in, and which does
the concrete check?

---

**[E0.6]** · *type reading (free theorems)* · tier 2 · **stretch**

Look **only** at the type `Empty → α`, polymorphic in `α`.  Without running anything, state
what every inhabitant does with its input and why it needs **zero** match cases; then say
one thing no *total* function `α → Empty` can do when `α` is inhabited (§0.5–0.6).  Finally,
read the provided term `fromImpossible : Empty → Nat × Bool × String := nomatch e` (§0.7) in
both registers — the computational one (an unreachable branch) and the logical one (*ex
falso quodlibet*).  No code to submit.
```lean
end W00
```


<div class="issue-box">📝 <a href="https://github.com/kevinsullivan/Lean4CS1/issues/new">Report an issue</a> with this section</div>

