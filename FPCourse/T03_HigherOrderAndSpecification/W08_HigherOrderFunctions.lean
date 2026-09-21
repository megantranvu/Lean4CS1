-- FPCourse/T03_HigherOrderAndSpecification/W08_HigherOrderFunctions.lean
import Mathlib.Data.List.Basic

/-! @@@
# Higher-Order Functions

## Functions as values

A *higher-order function* takes other functions as arguments or returns
functions as results.  In a typed functional language, this is not a
special case — functions are values like any other, and `→` is a type
constructor like `×` or `List`.

Higher-order functions enable *abstraction over computation patterns*.
Rather than writing separate functions for "sum all elements" and
"product all elements," we write one function `fold` parameterized by
the combining operation.

Every abstraction in this course corresponds to a *specification
pattern*: a family of propositions that all instances must satisfy.
@@@ -/

namespace W08

/-! @@@
## 8.1  map, filter, fold: the canonical trio

These three functions together cover an enormous range of list
computations.
@@@ -/

-- map: transform every element
#check @List.map      -- (α → β) → List α → List β

-- filter: keep elements satisfying a predicate
#check @List.filter   -- (α → Bool) → List α → List α

-- foldl: accumulate from the left
#check @List.foldl    -- (β → α → β) → β → List α → β

-- foldr: accumulate from the right
#check @List.foldr    -- (α → β → β) → β → List α → β

-- Evaluation traces for the three canonical operations:
-- map (·*2) [1,2,3]  ↝  [1*2, 2*2, 3*2]  ↝  [2, 4, 6]   (β-reduce per element)
-- filter even [1,2,3,4] ↝ keep 2, keep 4 ↝ [2, 4]        (evaluate predicate per element)
-- foldl (+) 0 [1,2,3]  ↝  foldl (+) 1 [2,3]              (0+1=1)
--                       ↝  foldl (+) 3 [3]                (1+2=3)
--                       ↝  foldl (+) 6 []                 (3+3=6)
--                       ↝  6                               (base case)
#eval [1,2,3,4,5].map (· * 2)              -- [2,4,6,8,10]
#eval [1,2,3,4,5].filter (· % 2 == 0)      -- [2,4]
#eval [1,2,3,4,5].foldl (· + ·) 0          -- 15
#eval [1,2,3,4,5].foldr (· :: ·) []        -- [1,2,3,4,5]

/-! @@@
> **Checkpoint — `map`.** `map f` applies `f` to every element and preserves length and
> order.  **Predict** the list below — three elements, each multiplied by 10 — before you
> read it.
@@@ -/

#eval [1, 2, 3].map (· * 10)   -- predict first

/-! @@@
> **Checkpoint — `filter`.** `filter p` keeps exactly the elements where `p` is `true`, in
> order.  **Predict** which of `1..6` survive `(· % 3 == 0)`, then check.
@@@ -/

#eval [1, 2, 3, 4, 5, 6].filter (· % 3 == 0)   -- predict first

/-! @@@
> **Checkpoint — `foldl` (accumulate from the left).** `foldl` threads the accumulator
> left-to-right: it sees `1`, then `2`, …  **Predict** the digits-to-number accumulation
> below (start `0`; each step is `acc * 10 + x`), then check.
@@@ -/

#eval [1, 2, 3, 4, 5].foldl (fun acc x => acc * 10 + x) 0   -- predict first

/-! @@@
> **Checkpoint — `foldr` (accumulate from the right).** `foldr f z` nests from the right:
> `1 - (2 - (3 - (4 - 0)))`.  Direction *matters* when `f` is not associative.  **Predict**
> this `Int` value — it is **not** the same as the left fold — then check.
@@@ -/

#eval ([1, 2, 3, 4] : List Int).foldr (fun x acc => x - acc) 0   -- predict first

/-! @@@
## 8.2  Deriving map from fold

`map` can be expressed as a `foldr`:
@@@ -/

def mapViaFoldr (f : α → β) (xs : List α) : List β :=
  xs.foldr (fun x acc => f x :: acc) []

-- Specification: mapViaFoldr agrees with List.map
theorem mapViaFoldr_eq_map (f : α → β) (xs : List α) :
    mapViaFoldr f xs = xs.map f :=
  List.recOn xs
    rfl
    (fun h _t ih => congrArg (f h :: ·) ih)

/-! @@@
> **Checkpoint — `mapViaFoldr` agrees with `map`.** `mapViaFoldr` rebuilds the list,
> replacing each `x` with `f x :: …`.  **Predict** the result from `mapViaFoldr_eq_map`
> (not by tracing the fold), then check.
@@@ -/

#eval mapViaFoldr (· + 1) [10, 20, 30]   -- predict from mapViaFoldr_eq_map

-- Similarly, filter can be expressed as foldr:
def filterViaFoldr (p : α → Bool) (xs : List α) : List α :=
  xs.foldr (fun x acc => if p x then x :: acc else acc) []

/-! @@@
> **Checkpoint — `filterViaFoldr`.** Each step keeps `x` only when `p x`.  **Predict**
> which of `1..4` survive `(· % 2 == 0)`, then check that it matches ordinary `filter`.
@@@ -/

#eval filterViaFoldr (· % 2 == 0) [1, 2, 3, 4]   -- predict first

/-! @@@
## 8.3  The functor laws

`List.map` satisfies two *functor laws*.  These are propositions —
logical types — that any correct implementation of `map` must inhabit.

**Law 1 (Identity)**: mapping the identity function does nothing.
**Law 2 (Composition)**: mapping a composition equals composing two maps.

These laws are not just bureaucratic requirements.  They are the
algebraic content of what it means to "transform elements without
changing structure."
@@@ -/

-- Functor Law 1: map id = id
-- Read: "for all lists, mapping the identity is the identity"
theorem map_id_law : ∀ xs : List α, xs.map id = xs :=
  List.map_id

-- Functor Law 2: map (f ∘ g) = map f ∘ map g
-- Read: "for all f, g, lists: mapping their composition equals
--        mapping g then mapping f"
theorem map_comp_law : ∀ (f : β → γ) (g : α → β) (xs : List α),
    xs.map (f ∘ g) = (xs.map g).map f :=
  fun f g xs => by simp [← List.map_map]

/-! @@@
> **Checkpoint — Functor Law 1 (`map id = id`).** By `map_id_law`, mapping `id` returns
> the list unchanged.  **Predict** the Boolean below *from the law* (not by evaluating the
> map), then check.
@@@ -/

#eval decide ((([1, 2, 3] : List Nat).map id) = [1, 2, 3])   -- predict from map_id_law

/-! @@@
> **Checkpoint — Functor Law 2 (`map (f ∘ g) = map f ∘ map g`).** One pass with the
> composition equals two passes.  **Predict** the Boolean below from `map_comp_law` with
> `g = (· * 2)`, `f = (· + 1)`, then check.
@@@ -/

#eval decide ((([1, 2, 3] : List Nat).map ((· + 1) ∘ (· * 2)))
              = ((([1, 2, 3] : List Nat).map (· * 2)).map (· + 1)))   -- predict from map_comp_law

/-! @@@
## 8.4  Writing law statements for other types

A key skill: given a new type with a map-like operation, state the
functor laws for it.  The laws have the same FORM regardless of the type.

Here are the laws for `Option.map`:
@@@ -/

-- You should read these and understand their form.
-- Then practice writing them for new types (see exercises).

theorem option_map_id : ∀ o : Option α, o.map id = o :=
  fun o => congr_fun Option.map_id o

theorem option_map_comp : ∀ (f : β → γ) (g : α → β) (o : Option α),
    o.map (f ∘ g) = (o.map g).map f :=
  fun f g o => (Option.map_map f g o).symm

/-! @@@
> **Checkpoint — `Option.map` obeys the *same* functor laws.** The identity law has one
> shape across all functors.  **Predict** both Booleans from `option_map_id` — `some` and
> `none` — then check that the form matched `List`.
@@@ -/

#eval decide ((some 5 : Option Nat).map id = some 5)   -- predict from option_map_id
#eval decide ((none  : Option Nat).map id = none)      -- predict from option_map_id

/-! @@@
## 8.5  fold and its specification pattern

`foldr f z` replaces each `::` constructor with `f` and the terminal
`[]` with `z`.

The key specification insight: many list properties are theorems about
`foldr`.  Length, sum, map, filter, append — all can be stated as `foldr`
computations.  The specification of `foldr` itself is therefore the
specification of a whole family of operations.
@@@ -/

-- foldr specification: reconstructing the list
theorem foldr_cons_nil (xs : List α) :
    xs.foldr (· :: ·) [] = xs :=
  List.foldr_cons_nil

/-! @@@
> **Checkpoint — `foldr (· :: ·) []` reconstructs the list.** Replacing every `::` with
> `::` and `[]` with `[]` is the identity.  **Predict** the result from `foldr_cons_nil`,
> then check.
@@@ -/

#eval ([1, 2, 3, 4] : List Nat).foldr (· :: ·) []   -- predict from foldr_cons_nil

-- foldr and append:
theorem foldr_append (f : α → β → β) (z : β) (xs ys : List α) :
    (xs ++ ys).foldr f z = xs.foldr f (ys.foldr f z) :=
  List.foldr_append

/-! @@@
> **Checkpoint — `foldr_append`.** Folding over `xs ++ ys` folds `ys` first, then feeds
> that result in as the base for `xs`.  **Predict** the Boolean below from `foldr_append`
> (both sides sum to the same number), then check.
@@@ -/

#eval decide ((([1, 2] ++ [3, 4] : List Nat).foldr (· + ·) 0)
              = (([1, 2] : List Nat).foldr (· + ·) (([3, 4] : List Nat).foldr (· + ·) 0)))
              -- predict from foldr_append

/-! @@@
## 8.6  The fusion law

When a `map` is followed immediately by a `fold`, they can be fused into
a single `fold`.  This is a *semantic optimization*: the two-pass
computation is equal to the single-pass computation.

Fusion laws are propositions.  Compilers use them as rewrite rules.
We state them here as types; applying them requires knowing they hold.
@@@ -/

-- map-foldr fusion:
-- foldr f z (map g xs) = foldr (f ∘ g) z xs
theorem map_foldr_fusion (f : β → γ → γ) (z : γ) (g : α → β) (xs : List α) :
    (xs.map g).foldr f z = xs.foldr (f ∘ g) z :=
  List.recOn xs
    rfl
    (fun h _t ih => congrArg (f (g h) ·) ih)

/-! @@@
> **Checkpoint — map-foldr fusion.** By `map_foldr_fusion`, mapping `(· * 2)` and then
> summing equals a single fold with `(· + ·) ∘ (· * 2)`.  **Predict** the Boolean below
> from the law (both fold the same total), then check.
@@@ -/

#eval decide (((([1, 2, 3] : List Nat).map (· * 2)).foldr (· + ·) 0)
              = (([1, 2, 3] : List Nat).foldr ((· + ·) ∘ (· * 2)) 0))   -- predict from map_foldr_fusion

/-! @@@
## Exercises

Each exercise carries a banner — `[id] · competency · tier · level · target` — and,
where it asks you to build something, an **acceptance check**: paste it beneath your
definition in your own file and it must succeed.  `#guard` is silent on success and
errors on failure, so the compiler is your grader.  See `EXERCISE_CONVENTIONS.md` for
the schema.  Do every **core** exercise; **stretch** exercises go deeper and are
optional.

---

**[E8.1]** · *specification writing* · tier 1 · **core** · target `MyPair.map`

Define the type and its map, deriving `DecidableEq` so the laws are `decide`-checkable:

```lean
inductive MyPair (α : Type) where
  | mk : α → α → MyPair α
  deriving DecidableEq
def MyPair.map (f : α → β) : MyPair α → MyPair β
  | .mk a b => .mk (f a) (f b)
```

State the two **functor laws** for `MyPair` as `Prop`s (identity and composition — same
*form* as §8.3), then confirm them on concrete instances.  Do **not** prove the general
laws; the point is to *write the specification* and check it holds on data:

```lean
-- identity law, one instance
#guard (MyPair.mk (1 : Nat) 2).map id = MyPair.mk 1 2
-- composition law, one instance (g = (· * 2), f = (· + 1))
#guard (MyPair.mk (1 : Nat) 2).map ((· + 1) ∘ (· * 2))
       = ((MyPair.mk (1 : Nat) 2).map (· * 2)).map (· + 1)
```

In one line: which tier does the *general* law live in, and which the two checks?

---

**[E8.2]** · *type-directed derivation* · tier 2 · **core** · target `sumList`

Derive `sumList : List Nat → Nat` (the sum of the elements) as a `foldl`.  The graded
artifact is a **derivation trace** in the Week 2 §2.6 format, *then* the `def`.
*First-step hint:* read the type `List Nat → Nat` — the seed is the unit of `+` (which
`Nat`?), and `foldl (· + ·)` threads it left across the list.  Effort: ~3 trace steps,
1 line of code.

```lean
#guard sumList [] = 0
#guard sumList [5] = 5
#guard sumList [1, 2, 3, 4] = 10
```

---

**[E8.3]** · *counterexample finding* · tier 1 · **core**

A student claims *"`foldl f z xs` and `foldr f z xs` always compute the same result."*
It is **wrong** whenever `f` is not associative/commutative.  Find one `f`, `z`, and `xs`
witnessing the mismatch and encode the witness so the check **succeeds** (it confirms the
two sides differ):

```lean
#guard ([1, 2, 3] : List Int).foldl (· - ·) 0 ≠ ([1, 2, 3] : List Int).foldr (· - ·) 0
```

In one line: for which class of operators `f` *do* the two folds agree?

---

**[E8.4]** · *type reading (free theorems)* · tier 2 · **core**

Look **only** at the type of `List.map`, namely `(α → β) → List α → List β`, polymorphic
in `α` and `β`.  Without running anything, state **two** things *every* inhabitant must
do and **one** thing it *cannot* do.  Prompts: can it change the length?  reorder?
invent a `β` out of nowhere, with no `α` in hand and no `f` applied?  inspect an `α`
(compare two, branch on a value) when all it holds is `f : α → β`?  Then, second: what
extra does the type of `List.foldr`, `(α → β → β) → β → List α → β`, let an inhabitant do
that `map`'s type does not?  (Builds on §8.3–§8.5 and Week 7 §7.2.  No code to submit.)

---

**[E8.5]** · *specification writing* · tier 1 · **stretch** · target `flatten`

Write `flatten : List (List α) → List α` using `foldr` (concatenate a list of lists).
State its specification as a `Prop` relating it to the library function — *"for every
`xss`, `flatten xss = xss.flatten`"* — then confirm on instances.  Do not prove the
general spec; write it and check it.  Effort: one `foldr (· ++ ·) []`; ~1 line.

```lean
#guard flatten [[1, 2], [3], [4, 5, 6]] = [1, 2, 3, 4, 5, 6]
#guard flatten ([] : List (List Nat)) = []
#guard flatten [[], [1], []] = [1]
#guard flatten ([[1, 2], [3], [4, 5, 6]] : List (List Nat)) = ([[1, 2], [3], [4, 5, 6]] : List (List Nat)).flatten
```

---

**[E8.6]** · *decidability identification* · tier 1 · **stretch**

For each proposition, say **whether `decide` can close it and why** (finite domain?
decidable predicate? quantifier over a function type or an unbounded `Nat`?) *before*
checking — the judgment is the point, not the tool-use:

(a) `([1, 2, 3] : List Nat).map (· + 1) = [2, 3, 4]`
(b) `∀ x ∈ ([1, 2, 3] : List Nat), (· + 1) x > x`
(c) `∀ xs : List Nat, xs.map id = xs`
(d) `∀ f : Nat → Nat, [1, 2].map f = [f 1, f 2]`

```lean
#guard decide (([1, 2, 3] : List Nat).map (· + 1) = [2, 3, 4]) = true
#guard decide (∀ x ∈ ([1, 2, 3] : List Nat), (· + 1) x > x) = true
-- (c) and (d) have no check on purpose: say why `decide` cannot close each
--     (name the obstacle — unbounded `Nat`; equality/quantification over a function type).
```
---

**[E8.7]** · *type-directed derivation + specification writing* · tier 2 · **stretch** · target `flatMap`

Derive `flatMap : (α → List β) → List α → List β` using `foldr`: apply `f` to every element
and concatenate the results.  Produce a **derivation trace** in the Week 2 §2.6 format — the
trace is the graded artifact — then the `def`.  Then state, as a `Prop`, that your `flatMap`
agrees with the standard library's list bind, which in this toolchain is
`List.flatMap : (α → List β) → List α → List β` (named `List.bind` in earlier versions);
look it up and read its type rather than proving the agreement.

```lean
#guard flatMap (fun n => [n, n]) [1, 2, 3] = [1, 1, 2, 2, 3, 3]
#guard flatMap (fun n => List.replicate n 0) [0, 2] = [0, 0]
#guard flatMap (fun n => [n]) ([] : List Nat) = ([] : List Nat)
```

*First-step hint:* `foldr` consumes the `List α`; its step function receives one `α` and the
already-folded `List β`, so the step is an append.  Effort: ~3 trace steps, 2 lines of code.

@@@ -/

end W08
