-- FPCourse/T02_InductiveTypes/W07_PolymorphismDecidability.lean
import Mathlib.Data.List.Basic
import Mathlib.Logic.Basic

/-! @@@
# Polymorphism and Decidability

## Type variables and parametric polymorphism

A *polymorphic* function works uniformly for any type.  Type variables
(written with lowercase letters like `α`, `β`) stand for any type.

A function is *parametrically polymorphic* if its behavior does not
depend on which type the variable is instantiated to.  The type alone
constrains what the function can do — a polymorphic `f : List α → List α`
cannot inspect element values, so it can only permute, drop, or
duplicate them.
@@@ -/

namespace W07

/-! @@@
## 7.1  Polymorphic functions and their types
@@@ -/

-- id works for any type
#check @id        -- (α : Type u) → α → α

-- const ignores its second argument
def myConst (a : α) (_ : β) : α := a
#check @myConst   -- (α β : Type u) → α → β → α

-- flip swaps argument order
def myFlip (f : α → β → γ) : β → α → γ := fun b a => f a b
#check @myFlip    -- (α β γ : Type u) → (α → β → γ) → β → α → γ

/-! @@@
> **Checkpoint — `myConst`.** `myConst : α → β → α` returns its first argument.
> **Predict** the value below — does the second argument affect it? — then check.
@@@ -/

#eval myConst 7 "ignored"   -- predict first

/-! @@@
> **Checkpoint — `myFlip`.** `myFlip` swaps a function's two arguments.  **Predict** the
> value of the flipped subtraction below, then check.
@@@ -/

#eval myFlip (fun a b => a - b) 3 10   -- predict:  (fun a b => a - b) 10 3

/-! @@@
## 7.2  Free theorems: what a polymorphic type guarantees

The intro claimed a polymorphic `f : List α → List α` "can only permute, drop, or
duplicate."  That is not a remark about *some* implementation — it is forced by the
type, for *every* inhabitant.  When a function is polymorphic in `α`, its code is handed
a type it cannot name: it cannot test a value of `α`, compare two, or manufacture one.
The only `α`s it can return are those it was given.  This is **parametricity**
(Reynolds 1983); the theorems it hands you for free are Wadler's "theorems for free"
(2015).  Read every signature below by asking:

> **What does this type forbid every inhabitant from doing?**
@@@ -/

/-! @@@
**`∀ α, α → α` has essentially one inhabitant.**  One value of an unknown type in, one
out; the only `α` available is the input, so it must be returned.  Free theorem: for
every `g`, `g (f x) = f (g x)`.
@@@ -/

def myId : ∀ α : Type, α → α := fun _ x => x
#eval myId String (toString 3)   -- "3"  = g (f 3)
#eval toString (myId Nat 3)      -- "3"  = f (g 3)

/-! @@@
**`∀ α, α → α → α` has exactly two inhabitants** — the two projections; nothing else
can be built.
@@@ -/

def fst' : ∀ α : Type, α → α → α := fun _ x _ => x
def snd' : ∀ α : Type, α → α → α := fun _ _ y => y

/-! @@@
**`∀ α, List α → Nat` can only measure shape.**  It cannot inspect elements, so the
result depends only on the length.  Free theorem: `f (xs.map g) = f xs`.
@@@ -/

def len' : ∀ α : Type, List α → Nat := fun _ xs => xs.length
#eval len' Nat ([1, 2, 3].map (· * 10))   -- 3  = f (map g xs)
#eval len' Nat [1, 2, 3]                    -- 3  = f xs

/-! @@@
**`∀ α, List α → List α`: rearrange, drop, duplicate — never invent.**  Every output
element came from the input; which positions are kept is chosen by shape alone.  So `f`
commutes with `map`, and the output length depends only on the input length.  `reverse`,
`id`, `tail`, and `fun _ => []` inhabit it; "the singleton of the largest element" does
not — it would have to compare elements the type forbids it to inspect.
@@@ -/

def rev' : ∀ α : Type, List α → List α := fun _ xs => xs.reverse
#eval rev' Nat ([1, 2, 3].map (· * 10))   -- [30, 20, 10]  = f (map g xs)
#eval (rev' Nat [1, 2, 3]).map (· * 10)    -- [30, 20, 10]  = (map g) (f xs)

/-! @@@
### The boundary of free theorems

A polymorphic signature can force *naturality*, *no-invention*, and *shape-only*
behaviour — but never a property that depends on the element *values*.  No
`∀ α, List α → List α` forces "the output is a permutation of the input" (`reverse`
satisfies it, but `fun _ => []` inhabits the same type); "sorted" is further out of
reach, since sorting must *compare* elements.  Those properties need a specification
carried *in addition to* the type — the subtype/`Prop` specifications of Weeks 9 and 11.
Free theorems tell you what you get for free; their boundary tells you where a written
specification becomes unavoidable.

This reading is the inverse of the **derivation** method of Week 2 (§2.6): where the
derivation is forced, the free theorem is total.  Building a term from a type and
reading what every term of a type must do are one skill in two directions.
@@@ -/

/-! @@@
## 7.3  Bounded polymorphism: type class constraints

Sometimes a polymorphic function needs *some* knowledge about the type.
Type classes express this: `[DecidableEq α]` says "α must have a
decidable equality test."  The constraint is explicit in the type.
@@@ -/

-- Without DecidableEq, we cannot compare elements
def contains [DecidableEq α] (x : α) : List α → Bool
  | []      => false
  | h :: t  => x == h || contains x t

-- The type class constraint is part of the specification:
-- "for any type α with decidable equality, ..."
theorem contains_spec [DecidableEq α] (x : α) (xs : List α) :
    contains x xs = true ↔ x ∈ xs := by
  induction xs with
  | nil => simp [contains]
  | cons h t ih =>
    simp only [contains, List.mem_cons]
    constructor
    · intro hc
      by_cases heq : x = h
      · left; exact heq
      · right
        have : contains x t = true := by
          have hne : (x == h) = false := beq_eq_false_iff_ne.mpr heq
          simp [hne] at hc
          exact hc
        exact ih.mp this
    · intro hm
      cases hm with
      | inl heq => simp [heq]
      | inr ht  =>
        simp
        right
        exact ih.mpr ht

/-! @@@
> **Checkpoint — `contains`.** `contains` needs `[DecidableEq α]` to test elements.
> **Predict** both Booleans, then check.
@@@ -/

#eval contains 3 [1, 2, 3]   -- predict
#eval contains 9 [1, 2, 3]   -- predict

/-! @@@
## 7.4  The DecidableEq type class

`DecidableEq α` is a type class that provides, for every pair `a b : α`,
a decision: either a proof that `a = b` or a proof that `a ≠ b`.

```lean
class DecidableEq (α : Type u) where
  decEq : (a b : α) → Decidable (a = b)
```

Instances of `Decidable`:
```lean
inductive Decidable (p : Prop) where
  | isFalse : ¬p → Decidable p
  | isTrue  :  p → Decidable p
```

A `Decidable` value IS either a proof of `p` or a proof of `¬p`.
When `decide` is used as a proof term, it extracts the `isTrue h`
component and provides `h : p`.

Types with `DecidableEq`: `Nat`, `Int`, `Bool`, `Char`, `String`,
`List α` (when α has it), `Option α` (when α has it), and all types
you define with `deriving DecidableEq`.

Types WITHOUT `DecidableEq`: functions `α → β` in general (you cannot
check `f = g` by running them), and — crucially — `Float`.
@@@ -/

-- Nat has DecidableEq:
example : DecidableEq Nat := inferInstance
example : (3 : Nat) = 3 ∨ (3 : Nat) ≠ 3 := by decide

-- Bool has DecidableEq:
example : DecidableEq Bool := inferInstance

-- List Nat has DecidableEq:
example : DecidableEq (List Nat) := inferInstance
example : ([1, 2, 3] : List Nat) = [1, 2, 3] := by decide

/-! @@@
> **Checkpoint — `DecidableEq (List Nat)`.** **Predict** the Boolean below, and say *why*
> `List Nat` has `DecidableEq` (but `List Float` would not), before reading the result.
@@@ -/

#eval decide (([1, 2, 3] : List Nat) = [1, 2, 3])   -- predict first

/-! @@@
## 7.5  Float and the absence of DecidableEq

`Float` represents IEEE 754 double-precision floating-point numbers.
IEEE 754 specifies that `NaN ≠ NaN` — the special "not a number" value
is not equal to itself.

This violates the *reflexivity* of equality: `∀ x, x = x`.
Lean's equality is reflexive by definition (`rfl : a = a`).
If `Float` had `DecidableEq`, we could derive `NaN = NaN` (by `rfl`),
contradicting IEEE 754.

Therefore `Float` does NOT have a `DecidableEq` instance in Lean.
This is not a missing feature.  It is the type system correctly
refusing to certify something that is not true.

The practical consequence:
- You CANNOT use `decide` to prove propositions involving `Float` equality.
- You CANNOT use `Float` values as keys in structures requiring `DecidableEq`.
- Specifications about floating-point programs must use `Real` or `Rat`
  for the mathematical content, with a separate claim about approximation.

More importantly, this is a lesson that applies in *every* programming language:
**never use `==` to compare floating-point values.**
The same IEEE 754 semantics that breaks `DecidableEq` here — `NaN ≠ NaN`, and
rounding means two computations of "the same" value may produce slightly different
results — make floating-point equality unreliable in Python, Java, C, and everywhere
else.  Always compare floats with a tolerance: `|x - y| < ε`.
@@@ -/

-- Float DOES have BEq (Boolean equality), but that is NOT the same as =
#check (inferInstance : BEq Float)   -- BEq Float is available

-- BEq.beq : α → α → Bool   -- a computation returning Bool
-- Decidable (a = b)          -- a proof of a logical claim
-- These are different things.

-- The == operator on Float uses BEq, not DecidableEq.
-- It handles NaN by returning false, matching IEEE 754.
-- #eval (Float.nan == Float.nan : Bool)    -- false  (IEEE 754)

-- But we CANNOT write:
-- example : (1.0 : Float) = 1.0 := decide   -- DOES NOT COMPILE

-- We CAN write specifications using Real (the mathematical reals):
-- "the floating-point addition of x and y approximates real addition"
-- ∀ x y : Float, |Float.toReal (x + y) - (Float.toReal x + Float.toReal y)| < ε
-- This is a real-valued specification; its verification uses a different
-- methodology (floating-point error analysis).

/-! @@@
> **Checkpoint — Float has `BEq`, not `DecidableEq`.** `==` on Float is IEEE 754 `BEq`
> (a `Bool`), *not* provable equality.  **Predict** the Boolean below — is `NaN` equal to
> itself? — then check, and say why this is exactly what forbids `DecidableEq Float`.
@@@ -/

#eval ((0.0 / 0.0 : Float) == (0.0 / 0.0 : Float))   -- 0/0 is NaN; predict (IEEE 754)

/-! @@@
## 7.6  Summary: the decidability boundary

**Reading `∀` and `∃`.**  Two quantifiers appear throughout this table
and the rest of the course.  Read them aloud as follows:

- `∀ x : α, P x` — "for every `x` of type `α`, the proposition `P x` holds"
- `∃ x : α, P x` — "there exists some `x` of type `α` such that `P x` holds"

Both are types.  A proof of `∀ x : α, P x` is a *function* `(x : α) → P x` —
given any `x`, produce a proof of `P x`.  A proof of `∃ x : α, P x` is a
*dependent pair* `⟨witness, proof⟩` — a specific value together with a proof
that the claim holds for that value.

| Proposition form | Decidable? | Proof term |
|-----------------|-----------|------------|
| `a = b` for `Nat`, `Bool`, `List Nat`, etc. | Yes | `decide` |
| `a < b` for `Nat`, `Int` | Yes | `decide` |
| `∀ x ∈ xs, P x` (finite `xs`, decidable `P`) | Yes | `decide` |
| `∃ x ∈ xs, P x` (finite `xs`, decidable `P`) | Yes | `decide` |
| `a = b` for `Float` | **No** | Cannot be proved with `decide` |
| `a = b` for function types | **No** | Not decidable in general |
| `∀ n : Nat, P n` (unbounded) | Not in general | Requires a proof |
| `∃ n : Nat, P n` (unbounded) | Not in general | Requires a witness + proof |

This table is one of the most important things in the course.
@@@ -/

/-! @@@
> **Checkpoint — the decidability boundary.** A *bounded* quantifier over a literal list
> is decidable; an *unbounded* one over `Nat` is not.  **Predict** the Boolean below, then
> say why the `∀ n : Nat, …` version could not be checked this way.
@@@ -/

#eval decide (∀ x ∈ ([1, 2, 3] : List Nat), x < 10)   -- predict

/-! @@@
## Exercises

Banners read `[id] · competency · tier · level · target`; build exercises ship a
`#guard` **acceptance check** (see `EXERCISE_CONVENTIONS.md`).  Do every **core**
exercise; **stretch** is optional.

---

**[E7.1]** · *inhabitation + specification writing* · tier 1 · **core** · target `myNub`

Define `myNub [DecidableEq α] : List α → List α` removing duplicates.  State its spec —
*"every result element is in the input, and no element repeats"* — then confirm via
*checkable properties* (order-independent, so any correct implementation passes):

```lean
#guard (myNub [1, 1, 2, 3, 3, 3]).Nodup
#guard (myNub [1, 1, 2, 3, 3, 3]).length = 3
#guard decide (∀ x ∈ myNub [1, 1, 2, 3, 3, 3], x ∈ [1, 1, 2, 3, 3, 3]) = true
```

---

**[E7.2]** · *decidability identification* · tier 1 · **core**

For each, state whether `decide` can close it and **why**, using the §7.6 boundary
table — *then* check only the ones that are decidable:

(a) `("hello" : String) = "hello"`   (b) `(1.0 : Float) = 1.0`
(c) `([1,2,3] : List Nat) = [1,2,3]`  (d) `∀ n : Nat, n + 0 = n`

```lean
#guard decide (("hello" : String) = "hello") = true
#guard decide (([1, 2, 3] : List Nat) = [1, 2, 3]) = true
-- (b) and (d) have no check on purpose: say why decide cannot close each.
```

---

**[E7.3]** · *counterexample finding* · tier 1 · **core**

A student claims *"`contains x xs = true` iff `x` is the head of `xs`."*  It is
**wrong**.  Find inputs where `contains` is `true` but `x` is not the head, and encode
the witness so the check **succeeds**:

```lean
#guard contains 3 [1, 2, 3] = true
#guard [1, 2, 3].head? ≠ some 3
```

What is the *correct* characterization of `contains x xs = true`?  (It is
`contains_spec`, §7.3 — read it.)

---

**[E7.4]** · *type-directed derivation* · tier 2 · **core** · target `second`

Derive `second : α → β → β` (return the second argument).  Give a **derivation trace**
(Week 2 §2.6) and show every step is **forced** — this type has exactly one inhabitant.  Contrast with
`myConst : α → β → α` (§7.1): same shape, the *other* projection.  Effort: 2 trace steps.

```lean
#guard second 1 2 = 2
#guard second "x" (5 : Nat) = 5
```

---

**[E7.5]** · *type reading (free theorems)* · tier 2 · **core**

The chapter intro says a polymorphic `f : List α → List α` "can only permute, drop, or
duplicate."  Read that off the type: state two things **every** inhabitant of `∀ α, List
α → List α` must satisfy and one thing it **cannot** do.  Then: how many inhabitants does
`∀ α β, α → β → α` have, and why?  (Builds on §7.2 — no code to submit.)

---

**[E7.6]** · *inhabitation + decidability identification* · tier 1 · **stretch** · target `Color`

Define `inductive Color where | Red | Green | Blue deriving DecidableEq`.  Use `decide`
to settle both, then explain why the bounded `∀ c ∈ […]` is decidable here but the same
shape over **all** `Nat` (§7.6) is not:

```lean
#guard decide (Color.Red ≠ Color.Blue) = true
#guard decide (∀ c ∈ [Color.Red, Color.Green, Color.Blue], c = Color.Red ∨ c ≠ Color.Red) = true
```
@@@ -/

end W07
