-- FPCourse/T05_AbstractTypesAndTypeClasses/W12_TypeClassesDecidable.lean
import Mathlib.Data.List.Basic
import Mathlib.Logic.Basic

/-! @@@
# Type Classes and the Decidable Type

## What a type class really is

A type class is an interface with implementations provided by instances.
We have seen type classes as abstract types (Week 11).  This week we
examine type classes as *algebraic structures* — sets with operations
satisfying laws.

More importantly, we examine `Decidable` itself as an inductive type.
Understanding `Decidable` as a data type — not magic — completes the
picture of how `decide` works as a term-mode proof producer.
@@@ -/

namespace W12

/-! @@@
## 12.1  Decidable: an inductive type carrying proofs

`Decidable` is defined in Lean's core library as:

```lean
inductive Decidable (p : Prop) where
  | isFalse : ¬p → Decidable p
  | isTrue  :  p → Decidable p
```

This is an ordinary inductive type.  A value of type `Decidable p` is
either:
- `isFalse h` where `h : ¬p` — a proof that p is false, OR
- `isTrue h`  where `h : p`  — a proof that p is true.

`Decidable p` does not just say "p is true or false" — it *provides*
the proof of whichever is the case.

**Evaluation.**  `decide` is not magic — it evaluates.  When you write
`by decide` to prove `p`, Lean:
1. Looks up the `Decidable p` instance (a value of type `Decidable p`).
2. *Evaluates* that instance to its normal form.
3. If the normal form is `isTrue h`, the proof `h : p` is extracted and
   used.  The goal is closed.
4. If the normal form is `isFalse h`, elaboration fails — the goal is
   `p` but only a refutation exists.

The whole operation is reduction: evaluate the `Decidable` term, inspect
the constructor, extract the payload.  Every `by decide` in this course
is exactly these four steps.

`decide` used as a proof term extracts the `isTrue h` component and
returns `h : p`.  If the instance is `isFalse _`, the file fails to
compile.
@@@ -/

-- We can inspect Decidable values directly:
#check @Decidable.isTrue   -- ∀ {p : Prop}, p → Decidable p
#check @Decidable.isFalse  -- ∀ {p : Prop}, ¬p → Decidable p

-- A Decidable value IS the proof:
example : Decidable (1 < 2) := Decidable.isTrue (by decide)
example : Decidable (2 < 1) := Decidable.isFalse (by decide)

-- The decEq function for Nat:
#check @Nat.decEq   -- (a b : Nat) → Decidable (a = b)

-- For any decidable proposition, we can extract the proof or refutation:
theorem toProofOrRefutation (p : Prop) [d : Decidable p] : p ∨ ¬p :=
  match d with
  | Decidable.isTrue h  => Or.inl h
  | Decidable.isFalse h => Or.inr h

/-! @@@
> **Checkpoint — `decide` evaluates the `Decidable` instance.** `decide p` reduces the
> `Decidable p` value and reports the constructor it lands on: `isTrue` shows as `true`,
> `isFalse` as `false`.  **Predict** both Booleans below, and say which constructor each
> instance evaluates to, before reading the result.
@@@ -/

#eval decide (1 < 2)   -- predict first (which constructor?)
#eval decide (2 < 1)   -- predict first (which constructor?)

/-! @@@
## 12.2  DecidableEq as a type class instance

`DecidableEq α` is a type class (an alias for `(a b : α) → Decidable (a = b)`).
An instance provides, for every pair of elements, a decision procedure.
@@@ -/

-- Inspecting a DecidableEq instance:
#check (@Nat.decEq : DecidableEq Nat)

-- Using a DecidableEq instance explicitly:
def eqTest [DecidableEq α] (a b : α) : String :=
  match decEq a b with
  | Decidable.isTrue _  => "equal"
  | Decidable.isFalse _ => "not equal"

/-! @@@
> **Checkpoint — `eqTest` reads the `DecidableEq` decision.** `eqTest` matches on
> `decEq a b`, branching on whether the decision is `isTrue` or `isFalse`.  **Predict**
> both strings below — and which constructor each `decEq` call produces — then check.
@@@ -/

#eval eqTest (3 : Nat) 3    -- predict first ("equal" / "not equal"?)
#eval eqTest (3 : Nat) 4    -- predict first ("equal" / "not equal"?)

/-! @@@
## 12.3  Functor as a type class

A `Functor` is a type constructor `F : Type → Type` equipped with a
`map` operation satisfying the two functor laws.
@@@ -/

-- Our own Functor class with laws:
class MyFunctor (F : Type → Type) where
  fmap : (α → β) → F α → F β
  map_id  : ∀ (x : F α), fmap id x = x
  map_comp : ∀ (f : β → γ) (g : α → β) (x : F α),
      fmap (f ∘ g) x = fmap f (fmap g x)

-- List instance: the laws are theorems we proved in Week 8.
instance : MyFunctor List where
  fmap     := List.map
  map_id   := List.map_id
  map_comp := fun f g xs => by simp [← List.map_map]

-- Option instance:
instance : MyFunctor Option where
  fmap     := Option.map
  map_id   := fun o => congr_fun Option.map_id o
  map_comp := fun f g o => (Option.map_map f g o).symm

/-! @@@
> **Checkpoint — `MyFunctor.fmap`.** The `List` instance sets `fmap := List.map`, the
> `Option` instance `fmap := Option.map`; the same overloaded `fmap` dispatches on the
> container.  **Predict** both results below, then check.
@@@ -/

#eval MyFunctor.fmap (· + 1) [1, 2, 3]            -- predict (List instance)
#eval MyFunctor.fmap (· + 1) (some (5 : Nat))     -- predict (Option instance)

/-! @@@
## 12.4  Foldable as a type class
@@@ -/

class MyFoldable (F : Type → Type) where
  fold : (α → β → β) → β → F α → β

instance : MyFoldable List where
  fold := List.foldr

instance : MyFoldable Option where
  fold := fun f z o => o.elim z (fun x => f x z)

-- Specification: fold on List with cons/nil reconstructs the list
theorem list_fold_spec (xs : List α) :
    MyFoldable.fold (· :: ·) [] xs = xs :=
  List.foldr_cons_nil

-- Specification: fold on Option
theorem option_fold_none (f : α → β → β) (z : β) :
    MyFoldable.fold f z (none : Option α) = z :=
  rfl

theorem option_fold_some (f : α → β → β) (z : β) (x : α) :
    MyFoldable.fold f z (some x) = f x z :=
  rfl

/-! @@@
> **Checkpoint — `MyFoldable.fold` on `List`.** The `List` instance is `List.foldr`, so
> `fold (· + ·) 0` sums the elements.  **Predict** the total below, then check.
@@@ -/

#eval MyFoldable.fold (· + ·) 0 [1, 2, 3, 4]   -- predict first

/-! @@@
> **Checkpoint — `list_fold_spec`.** Folding with the list constructors themselves,
> `fold (· :: ·) []`, rebuilds the input (that is exactly `list_fold_spec`).  **Predict**
> the result below *from the spec* — not by simulating the fold — then check.
@@@ -/

#eval MyFoldable.fold (· :: ·) ([] : List Nat) [1, 2, 3]   -- predict from list_fold_spec

/-! @@@
## 12.5  Monoid: an algebraic structure with laws
@@@ -/

class MyMonoid (α : Type) where
  one  : α
  mul  : α → α → α
  mul_one   : ∀ a : α, mul a one = a
  one_mul   : ∀ a : α, mul one a = a
  mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)

-- Nat under addition:
instance : MyMonoid Nat where
  one       := 0
  mul       := (· + ·)
  mul_one   := Nat.add_zero
  one_mul   := Nat.zero_add
  mul_assoc := Nat.add_assoc

-- List under append:
instance : MyMonoid (List α) where
  one       := []
  mul       := (· ++ ·)
  mul_one   := List.append_nil
  one_mul   := List.nil_append
  mul_assoc := List.append_assoc

/-! @@@
> **Checkpoint — `MyMonoid Nat` (addition).** This instance reads `one := 0`,
> `mul := (· + ·)`.  **Predict** the two values below — the product and the identity —
> then check.
@@@ -/

#eval MyMonoid.mul (3 : Nat) 4     -- predict first (mul is +)
#eval (MyMonoid.one : Nat)         -- predict first (the identity)

/-! @@@
> **Checkpoint — `MyMonoid (List α)` (append).** Here `one := []`, `mul := (· ++ ·)`.
> Predict the concatenation and the identity below — the *same* class methods, a different
> instance — then check.
@@@ -/

#eval MyMonoid.mul [1, 2] ([3, 4] : List Nat)   -- predict first (mul is ++)
#eval (MyMonoid.one : List Nat)                 -- predict first (the identity)

/-! @@@
## 12.6  The boundary, revisited

After twelve weeks, we can state the decidability boundary precisely.

`Decidable p` holds (has an instance) when there is a terminating
algorithm that produces either `isTrue h : p` or `isFalse h : ¬p`.

The boundary is not arbitrary:
- **Nat equality**: decidable. Algorithm: compare digit by digit.
- **List equality** (when element equality is decidable): decidable.
  Algorithm: compare element by element.
- **Float equality**: NOT decidable soundly, because NaN ≠ NaN would
  require an algorithm that produces `isFalse h : ¬(NaN = NaN)`, but
  `rfl : NaN = NaN` would refute it.  The instance cannot exist.
- **Function equality**: NOT decidable in general.  To check `f = g`
  you would need to check all inputs — infinitely many.
- **∀ n : Nat, P n**: NOT decidable in general.  There is no algorithm
  that terminates and checks all natural numbers.
  (This is related to the halting problem.)

Understanding what is and is not decidable — and WHY — is one of the
foundational concepts of computer science.
@@@ -/

/-! @@@
> **Checkpoint — bounded vs. unbounded `∀`.** A `∀ n ∈ xs` over a *literal* list is
> decidable (finitely many checks); the *unbounded* `∀ n : Nat` on the last table row is
> not.  **Predict** the Boolean below, then say why replacing the list with "all of `Nat`"
> would put it past the boundary.
@@@ -/

#eval decide (∀ n ∈ ([0, 1, 2, 3] : List Nat), n + 0 = n)   -- predict first

/-! @@@
## Exercises

Each exercise carries a banner — `[id] · competency · tier · level · target` — and,
where it asks you to build something, an **acceptance check**: paste it beneath your
definition in your own file and it must succeed.  `#guard` is silent on success and
errors on failure, so the compiler is your grader.  See `EXERCISE_CONVENTIONS.md` for
the schema.  Do every **core** exercise; **stretch** exercises go deeper and are
optional.

---

**[E12.1]** · *specification writing* · tier 1 (+ tier-3 reading) · **core** · target `MonoidIdSpec`

The `MyMonoid Nat` instance (§12.5) claims `0` is a two-sided identity for `+`.  State the
two identity laws as `Prop`s —
`MulOneSpec : Prop := ∀ a : Nat, MyMonoid.mul a MyMonoid.one = a` and its mirror
`OneMulSpec`.  Do **not** prove the general `∀`; that proof is `Nat.add_zero` /
`Nat.zero_add`, wired into the instance in §12.5 for you to *read* (tier 3).  Confirm the
spec on instances — including the identity element itself and a *different* monoid (`List`,
where `one = []`):

```lean
#guard MyMonoid.mul (5 : Nat) MyMonoid.one = 5
#guard MyMonoid.mul MyMonoid.one (5 : Nat) = 5
#guard MyMonoid.mul (0 : Nat) MyMonoid.one = 0
#guard (MyMonoid.mul ([1, 2] : List Nat) MyMonoid.one) = [1, 2]
```

In one line: which tier does the *general* `∀` law live in, and which the four checks?

---

**[E12.2]** · *decidability identification* · tier 1 · **core**

For each proposition, deliver a **judgment** *before* touching `decide`: does a `Decidable`
instance exist at all, and if so can `decide` be the grader?  The judgment — not the
tool-use — is the point (§12.6).

(a) `(5 : Nat) = 5`   (b) `([1,2,3] : List Nat) = [1,2,3]`   (c) `(1.0 : Float) = 1.0`
(d) `∀ n : Nat, n < n + 1`   (e) `(id : Nat → Nat) = (fun n => n)`

```lean
#guard decide (((5 : Nat) = 5)) = true
#guard decide (([1, 2, 3] : List Nat) = [1, 2, 3]) = true
-- (c), (d), (e) have no check on purpose.  For each, state whether a Decidable
-- instance exists at all, and — when it does not (Float, functions) — name the
-- semantic reason from §12.6; for (d) say why an unbounded ∀ escapes decide even
-- though every instance of the body is provable.
```

---

**[E12.3]** · *counterexample finding* · tier 1 · **core**

A student claims *"every `MyMonoid` is commutative: `mul a b = mul b a`."*  It is
**wrong** — commutativity is not one of the three monoid laws (`mul_one`, `one_mul`,
`mul_assoc`).  Find a witness in the `List` monoid (`mul = ++`) and encode it two ways, so
each check **succeeds** on a correct counterexample:

```lean
#guard (MyMonoid.mul ([1, 2] : List Nat) [3]) ≠ MyMonoid.mul ([3] : List Nat) [1, 2]
#guard decide (¬ (MyMonoid.mul ([0, 1] : List Nat) [1] = MyMonoid.mul ([1] : List Nat) [0, 1]))
```

In one line: which of the three laws, if any, does your witness still satisfy?

---

**[E12.4]** · *type-directed derivation* · tier 2 · **core** · target `fork`

Derive `fork : (α → β) → (α → γ) → α → β × γ` applying both functions to the same input
(`fork f g a = (f a, g a)`).  The **derivation trace** (Week 2 §2.6) is the graded
artifact — then the `def`.  *First-step hint:* the type is three nested arrows, so start
with `→I` three times (introduce `f`, `g`, `a`); the goal `β × γ` is a product, so close
with `×I`, pairing one application under each component.  Effort: ~4 trace steps, 2 lines
of code.

```lean
#guard fork (· + 1) (· * 2) 5 = (6, 10)
#guard (fork (fun n => n) (fun n => n + 100) 0 : Nat × Nat) = (0, 100)
#guard (fork List.length List.reverse [7, 8, 9] : Nat × List Nat) = (3, [9, 8, 7])
```

---

**[E12.5]** · *specification reading* · tier 3 (reading) · **stretch**

Read the *provided* `toProofOrRefutation` (§12.1): it turns any `[Decidable p]` into a
proof of `p ∨ ¬p`.  Without authoring a proof, explain in one or two lines what each
`match` branch returns and why `p ∨ ¬p` is exactly the information a `Decidable p` *value*
already carries.  Then read `list_fold_spec` (§12.4): which library lemma discharges it,
and what proposition (in words) does it assert about folding with the list constructors?

---

**[E12.6]** · *decidability identification* · tier 1 · **stretch** · target `Suit`

**Part A (build + `decide`).**  Define
`inductive Suit where | hearts | diamonds | clubs | spades deriving DecidableEq, Repr`.
Use `decide` to settle a disequality and a bounded `∀`:

```lean
#guard decide (Suit.hearts ≠ Suit.spades) = true
#guard decide (∀ s ∈ [Suit.hearts, Suit.diamonds, Suit.clubs, Suit.spades],
                 s = Suit.hearts ∨ s ≠ Suit.hearts) = true
```

**Part B (judgment).**  Consider `∀ n : Nat, n + 0 = n`.  Every *instance* of the body is
trivially true — `n + 0` reduces definitionally to `n`, so `n + 0 = n` is `rfl`.  Predict:
does `inferInstance : Decidable (∀ n : Nat, n + 0 = n)` **succeed**?  It does **not** — and
that is the lesson.  In one or two lines, explain the gap: Lean ships no `Decidable`
instance for an *unbounded* `∀` over `Nat`, even when each body is decidable and even
trivially provable, because deciding it would require checking infinitely many `n` (§12.6).
What *does* settle the proposition — a **proof** such as `fun n => rfl` (or `Nat.add_zero`),
not a decision procedure?  Why is "every case is provable" strictly weaker than "the whole
`∀` is decidable"?  Contrast with the false `∀ n : Nat, n = n + 1`.
---

**[E12.7]** · *type-directed derivation + decidability identification* · tier 1 · **stretch** · target `mapDecide`

Write

```lean
def mapDecide [DecidableEq α] (xs ys : List α) : List (α ⊕ α) := ...
```

tagging each element of `xs` with `Sum.inl` when it also occurs in `ys`, and with `Sum.inr`
when it does not.  Say *first* why the `[DecidableEq α]` constraint is exactly what makes
this definable — which step of the computation consumes it, and what could you not write
without it?

```lean
#guard mapDecide [1, 2, 3] [2, 3, 4] = [Sum.inr 1, Sum.inl 2, Sum.inl 3]
#guard mapDecide ([] : List Nat) [1] = []
#guard mapDecide [5] ([] : List Nat) = [Sum.inr 5]
```

*First-step hint:* the shape is a `map` over `xs`; the decision inside is `x ∈ ys`, decidable
exactly because of the instance.  Effort: 2 lines of code.

@@@ -/

end W12
