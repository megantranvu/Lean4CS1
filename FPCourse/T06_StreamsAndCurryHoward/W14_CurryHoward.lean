-- FPCourse/T06_StreamsAndCurryHoward/W14_CurryHoward.lean
import Mathlib.Data.List.Basic
import Mathlib.Logic.Basic

/-! @@@
# The Curry-Howard Correspondence

## Naming what you already know

By this point in the course you have been living the Curry-Howard
correspondence for thirteen weeks.  This week we name it, state it
precisely, and see it embodied in the capstone: a type-checker whose
type *is* its correctness proof.

The Curry-Howard correspondence is the observation — discovered
independently by Haskell Curry (1934) and William Howard (1969) —
that the system of *propositions and their proofs* is isomorphic to
the system of *types and their terms*.  They are not analogous.
They are the same thing, viewed from two angles.

Lean does not *implement* this correspondence.  Lean *is* a system in
which the correspondence is the foundational design principle.  You
have not been using an analogy; you have been using the real thing.

Look back at the core types introduced in this course:
`→` is implication.  `×` is conjunction.  `⊕` is disjunction.
`Unit` is truth.  `Empty` is falsehood.  `∀` is the dependent
function type; `∃` is the dependent pair type.  These are the
constituents of the Curry-Howard correspondence.  Types such as
`Option`, `List`, and `BTree` are useful programming types built
on top of that foundation, but the correspondence itself lives here.
You have been working inside it since Week 0.  This week names it.

That is also why this course is the direct prerequisite for
**CS2: Certified Proofs**.  CS2 does not introduce a new subject.
It flips the orientation: from `Type` to `Prop`, from *computing*
a value to *proving* a proposition.  Every concept covered here —
data definitions, specifications, recursion, higher-order functions,
sets, relations, type classes — ports intact to that setting.
The entire structure of this course is the foundation.
@@@ -/

namespace W14

/-! @@@
## 14.1  The correspondence table

Each row of the following table presents two views of the same concept.

| Logic (left view) | Type Theory (right view) | Lean |
|-------------------|--------------------------|------|
| Proposition P | Type P | `P : Prop` |
| Proof of P | Term of type P | `h : P` |
| P is provable | P is inhabited | `Nonempty P` |
| P → Q (implication) | Function type P → Q | `fun h : P => ...` |
| P ∧ Q (conjunction) | Product type P × Q | `And.intro : P → Q → P ∧ Q` |
| P ∨ Q (disjunction) | Sum type P ⊕ Q | `Or.inl : P → P ∨ Q` |
| ⊥ (absurdity / False) | Empty type | `False : Prop` |
| ¬P (negation) | Function type P → False | `fun h : P => False.elim ...` |
| ∀ x : α, P x | Dependent function (Π) | `(x : α) → P x` |
| ∃ x : α, P x | Dependent pair (Σ) | `⟨witness, proof⟩` |

This is not a mapping we impose.  These are the same thing.
@@@ -/

-- Every row of the table, demonstrated:

-- Proposition / Type:
#check (1 + 1 = 2 : Prop)          -- a proposition
#check (1 + 1 = 2)                  -- the same proposition, as a type

-- Proof / Term:
example : 1 + 1 = 2 := rfl         -- rfl is the proof term

-- Implication / Function:
example : (1 = 1) → (1 = 1) := id  -- implication IS function type

/-! @@@
> **Checkpoint — `→` is implication.** Under Curry-Howard the *function* arrow and the
> *implication* arrow are one symbol. An implication between decidable propositions is
> itself decidable. **Predict** the Boolean — is `(1 = 1) → (2 = 2)` true? — then check.
@@@ -/

#eval decide ((1 = 1) → (2 = 2))   -- predict first

-- Conjunction / Product:
example : 1 < 2 ∧ 2 < 3 :=
  And.intro (by decide) (by decide)  -- And.intro IS Prod.mk for Props

/-! @@@
> **Checkpoint — `∧` is a product.** A proof of `P ∧ Q` is a *pair* of proofs, so it holds
> only when *both* conjuncts do. **Predict** the Boolean, then check.
@@@ -/

#eval decide (1 < 2 ∧ 2 < 3)   -- predict first

-- Disjunction / Sum:
example : 1 = 1 ∨ 1 = 2 := Or.inl rfl  -- Or.inl IS Sum.inl for Props

/-! @@@
> **Checkpoint — `∨` is a sum.** A proof of `P ∨ Q` is a *tagged* proof — `inl` or `inr` —
> so it holds when *at least one* disjunct does. Here the left side carries it. **Predict**
> the Boolean, then check.
@@@ -/

#eval decide (1 = 1 ∨ 1 = 2)   -- predict first

/-! @@@
> **Checkpoint — `¬P` is `P → False`.** Negation is the function type into the empty type:
> `¬P` holds exactly when `P` is false (so the function is vacuous). **Predict** the Boolean
> for `¬ (1 = 2)`, then check.
@@@ -/

#eval decide (¬ (1 = 2))   -- predict first

-- ∀ / Π type:
example : ∀ n : Nat, n + 0 = n := Nat.add_zero  -- a dependent function

/-! @@@
> **Checkpoint — `∀` is a dependent function.** A proof of `∀ n, P n` is a *function*
> sending each `n` to a proof of `P n`. Over a *finite* list the claim is decidable.
> **Predict** the Boolean below, then check.
@@@ -/

#eval decide (∀ n ∈ ([0, 1, 2, 3] : List Nat), n + 0 = n)   -- predict first

-- ∃ / Σ type:
example : ∃ n : Nat, n > 100 := ⟨101, by decide⟩  -- a dependent pair

/-! @@@
> **Checkpoint — `∃` is a dependent pair.** A proof of `∃ n, P n` is a *pair* `⟨w, proof⟩`:
> a witness and a proof it works. Over a finite list the search is decidable. **Predict**
> the Boolean — is there an element `> 100` in `[50, 101]`? — then check.
@@@ -/

#eval decide (∃ n ∈ ([50, 101] : List Nat), n > 100)   -- predict first

/-! @@@
## 14.2  Proofs ARE terms: a demonstration

The following function and theorem look syntactically identical.
That is not a coincidence.
@@@ -/

-- A computational function:
def addOne : Nat → Nat := fun n => n + 1

-- A proof of an implication:
theorem oneImpliesOne : (1 = 1) → (1 = 1) := fun h => h

/-! @@@
> **Checkpoint — a proof IS a term.** `addOne = fun n => n + 1` and `oneImpliesOne =
> fun h => h` are built the *same way*; only the types differ. `addOne` is data, so it
> evaluates. **Predict** `addOne 41`, then check.
@@@ -/

#eval addOne 41   -- predict first

-- They have the same structure.  The types are different —
-- Nat and Prop — but the TERMS are constructed identically.

-- More striking: ∧-introduction and pair construction
def makePair : α → β → α × β := fun a b => (a, b)
theorem makeConjunction (h1 : P) (h2 : Q) : P ∧ Q := And.intro h1 h2

/-! @@@
> **Checkpoint — `And.intro` IS `Prod.mk`.** `makePair a b` builds a `×` pair exactly as
> `makeConjunction` builds an `∧` proof — same constructor, one on data, one on `Prop`.
> **Predict** `makePair 3 "hi"`, then check.
@@@ -/

#eval makePair 3 "hi"   -- predict first

-- And.intro IS (essentially) Prod.mk, working on Props.

/-! @@@
## 14.3  The capstone: a type-checker whose type is its proof

We define a small typed language and a type-checker for it.  The
type-checker's return type includes a *proof* that the expression is
well-typed.  Any expression that passes the checker comes with a
certificate.

This is Curry-Howard in its most direct form: the act of type-checking
IS the act of proof construction.
@@@ -/

-- Types of our mini-language:
inductive Ty where
  | Nat  : Ty
  | Bool : Ty
  | Arr  : Ty → Ty → Ty   -- function type
deriving DecidableEq, Repr

-- Terms of our mini-language:
inductive Term where
  | natLit  : Nat → Term
  | boolLit : Bool → Term
  | var     : String → Term
  | app     : Term → Term → Term
  | lam     : String → Ty → Term → Term
deriving Repr

-- A typing context maps variable names to types:
def Context := List (String × Ty)

-- Context lookup:
def ctxLookup : Context → String → Option Ty
  | [],            _   => none
  | (x, τ) :: ctx, y  => if x == y then some τ else ctxLookup ctx y

/-! @@@
> **Checkpoint — `ctxLookup`.** `ctxLookup` walks the context returning the *first* binding
> whose name matches, or `none`. **Predict** the result of looking up `"y"` below, then
> check.
@@@ -/

#eval ctxLookup [("x", Ty.Nat), ("y", Ty.Bool)] "y"   -- predict first

/-! @@@
> **Checkpoint — `DecidableEq Ty`.** `Ty` derives `DecidableEq`, so the type-checker can
> compare types (it does exactly this in the `app` rule, `τ₁ = τ₁'`). **Predict** the
> Boolean — is `Nat` the same type as `Bool → Nat`? — then check.
@@@ -/

#eval decide (Ty.Nat = Ty.Arr Ty.Bool Ty.Nat)   -- predict first

/-! @@@
## 14.4  The typing relation

The typing relation `Typed ctx e τ` is an inductive proposition:
it holds exactly when expression `e` has type `τ` in context `ctx`.

This is the *specification* for the type-checker.
@@@ -/

inductive Typed : Context → Term → Ty → Prop where
  | natLit  : Typed ctx (.natLit n) .Nat
  | boolLit : Typed ctx (.boolLit b) .Bool
  | var     : ctxLookup ctx x = some τ →
              Typed ctx (.var x) τ
  | app     : Typed ctx f (.Arr τ₁ τ₂) →
              Typed ctx e τ₁ →
              Typed ctx (.app f e) τ₂
  | lam     : Typed ((x, τ₁) :: ctx) body τ₂ →
              Typed ctx (.lam x τ₁ body) (.Arr τ₁ τ₂)

/-! @@@
## 14.5  The type-checker

`typecheck ctx e` returns `some ⟨τ, h⟩` where `h : Typed ctx e τ`
if `e` is well-typed, and `none` otherwise.

The return type `Option (Σ τ, Typed ctx e τ)` IS the correctness
specification.  Any `some` result carries a proof.
@@@ -/

def typecheck : (ctx : Context) → (e : Term) →
    Option (Σ' τ, Typed ctx e τ)
  | _, .natLit _  =>
    some ⟨.Nat, Typed.natLit⟩
  | _, .boolLit _ =>
    some ⟨.Bool, Typed.boolLit⟩
  | ctx, .var x     =>
    match h : ctxLookup ctx x with
    | none   => none
    | some τ => some ⟨τ, Typed.var h⟩
  | ctx, .app f e   =>
    match typecheck ctx f, typecheck ctx e with
    | some ⟨.Arr τ₁ τ₂, hf⟩, some ⟨τ₁', he⟩ =>
      if h : τ₁ = τ₁' then
        some ⟨τ₂, Typed.app hf (h ▸ he)⟩
      else none
    | _, _ => none
  | ctx, .lam x τ₁ body =>
    match typecheck ((x, τ₁) :: ctx) body with
    | some ⟨τ₂, hbody⟩ => some ⟨.Arr τ₁ τ₂, Typed.lam hbody⟩
    | none              => none

/-! @@@
> **Checkpoint — the checker types a literal.** `(typecheck ctx e).map (·.1)` reads off the
> *type* the checker assigns (discarding the proof). A `natLit` always types as `Nat`.
> **Predict** the `Option Ty` below, then check.
@@@ -/

#eval (typecheck [] (Term.natLit 5)).map (·.1)   -- predict first

/-! @@@
> **Checkpoint — the checker types the identity λ.** `λx:Nat. x` should type as `Nat → Nat`
> — the `lam` rule wraps the body's type in an `Arr`. **Predict** the `Option Ty` below,
> then check.
@@@ -/

#eval (typecheck [] (Term.lam "x" Ty.Nat (Term.var "x"))).map (·.1)   -- predict first

/-! @@@
> **Checkpoint — the checker rejects an ill-typed term.** Applying `1` to `2` (`app` of a
> `natLit` to a `natLit`) has no typing: the function position is not an `Arr`, so the
> `app` rule fails and the result is `none`. **Predict** the `Option Ty` below, then check.
@@@ -/

#eval (typecheck [] (Term.app (Term.natLit 1) (Term.natLit 2))).map (·.1)   -- predict first

/-! @@@
## 14.6  Soundness: every result is correct

Soundness follows immediately from the return type: any time `typecheck`
returns `some ⟨τ, h⟩`, `h` IS the proof that the term has type `τ`.
There is no gap between the checker and the proof.

**Evaluation.**  The type-checker *is* an evaluator — it reduces the
term `e` through the pattern-match clauses of `typecheck`, each step
applying one rule of the typing relation, until it reaches a leaf
(`natLit`, `boolLit`, `var`) or fails.  The proof `h` is not constructed
separately; it is the *value produced by evaluation of `typecheck`*.
This is Curry-Howard lived from the inside: type-checking IS proof
construction, and proof construction IS evaluation.

This is in contrast with conventional type-checkers, which return a
type or an error, and whose *correctness* requires a separate proof
(in a meta-theory) that the checker matches the typing relation.

In our checker, the correctness proof is built into the return value.
The type-checker and the proof of soundness are the same program.
@@@ -/

-- Soundness: whenever `typecheck ctx e` returns `some p`, the term genuinely has the
-- type `p.1` that the checker reports — witnessed by `p.2`.  There is nothing to
-- construct: the proof IS the value the checker already produced, so soundness holds by
-- `p.2` alone.  (The converse — *completeness*, that every well-typed term is accepted —
-- is a separate property the return type does NOT give for free; it is Exercise E14.6.)
theorem typecheck_sound (ctx : Context) (e : Term)
    (p : Σ' τ, Typed ctx e τ) (_h : typecheck ctx e = some p) :
    Typed ctx e p.1 :=
  p.2

/-! @@@
## 14.7  What you have learned

You entered this course knowing that programs have types.  You leave it
knowing that:

1. **Propositions are types**.  A logical claim is a Lean type.  Its
   proofs are the terms inhabiting that type.

2. **Proof-carrying types are programs**.  A function whose type includes
   a proposition requires that proposition to be proved before it can be
   called.  The compiler enforces this.

3. **Decidability is structured**.  Some propositions have decidable
   instances — algorithms that mechanically produce the proof or the
   refutation.  Others do not.  The `Decidable` type class captures this.
   `Float` lacks `DecidableEq` for a precise mathematical reason.

4. **Specifications are types**.  `CorrectSort`, `IsBST`, `LawfulDict`,
   `Typed` — these are all types.  Satisfying a specification means
   inhabiting the type.

5. **The compiler is the verifier**.  When a file type-checks, every
   claim in every type has been verified by the elaborator.

This is the Curry-Howard correspondence, lived from the inside.

## Exercises

Each exercise carries a banner — `[id] · competency · tier · level · target` — and,
where it asks you to build something, an **acceptance check**: paste it beneath your
definition in your own file and it must succeed.  `#guard` is silent on success and
errors on failure, so the compiler is your grader.  See `EXERCISE_CONVENTIONS.md` for
the schema.  Do every **core** exercise; **stretch** exercises go deeper and are
optional.

This is the Curry-Howard capstone, so the emphasis is on **type-directed derivation**
(building a term from its type — proofs *as* programs) and its inverse, **type reading**
(reading a type to learn what every inhabitant must do).  For the derivation exercises the
graded artifact is the **derivation trace** in the Week 2 §2.6 format — not merely a term
that compiles.  `RULE` at each step is one of `→I`, `→E`, `×I`, `×E`, `⊕I`, `⊕E`, or
"use `h`".  Recall from §14.1 that `∧` behaves like `×` and `∨` like `⊕`, so the *same*
moves derive proofs and programs — that identity is the whole point of the week.

---

**[E14.1]** · *type-directed derivation* · tier 2 · **core** · target `modusPonens`

Derive `modusPonens : A → (A → B) → B` (with `A B : Type`) — a value, and a proof, and a
function application, all at once: under Curry-Howard this term *is* the inference rule
"from `A` and `A → B`, conclude `B`."  Give the **derivation trace** (§2.6 format) then the
term; name the rule closing each goal.  Effort: 3 trace steps, ~1 line.

```lean
#guard modusPonens 3 (fun n => n + 1) = 4
#guard modusPonens "hi" String.length = 2
#guard modusPonens true (fun b => !b) = false
```

*First-step hint:* the goal is an arrow into an arrow, so the first two moves are forced
(`→I` on `a : A`, then `→I` on `f : A → B`); the last goal `B` is closed by one `→E`
(`f a`).  Which hypothesis does the final application use, and which supplies its argument?

---

**[E14.2]** · *type-directed derivation* · tier 2 · **stretch** · target `distribute`

Derive `distribute : A × (B ⊕ C) → (A × B) ⊕ (A × C)` (with `A B C : Type`) — the
distributivity of `∧` over `∨`, read as a program.  Give the **derivation trace** then the
term.  Effort: ~5 trace steps.

```lean
#guard distribute ((5, Sum.inl 1) : Nat × (Nat ⊕ Nat)) = Sum.inl (5, 1)
#guard distribute ((5, Sum.inr 2) : Nat × (Nat ⊕ Nat)) = Sum.inr (5, 2)
```

*First-step hint:* after `→I` on the pair `p` and `×E` to name `p.1 : A` and `p.2 : B ⊕ C`,
the output side is not yet determined — you must `⊕E` (match) on `p.2` *before* you can
choose `⊕I` `.inl`/`.inr`, because which side of the result you build depends on which side
the input was.  State, at each step, the remaining goal.

---

**[E14.3]** · *type reading (free theorems)* · tier 2 · **core**

The inverse of derivation: read a type to learn what **every** inhabitant must do (§7.2, and
§2.6's "inverse direction").  No code to submit.

(a) `∀ A B : Type, A × B → A` — reading only the type, what must every inhabitant do, and how
many inhabitants are there?  (This is `Prod.fst`; under Curry-Howard it is the proof of
`P ∧ Q → P`, i.e. `And.left`.)

(b) `∀ A B : Type, A → A ⊕ B` — how many inhabitants, and why can no inhabitant produce a
`B`?  Name the Curry-Howard reading of this type as a logical implication.

(c) Contrast: does the type `∀ A : Type, A ⊕ B → A` have *any* inhabitant when `B` is a
type the code cannot inspect?  Say why the `.inr` case blocks it — this is where a type
*fails* to be inhabited, i.e. the proposition is *not* provable.

---

**[E14.4]** · *counterexample finding* · tier 1 · **core**

A student claims *"every `Term` is well-typed — `typecheck` assigns a type to all of them."*
It is **wrong**: an ill-typed application and an unbound variable both have *no* typing.
Find witnesses and encode them so the checks **succeed** (recall `(typecheck ctx e).map
(·.1) : Option Ty` reads off the assigned type, or `none`):

```lean
#guard (typecheck [] (Term.app (Term.natLit 1) (Term.natLit 2))).map (·.1) ≠ some Ty.Nat
#guard (typecheck [] (Term.var "x")).map (·.1) = none
#guard (typecheck [] (Term.app (Term.boolLit true) (Term.natLit 2))).map (·.1) = none
```

What is the *correct* characterization of when `typecheck ctx e` returns `some _`?  (It is
exactly when `Typed ctx e τ` is inhabited for some `τ` — read the `app` and `var` clauses of
§14.5.)

---

**[E14.5]** · *decidability identification* · tier 1 · **core**

For each Curry-Howard proposition, say **whether `decide` can close it and why** (finite
domain? decidable predicate? a `Decidable`/`DecidableEq` instance in scope?) *before*
checking — the judgment is the point, not the tool-use:

(a) `(Ty.Nat = Ty.Nat) ∧ (Ty.Bool ≠ Ty.Nat)`   (b) `∃ n ∈ ([1, 2, 3] : List Nat), n > 2`
(c) `∀ n : Nat, n + 0 = n`   (d) `Typed [] (Term.natLit 1) Ty.Nat`

```lean
#guard decide ((Ty.Nat = Ty.Nat) ∧ (Ty.Bool ≠ Ty.Nat)) = true
#guard decide (∃ n ∈ ([1, 2, 3] : List Nat), n > 2) = true
-- (c) and (d) have no check on purpose: say why decide cannot close each.  For (d),
--     note that Typed is an inductive Prop with no Decidable instance — even though
--     `typecheck` effectively decides it, `decide` needs the instance, which is absent.
```

---

**[E14.6]** · *specification writing · specification reading* · tier 2 (+ tier-3 reading) · **stretch** · target `Complete`

Two parts, one about the checker's specification.

(a) **Spec writing.** State `typecheck`'s *completeness* as a `Prop` — the converse of the
soundness the return type gives for free: *"whenever `Typed ctx e τ` holds, `typecheck ctx e`
returns a `some` whose type is `τ`."*  Write it as a single `def Complete : Prop := ∀ …`.

(b) **Spec reading (tier 3).** Read the *provided* proof `typecheck_sound` (§14.6) — do **not**
author a proof.  Explain, in one sentence each: why is soundness discharged by `p.2` alone
(what does the return type `Option (Σ' τ, Typed ctx e τ)` already guarantee)?  And why can that
same return type *not* discharge your *completeness* `Prop` from part (a) — what would a proof
of completeness have to do that soundness never does?
@@@ -/

end W14
