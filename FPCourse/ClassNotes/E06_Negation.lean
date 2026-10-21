/- @@@

# Notes 9/21/26


- Curry-Howard Injection: Deductive Reasoning (Prop) => Computation (Type)

- Deep vs Shallow embedding of abstract theories into Lean 4
  - Deep embedding: Syntax as a type with constructor for each kind of term (propositional logic)
  - Shallow embedding: Syntax as collection of types, one for each kind of term (predicate logic)

  - Empty and False
  - Unit and True
  - Prod and And
  - Sum and Or
  - -> Empty and -> False (Not!)


@@@ -/

def e2e : Empty → Empty
| e => e

def fimpf : False → False
| f => f

inductive MyEmpty : Type where

def me2e : MyEmpty → Empty
| m => nomatch m

inductive MyFalse : Prop where
-- | mk

theorem myFalseIsReallyFalse : MyFalse → False
| m => nomatch m

def neg (a : Prop) : Prop := a → False

#check MyFalse

example : neg MyFalse
| m => nomatch m

example : ¬MyFalse
| m => nomatch m

#check (@And)

inductive KevinIsFromCville : Prop where
| driversLicense

example : KevinIsFromCville := KevinIsFromCville.driversLicense

inductive JorgIsFromToronto : Prop where
| driversLicense
| utilityBill
| healthCard

example : And KevinIsFromCville JorgIsFromToronto :=
And.intro
  KevinIsFromCville.driversLicense
  JorgIsFromToronto.healthCard

inductive Cat : Type where
| siamese
| tabby

example : ¬ (Cat.tabby = Cat.siamese)
| m => nomatch m

example :
JorgIsFromToronto.driversLicense = JorgIsFromToronto.healthCard :=
rfl


example{P : Prop} : ¬(P ∧ ¬P) :=
  fun (pnp : P ∧ ¬P) =>
    pnp.right pnp.left

/- @@@
## Predicates

Every proposition so far has been a fixed claim: `KevinIsFromCville`,
`P ∧ ¬P`, `¬¬P → P`. A *predicate* generalizes the idea. Informally,
a predicate is a property that a value may or may not have: *is
even*, *is empty*, *is less than ten*. Think of it as a sentence
with a hole in it, "___ is even", which becomes a definite
proposition only once the hole is filled with a particular value.

Lean 4 needs no new machinery to express this. A predicate on a
type α is simply a *function from α to `Prop`*:

- `P : α → Prop` is a predicate on α,
- `P a`, for `a : α`, is a proposition, something we can try to prove,
- so a predicate is a whole *family* of propositions, one for each
  value of α.

Here is a predicate on `Nat` and two of the propositions it yields.
Note the types reported by `#check`. For a definition Lean prints
the signature, `IsZero (n : Nat) : Prop`; the `@` form shows the
same thing as a function type, `Nat → Prop`. Each *application*
of the predicate is a `Prop`.
@@@ -/

def IsZero (n : Nat) : Prop := n = 0

#check IsZero         -- IsZero (n : Nat) : Prop
#check @IsZero        -- Nat → Prop, a predicate
#check IsZero 0       -- Prop, a proposition
#check IsZero 1       -- Prop, also a proposition

/- @@@
`IsZero 0` unfolds to `0 = 0`, which `rfl` proves. `IsZero 1`
unfolds to `1 = 0`, a perfectly well formed proposition that
happens to be false, so we can prove its negation instead. Being
a predicate application says nothing about being true.
@@@ -/

example : IsZero 0 := rfl
example : ¬IsZero 1 := fun h => Nat.one_ne_zero h

/- @@@
Predicates do not have to be named. A function literal from values
to propositions is a predicate too.
@@@ -/

#check fun n : Nat => n > 3

/- @@@
A predicate may take extra parameters before the value it is
about. Here `Between lo hi` is a predicate on `Nat` for each
choice of bounds, built from the connectives we already know.
@@@ -/

def Between (lo hi n : Nat) : Prop := lo ≤ n ∧ n ≤ hi

example : Between 0 10 4 := And.intro (Nat.zero_le 4) (Nat.le_add_left 4 6)

/- @@@
A predicate of two arguments, `α → α → Prop`, is what we usually
call a *relation*: it asserts that a property holds *of a pair*.
Equality and ≤ on `Nat` are exactly this, and the second is defined
inductively, which is how such predicates are often given.
@@@ -/

#check @Eq             -- {α : Sort u_1} → α → α → Prop
#check @Nat.le         -- Nat → Nat → Prop

def Divides (d n : Nat) : Prop := n % d = 0

#check Divides 3       -- Nat → Prop, "is divisible by three"

example : Divides 3 9 := rfl
example : ¬Divides 3 10 := fun h => nomatch h

/- @@@
One distinction is worth stressing, because Lean maintains it
carefully. A predicate returns a `Prop`, a *proposition* whose
proofs are evidence. A function returning `Bool` returns *data*,
the result of a *computation*. `isZeroBool 1` evaluates to `false`;
`IsZero 1` does not evaluate to anything, it is a claim we can
refute. Propositions are what we reason about; Booleans are what
we compute with. Connecting the two, deciding a proposition by
running a Boolean test, is the topic of decidability.
@@@ -/

def isZeroBool (n : Nat) : Bool := n == 0

#check @isZeroBool     -- Nat → Bool, a decision procedure
#eval isZeroBool 1     -- false, a computed value

/- @@@
Predicates are what the quantifiers quantify over. `∀ x : α, P x`
says every value of α satisfies the predicate P, and `∃ x : α, P x`
says at least one does. Having predicates in hand, we take up the
second of these in `E07_Exists.lean`.
@@@ -/

/- @@@
@@@ -/

example
  (em : ∀ (X : Prop),  X ∨ ¬X) :
  ¬(P ∧ Q) → ¬P ∨ ¬Q :=
  fun npandq =>
    match (em P) with
    | Or.inl p =>
      match (em Q) with
      | Or.inl q =>  False.elim (npandq (And.intro p q))
      | Or.inr nq => Or.inr nq
    | Or.inr np => Or.inl np
