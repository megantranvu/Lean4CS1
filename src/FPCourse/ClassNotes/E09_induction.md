# Induction is Elimination for Inductive Types

Last class we met induction principles in the
form of *recursors* in Lean. Recursors tell you
exactly what you must do to *use* a value/proof
of a given data or proposition type. For example,
to use a `Bool` value, you must provide code that
computes an answer for each possible case or form
of a `Bool` value.


Every inductive type comes with a *recursor*, a function
Lean generates automatically from the type's constructors.
A recursor is the one principled way to consume a value of
the type: give it one case per constructor (a value, or a
function, matching that constructor's shape) and it tells
you how to produce a result for *any* value of the type.

Here's a key insight: recursors are what ultimately create
total functionso when given the means of providing a result
for each possible form/constructor of the given inductively
defined type. Lean's `match` and pattern-matching `def`s are
just friendlier notations that compile down to calls to the
recursor for a given argument type. If you understand the
recursor for a type, you understand why pattern matching on
it is allowed to look the way it does, and why it has to
cover the cases it covers.

Next we look at the recursors for five familiar types,
from the one with zero constructors up to the ones that
carry recursive data.

One wrinkle you'll meet below: Lean's compiler knows how
to turn `match`-notation (and `Nat.rec` itself) into fast
executable code, but it doesn't yet know how to compile a
*bare* call to most other recursors. So several of the
`def`s below have to be marked `noncomputable`, and we
check their results with `#reduce` (plain symbolic
evaluation in the elaborator) instead of `#eval` (which
needs compiled code). `Nat.rec` is the exception -- it
*is* directly computable, which is why `factorial` below
can use `#eval`.
## Empty / False: zero constructors

`Empty` and its `Prop` analog `False` have *no*
constructors. So its recursor needs no *case* arguments
at all, just a motive and the (impossible) value itself.
What you get back is a valid function term, albeit one
that can never be applied. This is "from a contradiction,
anything follows" (ex falso), but in the *computational*
realm.

For a concrete example, pick any computational type at
all. Take String, for example. You can for free have a
total function from Empty to String.
```lean
example : Empty → String := fun e => nomatch e
```

And it's easy to see that the same principle works for
*any* return type whatsoever.
```lean
example (α : Type u) : Empty → α := fun e => nomatch e
```

Now here's a walk-away lesson for the day. In deductive
logic as embedded in Lean, so-called *elimination rules*
for *inductively defined* propositions are applications
of the associated *recursors*, or *induction principles*.
In other words, the functions we just define ultimately
reduce to applications of the associated recursors. Here
we're given a value of type Empty, and to use it, we use
nice syntax to invoke the recursor for it. So let's look
at that!
```lean
#check @Empty.rec
```

```lean
Empty.rec :
  (motive : Empty → Sort u_1) →   -- given a function on non-existent values
  (t : Empty) →                   -- and given any such value in particular
  motive t                        -- the function will compute an answer
```
```lean
def e2s : Empty → String :=
  fun e =>
    Empty.rec
      (fun _ => String)
      e
```

There are no possible cases/forms of a value
of the Empty type, so the recursor does not
require code for any cases at all in order to
hand you back a total function from `Empty` to
any other type.
The one potentially mystifying element in the
definition is that `(fun _ => String)`. That is
the `motive : Empty → Sort u_1` argument that `Empty.rec`
asked for above. Recursors are stated for an arbitrary,
*type-valued* function from the value being eliminated,
rather than for one fixed return type, because in general
which type a function returns is allowed, in dependent
type theory, to depend on which constructor you matched
(and, for constructors carrying data, on that data too).

`Empty` has no constructors to depend on, so the motive
here just ignores its argument (`_`) and names the same
type, `String`, no matter what. Handing `Empty.rec` that
motive is how you tell it produce a `String`. It makes
`Empty.rec (fun _ => String) e` a term of type `String`,
exactly as `e2s`'s signature promises.
Reflecting the Curry-Howard correspondence the
associated logical reasoning principle, of False
elimination, is isomorphic to its computational
analog that you can always have a function taking
Empty to *any* other type *for free*.
```lean
#check @False.rec
```

```lean
False.rec :
  (motive : False → Sort u_1) →
  (t : False) →
  motive t
```
```lean
def fromEmpty (e : Empty) : Nat :=
  Empty.rec (fun _ => Nat) e

-- using nicer notation
def fromEmpty' (e : Empty) : Nat :=
  nomatch e

theorem fromFalse (h : False) : 3 = 4 :=
  False.rec (fun _ => (3 = 4)) h

-- using nicer notation
theorem fromFalse' (h : False) : 3 = 4 :=
  nomatch h
```

## Unit / True: one constructor, no data

`Unit` (and `True`) has exactly one constructor carrying
no data (`Unit.unit`, written `()`). So its recursor needs
exactly *one* case: a value to return for `Unit.unit`.
Since that's the only possible input, the recursor just
hands that one value back, no matter which `Unit` you give
it (there's only one anyway).

(`Unit` is just notation for `PUnit`, Lean's universe-
polymorphic one-element type, so its recursor is named
`PUnit.rec`.)
```lean
#check @PUnit.rec
#check @True.rec
```

```lean
@PUnit.rec :
  {motive : PUnit → Sort u_1} →
  motive PUnit.unit →
  (t : PUnit) →
  motive t
```
```lean
noncomputable def fromUnit (u : Unit) : String :=
  PUnit.rec "the one and only" u

-- noncomputable means no compiled code; #reduce doesn't need that
#reduce fromUnit ()   -- "()" is notation for Unit.unit

-- with nicer notation
noncomputable def fromUnit' (u : Unit) : String :=
  "the one and only"
```

## Bool: two constructors, no data

`Bool` has two constructors, `false` and `true`, neither
carrying data. So its recursor needs *two* cases: one
result for `false`, one for `true`. This is exactly
if-then-else, just with the cases spelled out in
constructor order.
```lean
#check @Bool.rec
```

```lean
@Bool.rec :
  {motive : Bool → Sort u_1} →
  motive false →
  motive true →
  (t : Bool) →
  motive t
```
```lean
noncomputable def describe (b : Bool) : String :=
  Bool.rec "it's false" "it's true" b

#reduce describe true
#reduce describe false

def deescribe' : Bool → String
| true => "T"
| false => "F"
```

## Nat: a recursive constructor

`Nat` has two constructors, `Nat.zero` and `Nat.succ`, and
`succ` carries another `Nat` inside it. So the recursor
needs a case for `zero`, and a case for `succ` that gets
handed *both* the smaller number `n` *and* the result
already computed for `n` (the "induction hypothesis").
That second piece is what makes it genuine recursion
rather than a one-step case split -- and it's why
induction and recursion are, underneath, the same thing.
```lean
def sumUp : Nat → Nat
| Nat.zero => 0
| Nat.succ n' =>(n' + 1) + sumUp n'

def fac : Nat → Nat
| 0 => 1
| (n' + 1) => (n' + 1) * fac n'

#eval fac 5

#check @Nat.rec
```

```lean
@Nat.rec :
  {motive : Nat → Sort u_1} →
  motive Nat.zero →
  ((n' : Nat) → motive n' → motive n'.succ) →
  (t : Nat) →
  motive t
```
```lean
def factorial (n : Nat) : Nat :=
  Nat.rec 1 (fun n ih => (n + 1) * ih) n

#eval factorial 0   -- 1
#eval factorial 5   -- 120
```

## String: one constructor, carrying data *and* a proof

In current Lean, `String` is a structure with a single
constructor holding a `ByteArray` together with a *proof*
that those bytes are valid UTF-8. So, like `Unit`, its
recursor needs only *one* case -- but here that case is a
function taking both pieces: the raw bytes, and the proof
obligation that goes with them. It's the same
proof-carrying-data idea you saw earlier with
`SquarePair`, just built into a type from the standard
library.
```lean
#check @String.rec
```

```lean
@String.rec :
  {motive : String → Sort u_1} →
  ((toByteArray : ByteArray) →
    (isValidUTF8 : toByteArray.IsValidUTF8) →
    motive { toByteArray := toByteArray, isValidUTF8 := isValidUTF8 }) →
  (t : String) →
  motive t
```
```lean
noncomputable def byteLength (s : String) : Nat :=
  String.rec (fun toByteArray _ => toByteArray.size) s

#reduce byteLength "hello"   -- 5
#reduce byteLength ""        -- 0
```

## Another Example of "Proof" by Induction

As a final reminder, constructing a proof of
a universal generalization, `∀ (x : P), Q x`,
works the same way. If there is a proof of it,
it'll be a total function from any value, `x`
of type (data or logical type) `T` to a proof
that *that* `x` in particular *satisfies* `Q`,
insofar as there is a proof of `Q x`. You need
a total function from any `x` to proofs of `Q x`,
Who's your total function buddy? The recursor
for the input type, here, `T`.
### Every Dog is Friendly or Not
Friendly.
```lean
-- Our dogs
inductive Dog : Type where | Iris | Fido | Sargent
open Dog

-- Property of being Friendly
inductive Friendly : Dog → Prop where
| irisIs : Friendly Iris
| fidoIs : Friendly Fido
-- Sargent is NOT friendly

-- Any friendly dog is pettable (safe to pet)
inductive Pettable : Dog → Prop
| canPet: ∀ (d : Dog), Friendly d → Pettable d
```

Given any dog, d, if there is a proof that
d is Friendly, then this constructor gives
you a proof that d is Pettable. So, if any
dog is friendly, then *that* dog is pettable.
```lean
open  Pettable

-- Iris is pettable
example : Pettable Iris := canPet Iris Friendly.irisIs

-- Fido is pettable
example : Pettable Fido := canPet Fido Friendly.fidoIs

-- Sargent is not pettable (proof by negation)
example : ¬Pettable Sargent :=
  fun sargIsPettable =>
    match sargIsPettable with
    | canPet Sargent sargentIs => nomatch sargentIs
```

Evidently, every dog that's friendly is pettable. We
can now state this as a top-level theorem, valid given
the particular Dog World we've modeled here.
```lean
example : ∀ d, Friendly d → Pettable d
| d, h => Pettable.canPet d h
```

This theorem proves that *all* dogs have the specified
property, of being pettable if friendly. Could we just
as well prove this theorem by induction? What would that
even mean? Induction on what? There are no Nats here.

Remember, induction is for proving universals or giving
back total functions. Where is there a universal here?
It's `∀ (d : Dog)`. So we'd use induction on Dog!
```lean
#check Dog.rec
```

```lean
Dog.rec.{u}
  {motive : Dog → Sort u}
  (Iris : motive Iris)
  (Fido : motive Fido)
  (Sargent : motive Sargent)
  -- what is `motive` here?
  -- given proofs for each dog individually
  -- you can now have a total function
  -- given *any* dog, it satisfies the predicate
  (t : Dog) :
  motive t
```
Yes. Here we prove the generalization by induction
on `Dog`, then apply it
```lean
theorem fImpP : ∀ d, Friendly d → Pettable d
| d, h =>
  Dog.rec
    (
      Pettable.canPet d h
    )
    (
       Pettable.canPet d h
    )
    (
       Pettable.canPet d h
    )
    Sargent
```

### Take-Away

You should see here that a proof by induction on
`Dog` is really just a proof by finite case analysis.
More generally, case analysis emerges as a special
case of induction for a type with finite cases.

<div class="issue-box">📝 <a href="https://github.com/kevinsullivan/Lean4CS1/issues/new">Report an issue</a> with this section</div>

