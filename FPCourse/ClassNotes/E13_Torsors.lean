/- @@@
# Torsors: Free and Transitive Group Actions

So far we've studied groups as abstract algebraic objects. But groups
are most interesting when they *act* on something: a rotation acts on
the corners of a square, a permutation acts on a sequence of elements,
a translation acts on the points of a plane.

A *torsor* for a group `G` is a set `T` where `G` acts on elements of
`T` in two special ways:
  - *Free*: no non-identity element of `G` leaves any point of `T` fixed
  - *Transitive*: any two points of `T` are related by some element of `G`

Together, these properties mean that `T` has no intrinsic identity or
structure -- all points are equivalent, and they're only distinguished
by the group action. A torsor is "a group without a distinguished element."

The phrase is worth unpacking, because it is the whole idea. A group has a
distinguished element: the identity. A torsor for `G` looks exactly like `G`
once you arbitrarily nominate one of its points to serve as "zero" -- but
nothing in the structure nominates one for you. Clock positions are like this.
There is nothing intrinsically special about 12 o'clock; it is a convention.
What *is* intrinsic is the three-hour shift that takes 12 to 3, and that
shift is a group element, not a position.

Examples: clock hours under time shifts, calendar dates under day shifts,
points in a plane under translations, directions in space under rotations.

This lesson builds on the `Group` class from the previous one, which we
import rather than redefine.
@@@ -/

import FPCourse.ClassNotes.E13_Groups

namespace Torsors

open Groups

/- @@@
## The `Torsor` Class

Four fields of data and law, plus one field that is easy to skim past and
worth slowing down for.
@@@ -/

class Torsor (G T : Type) where
  [groupG : Group G]
  act        : G → T → T
  actId      : ∀ t : T, act groupG.id t = t
  actComp    : ∀ g h : G, ∀ t : T, act (groupG.op g h) t = act g (act h t)
  actFree    : ∀ g : G, ∀ t : T, act g t = t → g = groupG.id
  actTransitive : ∀ t₁ t₂ : T, ∃ g : G, act g t₁ = t₂

/- @@@
### Why `[groupG : Group G]` Is in Square Brackets

`groupG` is a field like any other -- the laws below refer to it, writing
`groupG.id` and `groupG.op` -- but it is declared in square brackets rather
than with a colon alone. Those brackets make it *instance-implicit*, and they
change two things.

When you **build** a `Torsor`, you are not expected to type the group
structure out; Lean will look for a `Group G` instance and fill the field in.
Every instance below still mentions it, as `groupG := inferInstance`, which
is a way of saying out loud "find it by instance search" -- we keep it
explicit here because the field is new, and the following paragraph is the
only place in the course where `inferInstance` gets introduced.

When you **use** a `Torsor G T`, the group structure on `G` comes along for
free: you never have to pass `[Group G]` separately, because a torsor already
carries the group it acts by. Contrast this with `solve` in the previous
lesson, which took `[g : Group α]` as a function argument. There the brackets
were on a parameter; here they are on a *field*, so the dependency is baked
into the structure instead of being requested at each call.

The alternative design -- a plain `groupG : Group G` field -- would work, but
every instance would have to spell the group out and every user would have to
project it by hand.
@@@ -/

/- @@@
One caveat about this definition, stated plainly because it is a real gap
rather than a subtlety. The axioms above are all satisfied *vacuously* when
`T` is empty: there is no point for a group element to fix, and no pair of
points to relate. So by these axioms the empty type is a "torsor" for every
group, which is not what anyone means. The standard definition additionally
requires `T` to be nonempty, and only then does "a group without a
distinguished element" follow -- a nonempty torsor really is in bijection
with `G`. We leave the axioms as they are for readability, but the
nonemptiness requirement is part of the real definition.
@@@ -/

/- @@@
## A Tool We Will Need: `congrArg`

Before any instances, one small piece of equipment, because it does most of
the work in this file.

`congrArg` is the principle that **a function applied to equal arguments
gives equal results**. Its type says exactly that:

  `congrArg : (f : α → β) → a₁ = a₂ → f a₁ = f a₂`

So if you have a proof `h : a₁ = a₂` and any function `f`, then
`congrArg f h` is a proof that `f a₁ = f a₂`. That is all it does. It is the
workhorse for turning an equation you already have into the equation you
want, by applying the same thing to both sides.

Two uses recur below. Applying a function to both sides of a hypothesis:

  `congrArg (fun x => Monoid.op x c) h   -- from `a = b` get `a ∘ c = b ∘ c``

and lifting an equation from a representation up to a wrapper type, which is
what the plane instance does repeatedly.
@@@ -/

/- @@@
## Two Facts About Any Group

Now something the previous lesson did not do: prove a theorem about *all*
groups at once. Both facts below are about an arbitrary `[Group α]`. Neither
mentions ℚ, or `Fin 12`, or pairs. We prove each once here and then use them
at two different instances further down -- which is the whole argument for
bothering with an abstraction, made concrete rather than asserted.

The first says: **in a group, the only element that fixes anything is the
identity.** If combining `g` with `t` gives back `t`, then `g` was the
identity all along. This is exactly the `actFree` axiom for a group acting on
itself, so proving it here means two of our three instances get freeness for
free.

The proof is cancellation. Compose both sides with the inverse of `t` on the
right, then regroup: the `t` and its inverse annihilate, leaving `g` on one
side and the identity on the other.

Recall that `op`, `id`, `assoc`, `idLeft` and `idRight` are fields of
`Monoid`, which `Group` extends, so they are reached as `Monoid.op` and so
on. Only `inv`, `invLeft` and `invRight` belong to `Group` itself. Mixing the
two prefixes in one proof looks odd until you remember the `extends`.
@@@ -/

theorem eq_id_of_op_eq_self {α : Type} [Group α] {g t : α}
    (h : Monoid.op g t = t) : g = Monoid.id :=
  calc g
      -- Pad `g` out with the identity, so there is something to work on.
      = Monoid.op g Monoid.id                    := (Monoid.idRight g).symm
      -- The identity is `t` composed with its inverse.
    _ = Monoid.op g (Monoid.op t (Group.inv t))  :=
          congrArg (Monoid.op g) (Group.invRight t).symm
      -- Regroup, so that `g` and `t` sit together.
    _ = Monoid.op (Monoid.op g t) (Group.inv t)  :=
          (Monoid.assoc g t (Group.inv t)).symm
      -- That is exactly the hypothesis, applied under a function.
    _ = Monoid.op t (Group.inv t)                :=
          congrArg (fun x => Monoid.op x (Group.inv t)) h
      -- And `t` cancels against its own inverse.
    _ = Monoid.id                                := Group.invRight t

/- @@@
The second fact is the computation we will need for transitivity: composing
`a` with the inverse of `b`, then with `b`, gets you back to `a`. The `b`
cancels. Read it as "go to `a` the long way round, via `b`."
@@@ -/

theorem op_inv_op_cancel {α : Type} [Group α] (a b : α) :
    Monoid.op (Monoid.op a (Group.inv b)) b = a :=
  calc Monoid.op (Monoid.op a (Group.inv b)) b
      = Monoid.op a (Monoid.op (Group.inv b) b) := Monoid.assoc a (Group.inv b) b
    _ = Monoid.op a Monoid.id                   := congrArg (Monoid.op a) (Group.invLeft b)
    _ = a                                       := Monoid.idRight a

/- @@@
## Instance 1: Clock Hours (Integers Modulo 12)

The motivating example from the start of this lesson. The positions are
`Fin 12`, the shifts are also `Fin 12`, and the action is addition mod 12.
Adding an hour offset to a current hour gives the new hour, wrapping at 12.

First the group of shifts. Note that `op` is *defined to be* `Fin 12`'s own
`+`, and `inv` its own negation, so the group's abstract operation and the
arithmetic you can type at the keyboard are the same function here.

Every law is proved by `of_decide_eq_true rfl`, which deserves unpacking
since it recurs below and is the first genuinely new idiom in this file.
`Fin 12` is finite, so each law is a *decidable* proposition: there is a
procedure that checks it. `decide p` runs that procedure and returns a
`Bool`. The library theorem

  `of_decide_eq_true : decide p = true → p`

turns a successful run into a proof of `p`. And `rfl` proves
`decide p = true` whenever Lean can evaluate `decide p` and get `true` --
which it can, by checking every case. So the three words
`of_decide_eq_true rfl` mean "I checked all of them, and they all held."
@@@ -/

instance : Group (Fin 12) where
  op      : Fin 12 → Fin 12 → Fin 12 := (· + ·)
  id      : Fin 12 := 0
  assoc   : ∀ a b c : Fin 12, (a + b) + c = a + (b + c) := of_decide_eq_true rfl
  idLeft  : ∀ a : Fin 12, 0 + a = a := of_decide_eq_true rfl
  idRight : ∀ a : Fin 12, a + 0 = a := of_decide_eq_true rfl
  inv     : Fin 12 → Fin 12 := fun a => -a
  invLeft : ∀ a : Fin 12, (-a) + a = 0 := of_decide_eq_true rfl
  invRight: ∀ a : Fin 12, a + (-a) = 0 := of_decide_eq_true rfl

/- @@@
Nothing in those five proofs mentions how `Fin` arithmetic works -- no
unfolding to `Nat` and a `% 12`, no lemma names to look up. Exhaustive
checking does not need to know *why* a law holds, only that it holds in
every case. That is the bargain finiteness offers, and the rest of this file
shows what you do when it is not on the table.

Negation deserves a second look, because `Fin 12` contains no negative
numbers and yet `-a` is perfectly well defined. The inverse of a shift is
the shift that undoes it, which for a cyclic group means going the rest of
the way around.
@@@ -/

/- @@@
> **Checkpoint — inverses on a finite group.** `Fin 12` has no negative
> values, so `-(3 : Fin 12)` must be one of `0 … 11`. **Predict which one**
> from `invRight` (`a + (-a) = 0`) before evaluating, and predict the second
> line from the same law.
@@@ -/

#eval (-(3 : Fin 12))                    -- predict from invRight
#eval ((3 : Fin 12) + (-(3 : Fin 12)))   -- predict from invRight

/- @@@
And now the torsor, by the same method -- unavailable for ℚ -- of exhaustive
case analysis. `of_decide_eq_true rfl` checks every one of the 12, 144, or
1728 cases and reports back. This is worth seeing once: for finite
structures, "is this a theorem?" can be a decidable question, and Lean will
simply answer it.
@@@ -/

instance : Torsor (Fin 12) (Fin 12) where
  groupG        := inferInstance
  act           := (· + ·)
  actId         := of_decide_eq_true rfl
  actComp       := of_decide_eq_true rfl
  actFree       := of_decide_eq_true rfl
  actTransitive := of_decide_eq_true rfl

#eval (3 : Fin 12) + (5 : Fin 12)   -- 8
#eval (10 : Fin 12) + (5 : Fin 12)  -- 3 (wraps around)
#eval (0 : Fin 12) + (7 : Fin 12)   -- 7

/- @@@
Freeness is the interesting axiom here. It says that the only shift leaving
any hour unchanged is the zero shift -- a 5-hour shift moves *every* position.
Transitivity says you can get from any hour to any other by some shift. Taken
together: the twelve positions are interchangeable, and all the structure
lives in the shifts.

Note that `eq_id_of_op_eq_self` would also have discharged `actFree` here,
since the action *is* the group operation. We checked exhaustively instead,
to show the decidable route while we have a finite type to show it on.
@@@ -/

/- @@@
## Instance 2: ℚ (Rational Numbers)

The rational numbers form a torsor under themselves via addition.
Every rational can be shifted to every other rational by adding an
appropriate rational offset, and only 0 leaves any rational unchanged.

This uses the `Group ℚ` instance from the groups lesson. Note that here we
cannot appeal to `decide`: ℚ is infinite, so the proofs must be genuine
arguments rather than exhaustive checks.

And here the abstraction starts paying. `actFree` is not an argument about
rationals at all -- it is `eq_id_of_op_eq_self`, already proved above for
every group. The whole field is the name of that theorem.
@@@ -/

instance : Torsor Rat Rat where
  groupG    := inferInstance
  act       := (· + ·)
  actId     := Rat.zero_add
  actComp   := fun g h t => Rat.add_assoc g h t
  actFree   := fun _ _ h => eq_id_of_op_eq_self h
  actTransitive := fun t₁ t₂ => ⟨t₂ - t₁, Rat.sub_add_cancel⟩

/- @@@
## Instance 3: The Rational Plane, With Points and Vectors as Distinct Types

The two instances above both use *the same type* for the group and for the
set it acts on: `Torsor (Fin 12) (Fin 12)` and `Torsor Rat Rat`. That is
convenient, and it is also exactly the thing a torsor is supposed to rule
out. If positions and shifts are the same type, then `t₁ + t₂` typechecks --
and "the sum of 3 o'clock and 5 o'clock" is not a thing. Nothing in the
*axioms* is wrong; the *types* are simply too permissive to stop us writing
nonsense.

So for the plane we do it properly. We give the positions and the shifts
distinct types, `Point2` and `Vector2`, even though both are *implemented*
as a pair of rationals.
@@@ -/

structure Vector2 where
  ofPair ::
  toPair : Rat × Rat
deriving DecidableEq

structure Point2 where
  ofPair ::
  toPair : Rat × Rat
deriving DecidableEq

/- @@@
### Reading Those Two Declarations

Three pieces of syntax, two of them new.

`ofPair ::` names the constructor. Without it the constructor would be
`Vector2.mk`; with it we get `Vector2.ofPair`, which reads better at use
sites and, more importantly, reads better in the proofs below where the
constructor appears as a *function* being handed to `congrArg`.

`toPair : Rat × Rat` is the single field, so `v.toPair` is the pair inside
`v`. A one-field structure is the standard way to say "same representation,
different type": `Vector2` and `Point2` have identical representations and
are nonetheless unrelated types, which is precisely what we want.

`⟨…⟩` is the *anonymous constructor*, available for any structure. Writing
`⟨(3, 4)⟩` means "build the expected structure from these fields", with the
expected type deciding which constructor is meant. So `Vector2.ofPair (3, 4)`
and `(⟨(3, 4)⟩ : Vector2)` are the same value, and you will see both below:
the explicit form where the type is not otherwise determined, the anonymous
form inside instance fields where it is.

One consequence of a one-field structure is worth stating because the proofs
below rely on it silently. For any `v : Vector2`, the value
`Vector2.ofPair v.toPair` *is* `v` -- not merely equal to it, but the same
term as far as Lean is concerned. (This is called eta for structures: taking
a structure apart and putting it back together changes nothing.) That is why
a proof of `Vector2.ofPair x = Vector2.ofPair v.toPair` counts as a proof of
`Vector2.ofPair x = v`, which happens in every law we prove below.
@@@ -/

/- @@@
Next, printing. Lean does not know how to display our new types, so `#eval`
would refuse. A `Repr` instance says how. Its one method, `reprPrec`, takes
the value and a *precedence* -- used by Lean to decide whether to parenthesize
in a larger expression -- and returns formatted output. We ignore the
precedence (that is the `_`) and print the underlying pair tagged with the
type it came from, so the `#eval`s below say what they mean.
@@@ -/

instance : Repr Vector2 where reprPrec v _ := "Vector2 " ++ repr v.toPair
instance : Repr Point2  where reprPrec p _ := "Point2 "  ++ repr p.toPair

/- @@@
### The Group of Displacements

`Vector2` needs to be a group, since that is what acts. Rather than redo the
componentwise arithmetic, we *transport* the `Group (ℚ × ℚ)` instance from the
previous lesson across the wrapper: each operation unwraps its arguments,
defers to the pair instance, and wraps the result.

Every law then follows from the corresponding law on pairs by `congrArg`, with
`f` the constructor `Vector2.ofPair`. Read `idLeft` as the pattern: the pair
instance supplies `Monoid.idLeft a.toPair`, an equation between *pairs*;
applying the constructor to both sides lifts it to an equation between
`Vector2`s; and structure eta makes the right-hand side `a` itself. No
arithmetic is redone and no law is reproved.
@@@ -/

instance : Group Vector2 where
  op v w      := ⟨Monoid.op v.toPair w.toPair⟩
  id          := ⟨Monoid.id⟩
  inv v       := ⟨Group.inv v.toPair⟩
  assoc a b c := congrArg Vector2.ofPair (Monoid.assoc a.toPair b.toPair c.toPair)
  idLeft a    := congrArg Vector2.ofPair (Monoid.idLeft a.toPair)
  idRight a   := congrArg Vector2.ofPair (Monoid.idRight a.toPair)
  invLeft a   := congrArg Vector2.ofPair (Group.invLeft a.toPair)
  invRight a  := congrArg Vector2.ofPair (Group.invRight a.toPair)

/- @@@
### The Torsor of Points

Now the action: a displacement applied to a point yields a point. Note the
type of `act` for this instance -- `Vector2 → Point2 → Point2`. The two
argument types are different, so the operands cannot be swapped and two
points cannot be combined. That is the improvement over the instances above.

All four laws are now one line each, and two of them are the general group
theorems from the top of the file:

  - `actId` and `actComp` lift the pair laws with `congrArg`, as in the group
    instance just above.
  - `actFree` unwraps the hypothesis with `congrArg Point2.toPair` (the
    *field*, used as a function, going the other direction from the
    constructor), hands it to `eq_id_of_op_eq_self`, and wraps the conclusion
    back up. Notice that nothing in this step knows the entries are rationals.
  - `actTransitive` must *exhibit* a displacement, and `op_inv_op_cancel`
    says that `q` composed with the inverse of `p` is the one that works.
@@@ -/

instance : Torsor Vector2 Point2 where
  groupG        := inferInstance
  act v p       := ⟨Monoid.op v.toPair p.toPair⟩
  actId p       := congrArg Point2.ofPair (Monoid.idLeft p.toPair)
  actComp v w p := congrArg Point2.ofPair (Monoid.assoc v.toPair w.toPair p.toPair)
  actFree _v _p h :=
    congrArg Vector2.ofPair (eq_id_of_op_eq_self (congrArg Point2.toPair h))
  actTransitive p q :=
    ⟨⟨Monoid.op q.toPair (Group.inv p.toPair)⟩,
     congrArg Point2.ofPair (op_inv_op_cancel _ _)⟩

/- @@@
The outer `⟨_, _⟩` in `actTransitive` builds the `∃`: its first component is
the displacement, its second the proof that this displacement works. The
inner `⟨_⟩` builds the `Vector2`. Nested anonymous constructors are compact
and take some getting used to; written out, the first component is
`Vector2.ofPair (Monoid.op q.toPair (Group.inv p.toPair))`.
@@@ -/

/- @@@
The operations compute. Below, a displacement moves a point, and two
displacements compose -- with the types in the output showing which role each
value plays.
@@@ -/

/- @@@
> **Checkpoint — the action and the group operation are different
> operations.** One of the two lines below combines a displacement with a
> point and the other combines two displacements. **Predict both results and
> both type tags** before evaluating, then say which law each line is an
> instance of.
@@@ -/

#eval Torsor.act (Vector2.ofPair (3, 4)) (Point2.ofPair (1, 1))
      -- Point2 (4, 5)

#eval Monoid.op (Vector2.ofPair (3, 0)) (Vector2.ofPair (-2, 3))
      -- Vector2 (1, 3): displacements compose, because they form a group

/- @@@
And the type distinction really is enforced. Rather than claim that in a
comment, we can ask Lean. `#check_failure` succeeds exactly when the term it
is given **fails** to typecheck, so the three commands below are live,
machine-checked evidence that these expressions are rejected. Each reports
the instance Lean looked for and could not find.
@@@ -/

/- Points do not add: there is no `Monoid Point2`. -/
#check_failure Monoid.op (Point2.ofPair (1, 1)) (Point2.ofPair (2, 2))

/- A point is not a displacement: there is no `Torsor Point2 Point2`. -/
#check_failure Torsor.act (Point2.ofPair (1, 1)) (Point2.ofPair (2, 2))

/- The operands cannot be swapped: there is no `Torsor Vector2 Vector2`. -/
#check_failure Torsor.act (Vector2.ofPair (3, 4)) (Vector2.ofPair (1, 1))

/- @@@
Each failure is reported as an inability to synthesize an instance -- which
is the type checker saying, correctly, that there is no such operation. This
is what we bought with two wrapper types: the geometry that is meaningless is
now unwritable rather than merely unintended.
@@@ -/

/- @@@
## Reasoning Once, For Every Torsor

The two group theorems at the top of this file were about any `[Group α]`.
Here is one about any `[Torsor G T]`, which is the real test of whether the
class earns its keep.

**Acting by a fixed group element is injective**: if `g` moves `t₁` and `t₂`
to the same place, then `t₁` and `t₂` were the same point. Intuitively,
shifting the whole clock by five hours cannot make two different hours
coincide, because you can always shift back.

That intuition is the proof. Act by the inverse of `g` on both sides --
`congrArg` again -- then use `actComp` backwards to regroup each side into a
single action, and `inv g` composed with `g` is the identity, which `actId`
says moves nothing.

Note what the proof does *not* mention: no `Fin`, no ℚ, no pairs, no
`decide`, and not even `actFree` or `actTransitive`. It needs only two of the
four axioms, so it holds for all three instances below and for any torsor
anyone writes later.
@@@ -/

theorem act_left_cancel {G T : Type} [tor : Torsor G T] (g : G) {t₁ t₂ : T}
    (h : tor.act g t₁ = tor.act g t₂) : t₁ = t₂ :=
  calc t₁
      -- Pad with the identity action, which moves nothing.
      = tor.act tor.groupG.id t₁                          := (tor.actId t₁).symm
      -- The identity is `inv g` composed with `g`.
    _ = tor.act (tor.groupG.op (tor.groupG.inv g) g) t₁   :=
          congrArg (fun x => tor.act x t₁) (tor.groupG.invLeft g).symm
      -- Split the composite action into two actions.
    _ = tor.act (tor.groupG.inv g) (tor.act g t₁)         := tor.actComp _ _ _
      -- Here is the hypothesis, under `act (inv g)`.
    _ = tor.act (tor.groupG.inv g) (tor.act g t₂)         :=
          congrArg (tor.act (tor.groupG.inv g)) h
      -- Now run the same three steps backwards on `t₂`.
    _ = tor.act (tor.groupG.op (tor.groupG.inv g) g) t₂   := (tor.actComp _ _ _).symm
    _ = tor.act tor.groupG.id t₂                          :=
          congrArg (fun x => tor.act x t₂) (tor.groupG.invLeft g)
    _ = t₂                                                := tor.actId t₂

/- @@@
And now the payoff, which is the point of the whole lesson. Below, the same
theorem is applied at two instances with completely different carriers. Note
what is absent from both: any proof at all, only the theorem's name.
@@@ -/

example (g t₁ t₂ : Fin 12) (h : Torsor.act g t₁ = Torsor.act g t₂) : t₁ = t₂ :=
  act_left_cancel g h

example (v : Vector2) (p q : Point2) (h : Torsor.act v p = Torsor.act v q) : p = q :=
  act_left_cancel v h

/- @@@
## What the Torsor Abstraction Buys

All four axioms are machine-checked for all three instances -- no `sorry`
anywhere -- so each instance is also computable and its operations run.

The laws ensure that:
  - Applying the identity doesn't move anything
  - Actions compose consistently
  - Every point can reach every other point
  - No non-identity element fixes any point

One abstraction, and clocks, rationals, and the plane all satisfy it. The
payoff is not a slogan here but three named theorems:
`eq_id_of_op_eq_self` and `op_inv_op_cancel`, each proved once for every
group and then used to discharge axioms at two instances, and
`act_left_cancel`, proved once for every torsor and applied at two carriers
with nothing in common. Reasoning done once about `Torsor G T` really does
apply to every instance, whether the underlying set is finite or infinite,
and whether or not the group and the set it acts on are the same type.

## Where This Goes Next

Separating `Point2` from `Vector2` fixed one of the two problems with the
plane example. The other one remains, and it is in the class itself.
Transitivity is stated as an *existence claim*:

  `actTransitive : ∀ t₁ t₂ : T, ∃ g : G, act g t₁ = t₂`

Read that carefully: it says a displacement relating any two points *exists*.
It does not give you one. The witness is buried inside a proof, so there is
no operation to call, nothing to `#eval`, and no way to write "the vector from
`p` to `q`" as an expression. Our instance happens to construct the witness
explicitly, with `op_inv_op_cancel`, but the class cannot oblige an instance
to, and cannot hand the witness back to a caller.

The next lesson replaces that existential with an operation, `vsub : P → P → V`,
which *computes* the displacement between two points. A proof that something
exists becomes a function that produces it. That structure -- distinct types
for points and vectors, plus `vsub` -- is an *affine space*, and it is a
torsor with better ergonomics.
@@@ -/

/- @@@
## Exercises

Each exercise carries a banner -- `[id] · competency · tier · level · target`
-- and, where it asks you to build something, an **acceptance check**: paste
it beneath your definition in your own file and it must succeed. `#guard` is
silent on success and errors on failure, so the compiler is your grader. See
`EXERCISE_CONVENTIONS.md` for the schema. Do every **core** exercise;
**stretch** exercises go deeper and are optional.

---

**[E13.1]** · *decidability identification* · tier 1 · **core**

Instance 1 closed all four axioms by exhaustive checking; Instance 2 could
not. For each proposition below, say **whether `decide` can close it and
why** --
is the domain finite, is the predicate decidable? -- *before* checking. The
judgment is the point, not the tool-use.

(a) `∀ g t : Fin 7, g + t = t → g = 0`
(b) `∀ t₁ t₂ : Fin 7, ∃ g : Fin 7, g + t₁ = t₂`
(c) `∀ g t : Rat, g + t = t → g = 0`

```lean
#guard ∀ g t : Fin 7, g + t = t → g = 0
#guard ∀ t₁ t₂ : Fin 7, ∃ g : Fin 7, g + t₁ = t₂
-- (c) has no check on purpose: say why `decide` cannot close it, and name
--     the theorem in this file that settles it instead.
```

In one line each: what is `(a)` the freeness axiom *for*, and what is `(b)`?

---

**[E13.2]** · *type-directed derivation* · tier 1 · **core** · target `Torsor (Fin 7) (Fin 7)`

Days of the week are a torsor for the group of day-shifts. Build
`instance : Group (Fin 7)` and `instance : Torsor (Fin 7) (Fin 7)`, following
the `Fin 12` pattern in Instance 1. *First-step hint:* the group fields are
`(· + ·)`, `0` and negation, and all four torsor axioms are
`of_decide_eq_true rfl` because the type is finite. Effort: ~12 lines, no
hand-written proof.

```lean
#guard (3 : Fin 7) + 5 = 1
#guard ∀ g t : Fin 7, g + t = t → g = 0
```

Then say in one line what changes in your file if you replace `Fin 7` with
`Nat`, and which axiom breaks first.

---

**[E13.3]** · *counterexample finding* · tier 1 · **core** · target `natNotTransitive`

A student claims `Nat` is a torsor for itself under addition, with
`act := (· + ·)`. Transitivity fails. Find concrete `t₁ t₂ : Nat` for which
**no** `g : Nat` satisfies `g + t₁ = t₂`, and encode the witness so the check
**succeeds** -- that is, phrase it as the inequality that must hold. A bounded
`∀` over a literal list is decidable, which is what makes this checkable.

```lean
#guard ∀ g ∈ (List.range 20), g + 5 ≠ 3
```

Then answer in one line: is the failure in `actTransitive`, or does it
actually start earlier, at `Group Nat`?

---

**[E13.4]** · *specification reading* · tier 1 (+ tier-3 reading) · **core** · target `UniqueDisplacementSpec`

`act_left_cancel` cancels the *point*: from `act g t₁ = act g t₂` it concludes
`t₁ = t₂`. Its companion cancels the *group element*: from
`act g₁ t = act g₂ t` it should conclude `g₁ = g₂` -- "the displacement
between two points is unique."

Do **not** prove the general statement; read the provided proof of
`act_left_cancel` above (tier 3) and say in two lines which axioms the
companion would need instead. Then state the companion as a `Prop` and
confirm it on a decidable instance:

```lean
-- def UniqueDisplacementSpec : Prop :=
--   ∀ g₁ g₂ t : Fin 7, g₁ + t = g₂ + t → g₁ = g₂
#guard ∀ g₁ g₂ t : Fin 7, g₁ + t = g₂ + t → g₁ = g₂
```

Which tier does the general statement live in, and which does the check?

---

**[E13.5]** · *type reading (free theorems)* · tier 2 · **stretch**

Read these two types and nothing else -- no proofs, no instances:

  `actTransitive : ∀ t₁ t₂ : T, ∃ g : G, act g t₁ = t₂`
  `vsub : P → P → V`

In three or four lines: what can a caller *do* with the second that it cannot
do with the first? Your answer should explain why the file contains no
`#eval` of a displacement computed from two points, even though Instance 3's
`actTransitive` plainly constructs one.

---

**[E13.6]** · *specification writing* · tier 1 · **stretch** · target `ZeroShiftSpec`

State, as a `Prop`, the specification *"translating a point by the zero
displacement leaves it where it is"* for `Vector2` acting on `Point2`, then
confirm it on instances. The zero displacement is `Monoid.id`, and the axiom
that guarantees your spec is `actId`.

```lean
-- def ZeroShiftSpec : Prop :=
--   ∀ p : Point2, Torsor.act (Monoid.id : Vector2) p = p
#guard Torsor.act (Monoid.id : Vector2) (Point2.ofPair (3, 4))
         = Point2.ofPair (3, 4)
```

Why can this one be `#guard`ed at all, when the ℚ facts in E13.1(c) could
not? (Hint: look at what `deriving DecidableEq` bought us.)

---

### Coverage audit

| Competency | Exercises |
|---|---|
| specification writing | E13.6 |
| specification reading | E13.4 |
| type-directed derivation | E13.2 |
| counterexample finding | E13.3 |
| decidability identification | E13.1 |
| type reading (free theorems) | E13.5 |

Six of six competencies, two tiers, one counterexample item, four core and
two stretch. The tier-3 content (E13.4) is *reading* a provided proof, never
authoring one.
@@@ -/

end Torsors
