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

Four fields of data and law. The group `G` is an instance-implicit parameter,
so a torsor always carries the group structure it acts by.
@@@ -/

class Torsor (G T : Type) where
  [groupG : Group G]
  act        : G → T → T
  actId      : ∀ t : T, act groupG.id t = t
  actComp    : ∀ g h : G, ∀ t : T, act (groupG.op g h) t = act g (act h t)
  actFree    : ∀ g : G, ∀ t : T, act g t = t → g = groupG.id
  actTransitive : ∀ t₁ t₂ : T, ∃ g : G, act g t₁ = t₂

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
## Instance 1: Clock Hours (Integers Modulo 12)

The motivating example from the start of this lesson. The positions are
`Fin 12`, the shifts are also `Fin 12`, and the action is addition mod 12.
Adding an hour offset to a current hour gives the new hour, wrapping at 12.

First the group of shifts:
@@@ -/

instance : Group (Fin 12) where
  op      : Fin 12 → Fin 12 → Fin 12 := (· + ·)
  id      : Fin 12 := 0
  assoc   : ∀ a b c : Fin 12, (a + b) + c = a + (b + c) :=
    fun a b c => by ext; simp [Fin.add_def, Nat.add_assoc]
  idLeft  : ∀ a : Fin 12, 0 + a = a := fun a => by ext; simp [Fin.add_def]
  idRight : ∀ a : Fin 12, a + 0 = a := fun a => by ext; simp [Fin.add_def]
  inv     : Fin 12 → Fin 12 := fun a => -a
  invLeft : ∀ a : Fin 12, (-a) + a = 0 :=
    fun a => by ext; simp [Fin.add_def, Fin.neg_def]
  invRight: ∀ a : Fin 12, a + (-a) = 0 :=
    fun a => by ext; simp [Fin.add_def, Fin.neg_def]

/- @@@
And now the torsor. Because `Fin 12` is *finite*, we get to prove all four
axioms by a method unavailable for ℚ: exhaustive case analysis. `decide`
checks every one of the 12, 144, or 1728 cases and reports back. This is
worth seeing once -- for finite structures, "is this a theorem?" can be a
decidable question, and Lean will simply answer it.
@@@ -/

instance : Torsor (Fin 12) (Fin 12) where
  groupG        := inferInstance
  act           := (· + ·)
  actId         := by decide
  actComp       := by decide
  actFree       := by decide
  actTransitive := by decide

#eval (3 : Fin 12) + (5 : Fin 12)   -- 8
#eval (10 : Fin 12) + (5 : Fin 12)  -- 3 (wraps around)
#eval (0 : Fin 12) + (7 : Fin 12)   -- 7

/- @@@
Freeness is the interesting axiom here. It says that the only shift leaving
any hour unchanged is the zero shift -- a 5-hour shift moves *every* position.
Transitivity says you can get from any hour to any other by some shift. Taken
together: the twelve positions are interchangeable, and all the structure
lives in the shifts.
@@@ -/

/- @@@
## Instance 2: ℚ (Rational Numbers)

The rational numbers form a torsor under themselves via addition.
Every rational can be shifted to every other rational by adding an
appropriate rational offset, and only 0 leaves any rational unchanged.

This uses the `Group ℚ` instance from the groups lesson. Note that here we
cannot appeal to `decide`: ℚ is infinite, so the proofs must be genuine
arguments rather than exhaustive checks.
@@@ -/

instance : Torsor Rat Rat where
  groupG    := inferInstance
  act       := (· + ·)
  actId     := Rat.zero_add
  actComp   := fun g h t => Rat.add_assoc g h t
  actFree   := fun g t h => by
    -- If g + t = t, then g = 0 (the identity).
    -- Subtract t from both sides and cancel.
    have eq : g + t - t = t - t := by rw [h]
    simp [Rat.add_sub_cancel, Rat.sub_self] at eq
    exact eq
  actTransitive := fun t₁ t₂ => ⟨t₂ - t₁, by simp [Rat.sub_add_cancel]⟩

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
as a pair of rationals. A `structure` with one field is the standard way to
say "same representation, different type":
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
Printing the underlying pair, tagged with which type it came from, so that
the `#eval`s below say what they mean.
@@@ -/

instance : Repr Vector2 where reprPrec v _ := "Vector2 " ++ repr v.toPair
instance : Repr Point2  where reprPrec p _ := "Point2 "  ++ repr p.toPair

/- @@@
These are genuinely different types now, and the type checker enforces the
distinction. Points cannot be added to each other, and a point cannot be
used where a displacement is expected -- both are type errors rather than
silently meaningful expressions.

### The Group of Displacements

`Vector2` needs to be a group, since that is what acts. Rather than redo the
componentwise arithmetic, we *transport* the `Group (ℚ × ℚ)` instance from the
previous lesson across the wrapper: each operation unwraps, defers to the pair
instance, and wraps the result. Every law then follows from the corresponding
law on pairs by `congrArg`, which says "equal arguments give equal results"
and here lifts an equation on pairs to an equation on `Vector2`.

Recall that `op`, `id`, `assoc`, `idLeft` and `idRight` live in `Monoid`,
which `Group` extends; only `inv`, `invLeft` and `invRight` are `Group`'s own.
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

The `actId` and `actComp` proofs again just lift the pair laws. The two
interesting proofs are below them.
@@@ -/

instance : Torsor Vector2 Point2 where
  groupG        := inferInstance
  act v p       := ⟨Monoid.op v.toPair p.toPair⟩
  actId p       := congrArg Point2.ofPair (Monoid.idLeft p.toPair)
  actComp v w p := congrArg Point2.ofPair (Monoid.assoc v.toPair w.toPair p.toPair)
  -- Freeness: if a displacement fixes a point, it is the zero displacement.
  -- Unwrap to an equation on pairs, cancel `p` on the right, wrap back up.
  -- Note that the cancellation uses only the group axioms -- associativity
  -- and inverses -- and never the fact that the entries are rationals.
  actFree := fun v p h => by
    have hp : Monoid.op v.toPair p.toPair = p.toPair := congrArg Point2.toPair h
    have hv : v.toPair = (Monoid.id : Rat × Rat) :=
      calc v.toPair
          = Monoid.op v.toPair Monoid.id := (Monoid.idRight _).symm
        _ = Monoid.op v.toPair (Monoid.op p.toPair (Group.inv p.toPair)) := by
              rw [Group.invRight]
        _ = Monoid.op (Monoid.op v.toPair p.toPair) (Group.inv p.toPair) :=
              (Monoid.assoc _ _ _).symm
        _ = Monoid.op p.toPair (Group.inv p.toPair) := by rw [hp]
        _ = Monoid.id := Group.invRight _
    exact congrArg Vector2.ofPair hv
  -- Transitivity: the displacement from `p` to `q` is `q` composed with the
  -- inverse of `p`. Applying it to `p` cancels the `p` and lands on `q`.
  actTransitive := fun p q =>
    ⟨⟨Monoid.op q.toPair (Group.inv p.toPair)⟩, by
      show Point2.ofPair
        (Monoid.op (Monoid.op q.toPair (Group.inv p.toPair)) p.toPair) = q
      rw [Monoid.assoc, Group.invLeft, Monoid.idRight]⟩

/- @@@
The operations compute. Below, a displacement moves a point, and the
displacement between two points is recovered -- with the types in the output
showing which role each value plays.
@@@ -/

#eval Torsor.act (Vector2.ofPair (3, 4)) (Point2.ofPair (1, 1))
      -- Point2 (4, 5)

#eval Monoid.op (Vector2.ofPair (3, 0)) (Vector2.ofPair (-2, 3))
      -- Vector2 (1, 3): displacements compose, because they form a group

/- @@@
And the type distinction really is enforced. Each of these is a type error:

  `Monoid.op (Point2.ofPair (1, 1)) (Point2.ofPair (2, 2))`
      -- no `Monoid Point2` instance: points do not add

  `Torsor.act (Point2.ofPair (1, 1)) (Point2.ofPair (2, 2))`
      -- no `Torsor Point2 Point2` instance: a point is not a displacement

  `Torsor.act (Vector2.ofPair (3, 4)) (Vector2.ofPair (1, 1))`
      -- no `Torsor Vector2 Vector2` instance: the operands cannot be swapped

Lean reports each of these as a failure to synthesize the instance that
would be needed to make the expression mean anything -- which is the type
checker saying, correctly, that there is no such operation.

This is what we gained by paying for two wrapper types: the geometry that is
meaningless is now unwritable rather than merely unintended.
@@@ -/

/- @@@
## What the Torsor Abstraction Buys

All four axioms are machine-checked for all three instances -- no `sorry`
anywhere -- so each instance is also computable and its operations run.

The laws ensure that:
  - Applying the identity doesn't move anything
  - Actions compose consistently
  - Every point can reach every other point
  - No non-identity element fixes any point

One abstraction, and clocks, rationals, and the plane all satisfy it. That
is the payoff: reasoning done once about `Torsor G T` applies to every
instance, whether the underlying set is finite or infinite, and whether or
not the group and the set it acts on are the same type.

## Where This Goes Next

Separating `Point2` from `Vector2` fixed one of the two problems with the
plane example. The other one remains, and it is in the class itself.
Transitivity is stated as an *existence claim*:

  `actTransitive : ∀ t₁ t₂ : T, ∃ g : G, act g t₁ = t₂`

Read that carefully: it says a displacement relating any two points *exists*.
It does not give you one. The witness is buried inside a proof, so there is
no operation to call, nothing to `#eval`, and no way to write "the vector from
`p` to `q`" as an expression. Our instance happens to construct the witness
explicitly, but the class cannot oblige an instance to, and cannot hand the
witness back to a caller.

The next lesson replaces that existential with an operation, `vsub : P → P → V`,
which *computes* the displacement between two points. A proof that something
exists becomes a function that produces it. That structure -- distinct types
for points and vectors, plus `vsub` -- is an *affine space*, and it is a
torsor with better ergonomics.
@@@ -/

end Torsors
