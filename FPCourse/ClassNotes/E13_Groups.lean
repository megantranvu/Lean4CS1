/- @@@
# Groups: Monoids With Inverses

## What Groups Are: Symmetry-Preserving Actions

Think of a group as the mathematical language of *symmetry-preserving
actions*. When you rotate a square 90 degrees, you get back a square
that looks the same -- the action preserves the square's essential
structure, leaving it invariant. When you reflect a square across a
vertical line, again, the square's shape is unchanged. These operations
are *reversible*: if you rotate 90 degrees clockwise, you can rotate
90 degrees counter-clockwise to undo it. If you reflect vertically,
reflecting again gives you back the original.

Groups capture this idea: they're sets of actions that preserve a
structure and can all be undone. Every action in a group is reversible,
which is why groups are the right abstraction for studying the symmetries
of any object -- geometric shapes, algebraic systems, physical laws.

Last class we saw that a `Monoid` bundles an associative operator
with an identity element. That's already powerful -- it lets you
fold a container down to one value, and it guarantees that folding
is well-defined no matter how you parenthesize the operation. But
a monoid is still one-directional: once you've combined elements,
you can't pull them apart again.

A *group* adds one more piece: for *every* element, there's an
*inverse* that undoes what that element does. Add 5, then add
-5, and you're back where you started. Multiply by 2, then
multiply by 1/2, and you're back where you started. This inverse
property unlocks a whole new level of algebraic power.

Rather than asking "what is a group," we'll ask: what new
super-power does the inverse give you? The answer is *solving
equations*. In a monoid, if you know `a * x = b`, you can't
reliably solve for `x` -- you don't have a way to "divide out"
the `a`. In a group, you can: multiply both sides by the inverse
of `a`, written `inv a`, and the `a`'s cancel, leaving
`x = inv(a) * b`. That's the payoff.

## A Glimpse at Classification: The Finite Simple Groups

In October 2026, mathematicians led by Harmonic announced the formal
verification (in the Lean proof assistant, coincidentally!) of the
complete classification of all *finite simple groups* -- one of the
greatest achievements of 20th-century mathematics. This is worth
understanding at a high level.

A *finite* group is one with finitely many elements. For example,
integers modulo N form a finite group (it has exactly N elements).
The symmetries of a square form a finite group (rotations and
reflections, eight operations total).

A *simple* group is one with no "internal structure" -- it can't be
decomposed into smaller groups the way a more complicated group can.
Think of simple groups as the *atoms* of group theory: they're the
indivisible building blocks.

For contrast, the integers modulo 6 form a *non-simple* group. Why?
Because we can extract a smaller group from it: the integers modulo 2.
Every element of mod-2 lives inside mod-6, and the operations preserve
that structure. We call this relationship a "subgroup." A group that
has no such non-trivial subgroups is simple -- it can't be broken down.

The classification theorem says: there are *infinitely many* finite
simple groups, but they fall into exactly four families:

  1. *Cyclic groups of prime order*: integers modulo a prime, under addition.
  2. *Alternating groups*: even permutations of N elements.
  3. *Groups of Lie type*: built from symmetries of geometric structures.
  4. *The 26 sporadic groups*: exceptional cases that don't fit the patterns.

Why does classification matter? Because every finite group can be
built out of simple groups, the way every integer can be built from
primes. Understanding the atoms lets you understand the whole.

The formal verification in Lean is remarkable because it ensures that
the proof itself is mechanically sound -- no human error in 10,000+
pages of argument. This is the future of mathematics: proofs that are
not just believed, but *verified by machine*.
@@@ -/

namespace Groups

/- @@@
## Recap: `Monoid`

Same as before: associative operation, identity element, two laws.
@@@ -/

class Monoid (α : Type) where
  op      : α → α → α
  id      : α
  assoc   : ∀ a b c, op (op a b) c = op a (op b c)
  idLeft  : ∀ a, op id a = a
  idRight : ∀ a, op a id = a

/- @@@
## `Group`: A `Monoid` With Inverses

A group is a monoid with one additional requirement: for every
element `a`, there must exist an inverse `inv a` such that
combining `a` with its inverse (in either order) gives you back
the identity. The two laws are `invLeft` (inverse times element
equals identity) and `invRight` (element times inverse equals
identity).

Both laws are needed because the operator might not be commutative:
`a * inv(a)` might differ from `inv(a) * a`. In practice, for the
algebraic structures we care about, they're the same, but the
definition doesn't assume that.
@@@ -/

class Group (α : Type) extends Monoid α where
  inv     : α → α
  invLeft : ∀ a, op (inv a) a = id
  invRight: ∀ a, op a (inv a) = id

/- @@@
## Example 1: Integers Under Addition

The integers form a group under addition. The operation is `+`,
the identity is `0`, and the inverse of any integer `n` is `-n`.
Let's build this group step by step.

First, the monoid part: addition is associative, `0` is the
identity on both sides. We can use Lean's built-in proofs for
these properties.
@@@ -/

instance : Group Int where
  op      := (· + ·)
  id      := 0
  assoc   := Int.add_assoc
  idLeft  := Int.zero_add
  idRight := Int.add_zero
  inv     := fun n => -n
  invLeft := fun n => Int.add_left_neg n
  invRight:= fun n => Int.add_right_neg n

#eval (5 : Int) + 3              -- 8
#eval (-5 : Int)                 -- -5
#eval (5 : Int) + (-5)           -- 0

/- @@@
The last example shows what the inverse law means in practice:
adding a number and its inverse gives you back the identity.
@@@ -/

/- @@@
## Example 2: Integers Modulo N

Now for something trickier. Fix some positive integer `N > 1`,
and consider the integers *modulo* `N`: the numbers `{0, 1, ..., N-1}`,
where we treat `N` as equivalent to `0`, `N+1` as equivalent to `1`,
and so on.

Addition modulo N is associative, and `0` is still the identity. But
is every element invertible? Let's think about it. For the additive
inverse of some `a` to exist, we need a value `b` such that
`a + b ≡ 0 (mod N)`. That means `b ≡ -a (mod N)`, and we can
always find such a `b` in the range `{0, 1, ..., N-1}`. (If `a = 3`
and `N = 5`, then `b = 2`, because `3 + 2 = 5 ≡ 0 (mod 5)`.) So yes,
every element has an inverse.

This is an important example because it shows that a group doesn't have
to be about "real" numbers or familiar structures -- it's an abstract
property that can hold for any type, as long as the operation and
inverse satisfy the laws.

For this example, we'll use `Fin N`, which is Lean's type for "integers
from 0 to N-1" with addition wrapping around at N.
@@@ -/

instance : Group (Fin 5) where
  op      := (· + ·)
  id      := 0
  assoc   := by intros; ext; simp [Fin.add_def, Nat.add_assoc]
  idLeft  := by intros; ext; simp [Fin.add_def]
  idRight := by intros; ext; simp [Fin.add_def]
  inv     := fun a => -a
  invLeft := by intros; ext; simp [Fin.add_def, Fin.neg_def]
  invRight:= by intros; ext; simp [Fin.add_def, Fin.neg_def]

#eval (3 : Fin 5) + 2           -- 0 (because (3 + 2) mod 5 = 5 mod 5 = 0)
#eval (4 : Fin 5) + 1           -- 0 (because (4 + 1) mod 5 = 5 mod 5 = 0)

/- @@@
Both examples above show the additive inverse law in action: adding
an element to its inverse modulo 5 gives you 0. The structure itself
handles the wrapping; the group laws ensure it's consistent.
@@@ -/

/- @@@
## The Power of Groups: Solving Equations

Here's where groups become powerful. Given an equation `a * x = b`
in a group, we can solve for `x` by multiplying both sides by the
inverse of `a`:

  `a * x = b`
  `inv(a) * (a * x) = inv(a) * b`    (multiply both sides by `inv(a)`)
  `(inv(a) * a) * x = inv(a) * b`    (use associativity)
  `id * x = inv(a) * b`              (use `invLeft`)
  `x = inv(a) * b`                   (use identity)

Let's write a function that solves `a * x = b` in any group:
@@@ -/

def solve {α : Type} [g : Group α] (a b : α) : α :=
  g.op (g.inv a) b

/- @@@
This function computes `inv(a) * b`, which is the solution to
`a * x = b`. We can verify that it works conceptually by checking
the equation: if `x = inv(a) * b`, then `a * x = a * (inv(a) * b)`.
By associativity, that's `(a * inv(a)) * b = id * b = b`. ✓

For integers:
  `5 + x = 13`
  `x = -5 + 13 = 8`

For integers modulo 5:
  `3 + x ≡ 0 (mod 5)`
  `x ≡ -3 ≡ 2 (mod 5)`

The group structure guarantees this works for *any* group, not just
these specific examples. That's the abstraction paying off: we write
one `solve` function, and it works everywhere the group laws hold.
@@@ -/

end Groups
