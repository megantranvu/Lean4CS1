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
super-powers does the inverse give you? The answer is *solving
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
Because we can extract a smaller group sitting inside it. Be careful about
*which* smaller group, though: it is not the set `{0, 1}`. That set is not
closed under addition mod 6, since `1 + 1 = 2` escapes it, so it is not a
subgroup at all. The order-2 subgroup of mod-6 is `{0, 3}`:

  `0 + 0 = 0`,  `0 + 3 = 3`,  `3 + 3 = 6 ≡ 0 (mod 6)`

Nothing escapes, and every element has an inverse inside, so `{0, 3}` really
is a group in its own right. It is *isomorphic* to the integers mod 2 -- same
structure, relabelled -- but it is not literally a subset of mod-2's elements.
That distinction between "is isomorphic to" and "is a subset of" matters
constantly once you start formalizing, so it is worth getting right here.

Mod-6 has exactly four subgroups: `{0}`, `{0, 3}`, `{0, 2, 4}`, and all of
mod-6. The middle two are the interesting ones, isomorphic to mod-2 and
mod-3 respectively.

## Normal Subgroups and Composition Series

Now the correction to the naive definition. A group is simple when it has no
non-trivial **normal** subgroup -- not merely no non-trivial subgroup. A
subgroup `N ⊆ G` is *normal* when conjugating any of its elements by anything
in `G` lands you back in `N`: for all `g : G` and `n : N`, `g * n * inv g ∈ N`.
Normality is exactly the condition that lets you form a *quotient* group
`G / N`, which is what "breaking `G` down" actually means.

The word "normal" is not a technicality we can drop. The alternating groups
in family 2 below are simple, yet they have plenty of non-trivial subgroups --
`A₅` has order 60 and contains subgroups of orders 2, 3, 4, 5, 6, 10 and 12.
What `A₅` has none of is a *normal* subgroup, which is why it is simple and
why it cannot be taken apart.

For mod-6 the distinction happens to be invisible, and for a reason worth
naming: mod-6 is *abelian*, and in an abelian group every subgroup is
automatically normal (`g + n - g = n`, since the `g`s cancel). So all four
subgroups above are normal, and we may quotient by any of them.

That lets us decompose mod-6 into simple pieces. Build a chain, each step a
normal subgroup of the next, until the successive quotients are all simple:

  `{0}  ◁  {0, 3}  ◁  ℤ/6`

The two quotients along this chain are `{0,3} / {0} ≅ ℤ/2` and
`ℤ/6 / {0,3} ≅ ℤ/3`. Both are cyclic of prime order, hence simple -- they are
atoms, and the chain terminates. Such a chain is called a *composition
series*, and its quotients are the *composition factors*. So mod-6 is built
from the atoms `ℤ/2` and `ℤ/3`.

We could equally have gone through the other subgroup:

  `{0}  ◁  {0, 2, 4}  ◁  ℤ/6`

giving factors `ℤ/3` and then `ℤ/2`. Different route, same two atoms in the
other order. That is not a coincidence: the *Jordan-Hölder theorem* says any
two composition series of a finite group have the same multiset of
composition factors, up to reordering and isomorphism. The atoms of a finite
group are well defined, exactly as the prime factorization of an integer is.

The analogy with `6 = 2 × 3` is close enough to be useful, and in this
particular case even exact: because 2 and 3 are coprime, `ℤ/6 ≅ ℤ/2 × ℤ/3`.
But do not over-trust it. A composition series records the factors, not how
they were glued, and in general the gluing carries real information --
`ℤ/4` and `ℤ/2 × ℤ/2` have the same composition factors (`ℤ/2` twice) and are
not isomorphic. Knowing a group's atoms does not by itself tell you the group.

The classification theorem says: there are *infinitely many* finite
simple groups, but they fall into exactly four families:

  1. *Cyclic groups of prime order*: integers modulo a prime, under addition.
  2. *Alternating groups*: even permutations of N elements.
  3. *Groups of Lie type*: finite analogs of continuous Lie groups.
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
  assoc   : ∀ a b c : α, op (op a b) c = op a (op b c)
  idLeft  : ∀ a : α, op id a = a
  idRight : ∀ a : α, op a id = a

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
  invLeft : ∀ a : α, op (inv a) a = id
  invRight: ∀ a : α, op a (inv a) = id

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
  op      : Int → Int → Int := (· + ·)
  id      : Int := 0
  assoc   : ∀ a b c : Int, (a + b) + c = a + (b + c) := Int.add_assoc
  idLeft  : ∀ a : Int, 0 + a = a := Int.zero_add
  idRight : ∀ a : Int, a + 0 = a := Int.add_zero
  inv     : Int → Int := fun n => -n
  invLeft : ∀ a : Int, (-a) + a = 0 := fun n => Int.add_left_neg n
  invRight: ∀ a : Int, a + (-a) = 0 := fun n => Int.add_right_neg n

#eval (5 : Int) + 3              -- 8
#eval (-5 : Int)                 -- -5
#eval (5 : Int) + (-5)           -- 0

/- @@@
The last example shows what the inverse law means in practice:
adding a number and its inverse gives you back the identity.
@@@ -/

/- @@@
## Example 2: Integers Modulo 3 (Three Position Clock)

Clock hours form a group under addition modulo 12. The set is
{0, 1, ..., 11}, representing the 12 hours, and adding any number of
hours wraps around at 12. We return to the 12-hour clock in the next
lesson, where it becomes our first torsor. For our examples here we'll
simplify to a three position clock: think noon (0), four (1), eight (2),
then back to noon again (0). Each step is a four-hour shift, so the three
positions are the hours 12, 4 and 8.

`Fin 3` is worth a second look given the classification discussion above.
Three is prime, so this is a cyclic group of prime order -- a member of
family 1, and therefore one of the *simple* groups, an atom of group
theory. Its only subgroups are the trivial one and itself. Composition
series do not get shorter than this: `{0} ◁ ℤ/3` already terminates.
@@@ -/

instance : Group (Fin 3) where
  op      : Fin 3 → Fin 3 → Fin 3 := (· + ·)
  id      : Fin 3 := 0
  assoc   : ∀ a b c : Fin 3, (a + b) + c = a + (b + c) := fun a b c => by ext; simp [Fin.add_def, Nat.add_assoc]
  idLeft  : ∀ a : Fin 3, 0 + a = a := fun a => by ext; simp [Fin.add_def]
  idRight : ∀ a : Fin 3, a + 0 = a := fun a => by ext; simp [Fin.add_def]
  inv     : Fin 3 → Fin 3 := fun a => -a
  invLeft : ∀ a : Fin 3, (-a) + a = 0 := fun a => by ext; simp [Fin.add_def, Fin.neg_def]
  invRight: ∀ a : Fin 3, a + (-a) = 0 := fun a => by ext; simp [Fin.add_def, Fin.neg_def]

#eval (1 : Fin 3) + (1 : Fin 3)  -- 2
#eval (2 : Fin 3) + (1 : Fin 3)  -- 0 (wraps around)

/- @@@
## Example 3: Integers Modulo N

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
  op      : Fin 5 → Fin 5 → Fin 5 := (· + ·)
  id      : Fin 5 := 0
  assoc   : ∀ a b c : Fin 5, (a + b) + c = a + (b + c) := fun a b c => by ext; simp [Fin.add_def, Nat.add_assoc]
  idLeft  : ∀ a : Fin 5, 0 + a = a := fun a => by ext; simp [Fin.add_def]
  idRight : ∀ a : Fin 5, a + 0 = a := fun a => by ext; simp [Fin.add_def]
  inv     : Fin 5 → Fin 5 := fun a => -a
  invLeft : ∀ a : Fin 5, (-a) + a = 0 := fun a => by ext; simp [Fin.add_def, Fin.neg_def]
  invRight: ∀ a : Fin 5, a + (-a) = 0 := fun a => by ext; simp [Fin.add_def, Fin.neg_def]

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

Let's write a function that solves `a * x = b` in any group. Note
how the implicit required typeclass instance argumment protects the
code from being used when α has not been equipped with the structure
of a group.
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

/- @@@
## Example 4: The Rational Numbers

ℚ is a group under addition, exactly parallel to `Int`: the operation is
`+`, the identity is `0`, and the inverse of `q` is `-q`. Unlike `Fin n`
there is no wrapping, and unlike `Int` the elements are dense -- but the
group structure is indifferent to both facts. That indifference is the
point of the abstraction.

A warning while we are here. ℚ is a group under *addition*, not under
multiplication: `0` has no multiplicative inverse. Even dropping `0`, the
integers under multiplication are not a group either, since `2` has no
integer inverse. "Multiply by 2, then by 1/2" is a fine intuition for
inverses but a bad example of a group, so be careful with it.
@@@ -/

instance : Group Rat where
  op      : Rat → Rat → Rat := (· + ·)
  id      : Rat := 0
  assoc   : ∀ a b c : Rat, (a + b) + c = a + (b + c) := Rat.add_assoc
  idLeft  : ∀ a : Rat, 0 + a = a := Rat.zero_add
  idRight : ∀ a : Rat, a + 0 = a := Rat.add_zero
  inv     : Rat → Rat := fun q => -q
  invLeft : ∀ a : Rat, (-a) + a = 0 := Rat.neg_add_cancel
  invRight: ∀ a : Rat, a + (-a) = 0 := Rat.add_neg_cancel

#eval (1/2 : Rat) + (1/3 : Rat)        -- 5/6
#eval (1/2 : Rat) + (-(1/2) : Rat)     -- 0 (an element plus its inverse)

/- @@@
## Example 5: The Rational Plane ℚ × ℚ

Groups compose. If `α` and `β` are groups then so is `α × β`, with the
operation applied componentwise and the identity being the pair of
identities. Below is that construction for ℚ × ℚ.

This instance earns its keep in the next two lessons, where ℚ × ℚ becomes
the group of *translations* of the plane -- the first case where thinking of
group elements as actions rather than as numbers really pays.
@@@ -/

instance : Group (Rat × Rat) where
  op      : Rat × Rat → Rat × Rat → Rat × Rat := fun (a, b) (c, d) => (a + c, b + d)
  id      : Rat × Rat := (0, 0)
  assoc   : ∀ a b c : Rat × Rat, ((a.1 + b.1) + c.1, (a.2 + b.2) + c.2) = (a.1 + (b.1 + c.1), a.2 + (b.2 + c.2)) :=
    fun _ _ _ => by
      ext <;> (simp only [Rat.add_assoc])
  idLeft  : ∀ a : Rat × Rat, (0 + a.1, 0 + a.2) = a :=
    fun _ => by
      ext <;> (simp only [Rat.zero_add])
  idRight : ∀ a : Rat × Rat, (a.1 + 0, a.2 + 0) = a :=
    fun _ => by
      ext <;> (simp only [Rat.add_zero])
  inv     : Rat × Rat → Rat × Rat := fun (a, b) => (-a, -b)
  invLeft : ∀ a : Rat × Rat, (-a.1 + a.1, -a.2 + a.2) = (0, 0) :=
    fun _ => by
      ext <;> (simp only [Rat.neg_add_cancel])
  invRight: ∀ a : Rat × Rat, (a.1 + (-a.1), a.2 + (-a.2)) = (0, 0) :=
    fun _ => by
      ext <;> (simp only [Rat.add_neg_cancel])

/- @@@
## Solving Equations: Worked Examples

Recall the `solve` function from earlier: it solves `a * x = b` by computing
`inv(a) * b`. Let's run it on concrete examples.

One notational caution. The prose above writes the group operation
multiplicatively, as `a * x = b`, because that is the conventional way to
discuss groups in the abstract. But every instance in this file is
*additive*: `op` is `+` and `inv` is negation. So `solve (5 : Int) 13` is
solving `5 + x = 13`, not `5 * x = 13`. The abstract operation has no
intrinsic notation; `*` and `+` are both just `op`.
@@@ -/

#eval solve (5 : Int) 13       -- Solves: 5 + x = 13, answer: 8
#eval solve (3 : Fin 5) 0      -- Solves: 3 + x ≡ 0 (mod 5), answer: 2
#eval solve (1/2 : Rat) 2      -- Solves: 1/2 + x = 2, answer: 3/2

/- @@@
## Where This Goes Next

Everything so far has treated a group as a self-contained algebraic object:
a set with an operation. But the opening section described groups as
*symmetry-preserving actions* -- rotations of a square, shifts of a clock --
and we have not yet formalized what it means for a group to act *on*
something distinct from itself.

That is the subject of the next lesson, on **torsors**: sets on which a
group acts freely and transitively. It imports this file and reuses the
`Group` class and the instances above rather than redefining them.
@@@ -/

end Groups
