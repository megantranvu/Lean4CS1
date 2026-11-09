```lean
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Real.Basic
```

# Affine Spaces: Groups Acting on Structure-Free Geometry

## What Affine Spaces Are: Geometry Without an Origin

Last class we saw that a *torsor* is a set `T` where a group `G` acts
in two special ways: *freely* (no non-identity element fixes any point)
and *transitively* (any two points are related by some group element).

An *affine space* is a torsor with a specific structure: we have a group `V`
(the "displacement vectors") acting on a set `P` (the "points") in a torsor fashion.
The group structure on `V` lets us describe how displacements compose:
to move from point `p` by displacement `v`, we compute `v +ᵥ p`.
The freeness and transitivity of the action mean every pair of points has a unique
displacement vector relating them, and conversely, every vector can translate
any point to some other point.

Note the operand order: the *vector* goes on the left, the *point* on the right.
That is not arbitrary. It is what makes the composition law below read in the
same direction as function composition, and it is the convention mathlib uses
for `AddTorsor`. Writing `p + v` instead would force the composition law to
reverse the group operation, which is invisible for ℚ (where addition commutes)
but wrong for any non-commutative group of displacements.

Why does this matter? Because it captures *pure geometry* -- the essence
of space without imposing a choice of origin or coordinate system. In a vector space,
there's a distinguished point: the zero vector, which is both an algebraic and
geometric identity. In an affine space, there's no such point. All points
are equivalent, related only through the group action.

Examples: points in a Euclidean plane, events in spacetime (with vectors
representing intervals), locations on a calendar (with integer vectors
representing day offsets), positions in a color space.

An affine space has two core operations:
  - *Point translation*: given vector `v` and point `p`, compute `v +ᵥ p` (new point)
  - *Vector subtraction*: given points `p` and `q`, compute `q -ᵥ p` (displacement vector)

These must satisfy:
  - `v +ᵥ (w +ᵥ p) = (v + w) +ᵥ p`  (translating twice = translating by the sum)
  - `0 +ᵥ p = p`                     (the zero vector doesn't move anything)
  - `(q -ᵥ p) +ᵥ p = q`              (the displacement from p to q, applied to p, reaches q)
  - `(v +ᵥ p) -ᵥ p = v`              (translating p by v, then differencing against p, recovers v)
```lean
namespace AffineSpace
```

## Recap: `Group` (from the groups lesson)

We'll need the group structure we developed earlier: an associative
operation with identity and inverses.
```lean
class Group (α : Type) where
  op      : α → α → α
  id      : α
  assoc   : ∀ a b c, op (op a b) c = op a (op b c)
  idLeft  : ∀ a, op id a = a
  idRight : ∀ a, op a id = a
  inv     : α → α
  invLeft : ∀ a, op (inv a) a = id
  invRight: ∀ a, op a (inv a) = id

instance {α : Type} [Group α] : Add α where add := Group.op
instance {α : Type} [Group α] : Neg α where neg := Group.inv
instance {α : Type} [Group α] : Zero α where zero := Group.id
```

## `AffineSpace`: A Torsor Structure

An affine space is exactly a torsor: it pairs a set of points `P` with a group `V`
(the "vectors" or "displacements") where `P` is a torsor for the group action of `V`.
The group acts on points via a translation operation in a way that is both
*free* (no non-identity group element fixes any point) and *transitive*
(any two points are related by some group element). This means:
- Every pair of points has a unique displacement vector between them
- Every vector can translate any point to some other point

Here, we bundle the translation operation (`vadd`) and its inverse (`vsub`)
with proofs that they satisfy the affine axioms. The `VAdd` and `VSub`
typeclasses provide standard notation: `v +ᵥ p` for translation
and `q -ᵥ p` for vector subtraction.
```lean
class AffineSpace (V : Type) (P : Type) where
  [groupV : Group V]
  vadd    : V → P → P
  vsub    : P → P → V
  vaddAssoc : ∀ v w : V, ∀ p : P, vadd v (vadd w p) = vadd (groupV.op v w) p
  vaddZero  : ∀ p : P, vadd groupV.id p = p
  vsubAdd   : ∀ p q : P, vadd (vsub q p) p = q
  addVsub   : ∀ v : V, ∀ p : P, vsub (vadd v p) p = v

/- Standard notation typeclasses for affine operations -/
class VAdd (V : Type) (P : Type) where vadd : V → P → P
class VSub (P : Type) (V : Type) where vsub : P → P → V

instance {V P : Type} [AffineSpace V P] : VAdd V P where vadd := AffineSpace.vadd
instance {V P : Type} [AffineSpace V P] : VSub P V where vsub := AffineSpace.vsub

-- Both at precedence 65, matching mathlib. `-ᵥ` must bind tighter than `=`
-- (precedence 50), or a goal like `q -ᵥ p = v` fails to parse.
infixl:65 " +ᵥ " => VAdd.vadd
infixl:65 " -ᵥ " => VSub.vsub
```

## Connection to the `Torsor` Class

An affine space is the same mathematical idea as a torsor -- a group acting
freely and transitively -- but packaged differently, and the difference is
worth being precise about rather than calling it mere notation.

`Torsor` states transitivity as an *existence claim*:

  `actTransitive : ∀ t₁ t₂ : T, ∃ g : G, act g t₁ = t₂`

`AffineSpace` instead provides an *operation* that produces the group element:

  `vsub : P → P → V`

That is the real change: a proof that something exists becomes a function
that computes it. The existential tells you two points *are* related by some
displacement; `vsub` hands you the displacement. Only the second lets you
write `q -ᵥ p` and get a value out, which is why the geometry in this file
computes while the torsor version could only be reasoned about.

Freeness also changes character. In `Torsor` it is a separate axiom; here it
is a consequence of `addVsub`, which says `vsub` inverts `vadd` and so forces
the displacement between two points to be *unique*, not merely existent.

What is *not* a difference is the separation of points from vectors. `Torsor`'s
`act : G → T → T` already takes two distinct type parameters, and the last
instance of the previous lesson used them -- `Torsor Vector2 Point2`. The
signature `vadd : V → P → P` is the same shape. Keeping points and vectors
apart is good practice in either class, and this file goes on doing it; it is
just not what `AffineSpace` adds. What `AffineSpace` adds is `vsub`.
## Instance 1: Points and Vectors in the Rational Plane

The rational plane. Points are locations, vectors are displacements, and the
two get *distinct types* -- `Point2` and `Vector2` -- even though both are
implemented as a pair of rationals. A `structure` with a single field is how
Lean says "same representation, different type", and it is what stops
`p + q` for two points from typechecking.

These are the same two types introduced at the end of the torsors lesson. We
redeclare them here because each lesson in this sequence stands alone.
```lean
structure Vector2 where
  ofPair ::
  toPair : Rat × Rat
deriving DecidableEq

structure Point2 where
  ofPair ::
  toPair : Rat × Rat
deriving DecidableEq

/- Print the underlying pair, tagged with the type it came from, so that the
   `#eval`s below say which role each value is playing. -/
instance : Repr Vector2 where reprPrec v _ := "Vector2 " ++ repr v.toPair
instance : Repr Point2  where reprPrec p _ := "Point2 "  ++ repr p.toPair
```

First the group of pairs, which is where the componentwise arithmetic lives:
```lean
instance : Group (Rat × Rat) where
  op      : Rat × Rat → Rat × Rat → Rat × Rat := fun (a, b) (c, d) => (a + c, b + d)
  id      : Rat × Rat := (0, 0)
  assoc   : ∀ a b c : Rat × Rat, ((a.1 + b.1) + c.1, (a.2 + b.2) + c.2) = (a.1 + (b.1 + c.1), a.2 + (b.2 + c.2)) := fun _ _ _ => by simp [Rat.add_assoc]
  idLeft  : ∀ a : Rat × Rat, (0 + a.1, 0 + a.2) = a := fun _ => by simp
  idRight : ∀ a : Rat × Rat, (a.1 + 0, a.2 + 0) = a := fun _ => by simp
  inv     : Rat × Rat → Rat × Rat := fun (a, b) => (-a, -b)
  invLeft : ∀ a : Rat × Rat, (-a.1 + a.1, -a.2 + a.2) = (0, 0) := fun (a, b) => by ext <;> simp
  invRight: ∀ a : Rat × Rat, (a.1 + (-a.1), a.2 + (-a.2)) = (0, 0) := fun (a, b) => by ext <;> simp
```

Now `Vector2` becomes a group by *transporting* that instance across the
wrapper: each operation unwraps its arguments, defers to the pair instance,
and wraps the result. Each law then follows from the corresponding law on
pairs by `congrArg` -- "equal arguments give equal results" -- which lifts an
equation on pairs to an equation on `Vector2`. No arithmetic is redone.
```lean
instance : Group Vector2 where
  op v w      := ⟨Group.op v.toPair w.toPair⟩
  id          := ⟨Group.id⟩
  inv v       := ⟨Group.inv v.toPair⟩
  assoc a b c := congrArg Vector2.ofPair (Group.assoc a.toPair b.toPair c.toPair)
  idLeft a    := congrArg Vector2.ofPair (Group.idLeft a.toPair)
  idRight a   := congrArg Vector2.ofPair (Group.idRight a.toPair)
  invLeft a   := congrArg Vector2.ofPair (Group.invLeft a.toPair)
  invRight a  := congrArg Vector2.ofPair (Group.invRight a.toPair)
```

And the affine space itself. Read the two operation types carefully, because
they are the whole design:

  `vadd : Vector2 → Point2 → Point2`   a displacement moves a point
  `vsub : Point2 → Point2 → Vector2`   two points determine a displacement

`vsub` is defined as "compose with the inverse": the displacement from `p` to
`q` is `q` combined with the undoing of `p`. For ℚ² that computes exactly the
componentwise difference, but writing it group-theoretically makes all four
proofs one-liners, since each is just associativity and the inverse laws.
```lean
instance : AffineSpace Vector2 Point2 where
  groupV    := inferInstance
  vadd v p  := ⟨Group.op v.toPair p.toPair⟩
  vsub q p  := ⟨Group.op q.toPair (Group.inv p.toPair)⟩
  -- v +ᵥ (w +ᵥ p) = (v + w) +ᵥ p is associativity on pairs, read right to left
  vaddAssoc v w p :=
    congrArg Point2.ofPair (Group.assoc v.toPair w.toPair p.toPair).symm
  -- 0 +ᵥ p = p is the left identity law
  vaddZero p := congrArg Point2.ofPair (Group.idLeft p.toPair)
  -- (q -ᵥ p) +ᵥ p = q: the `inv p` cancels against the `p`
  vsubAdd p q := by
    show Point2.ofPair (Group.op (Group.op q.toPair (Group.inv p.toPair)) p.toPair) = q
    rw [Group.assoc, Group.invLeft, Group.idRight]
  -- (v +ᵥ p) -ᵥ p = v: the same cancellation, one step further along
  addVsub v p := by
    show Vector2.ofPair (Group.op (Group.op v.toPair p.toPair) (Group.inv p.toPair)) = v
    rw [Group.assoc, Group.invRight, Group.idRight]
```

This instance encodes a fundamental truth: the rational plane has no
distinguished origin. We can pick any point as a reference, and describe
all others relative to it via vectors. The structure guarantees that the
two directions of translation (`+ᵥ` and `-ᵥ`) are inverses.

It also buys the type safety the previous lesson was reaching for. All of
these are errors rather than meaningless values:

  `Group.op (Point2.ofPair (1, 1)) (Point2.ofPair (2, 2))`
      -- no `Group Point2` instance: points do not add
  `AffineSpace.vadd (Point2.ofPair (1, 1)) (Point2.ofPair (2, 2))`
      -- `vadd` takes a vector first, and a point is not a vector
  `AffineSpace.vsub (Vector2.ofPair (1, 1)) (Vector2.ofPair (2, 2))`
      -- `vsub` differences two *points*

Lean reports each as a failure to synthesize the instance that would be
needed for the expression to mean anything -- the type checker saying,
correctly, that there is no such operation.
## A Second Instance? Where the Missing Structure Shows Up

It is natural to want another instance, and the obvious candidate is
instructive precisely because it fails. Take any type `P` with decidable
equality as the points, and let the vectors be `Rat`. Now write `vadd`: what
does it mean to displace an arbitrary `p : P` by the rational `3`? Nothing
about `P` answers that. Supplying an answer *is* supplying `P` with a
ℚ-vector-space structure, which is the structure the next lesson adds. There
is no shortcut around it.

The other tempting move is to let a type act on itself -- `AffineSpace V V`,
the shape the first two torsor instances had. The axioms are satisfiable, so
it is a genuine affine space, and the vector space lesson will build exactly
that for ℚ. But it collapses points into vectors, which costs the type safety
demonstrated above. Worth doing deliberately; not worth doing by accident.
## Properties of Affine Spaces

Once we have an affine space, we can derive useful facts. For instance,
vector subtraction is a kind of "difference" operation: the vector that
takes us from one point to another is unique, and going from p to q to r
is the same as going directly from p to r.

This is captured in the affine space axioms:

  **vsubAdd**: `(q -ᵥ p) +ᵥ p = q`
  ```
    Geometric meaning: if we take the vector from p to q, and apply it to p,
    we get back to q.

    p ──────────(q - p)─────────> q
            (add to p)

    This says: the displacement from p to q, when added to p, reconstructs q.
  ```

  **addVsub**: `(v +ᵥ p) -ᵥ p = v`
  ```
    Geometric meaning: if we translate p by vector v, the difference between
    the new point and the original is the vector v.

    p ─────v────> (v + p)
            (subtract p)

    This says: translating p by v, then computing the vector back to p,
    recovers the original vector v.
  ```
## Concrete Examples: Small Geometric Worlds

Now let's see the affine space in action with concrete geometric worlds.
The key is that all operations are coordinate-free and don't require choosing
an origin.
### Example 1: A Triangle in the Rational Plane

Define three vertices of a triangle. These are `Point2`s -- locations, not
displacements:
```lean
def triangle_A : Point2 := ⟨(1, 2)⟩
def triangle_B : Point2 := ⟨(4, 2)⟩
def triangle_C : Point2 := ⟨(2, 5)⟩
```

The sides are `Vector2`s: displacements between the vertices, computed with
the `-ᵥ` operator. Note that the types are not a matter of our labelling --
`vsub` *returns* a `Vector2`, so these definitions could not be annotated
`Point2` even if we tried.
```lean
def side_AB : Vector2 := triangle_B -ᵥ triangle_A  -- (3, 0)
def side_BC : Vector2 := triangle_C -ᵥ triangle_B  -- (-2, 3)
def side_CA : Vector2 := triangle_A -ᵥ triangle_C  -- (-1, -3)
```

Verify the closure property: going around the triangle brings you back home.
The sum of all displacement vectors around a closed loop is the zero vector.

Displacements compose with the *group* operation on `V` -- that is the whole
point of requiring `V` to be a group, so we use `Group.op` rather than
re-deriving componentwise addition by hand.
```lean
def close_the_loop : Vector2 := Group.op (Group.op side_AB side_BC) side_CA

#eval side_AB         -- Vector2 (3, 0)
#eval side_BC         -- Vector2 (-2, 3)
#eval side_CA         -- Vector2 (-1, -3)
#eval close_the_loop  -- Vector2 (0, 0): AB + BC + CA = 0, the loop closes
```

### Example 2: Translation and Reconstruction

Translate a point by a vector, then recover the original vector from the
difference.
```lean
def point_P : Point2 := ⟨(0, 0)⟩
def vector_v : Vector2 := ⟨(3, 4)⟩
```

Here the `+ᵥ` notation simply works, and it is worth knowing why, because
with the wrong types it would not. Mathlib defines its own `+ᵥ`, and both
notations are in scope in this file. When points and vectors are the *same*
type -- say both `ℚ × ℚ` -- mathlib's instance for an additive monoid acting
on itself applies alongside ours, and `vector_v +ᵥ point_P` is genuinely
ambiguous: Lean reports an overloaded notation and refuses to guess.

With `Vector2` and `Point2` as distinct types of our own, mathlib has no
instance for them, so exactly one of the two readings elaborates and the
ambiguity disappears. The notation working is thus a small piece of evidence
that the types are now carrying the distinction the lesson is about.
```lean
def translated_point : Point2 := vector_v +ᵥ point_P
```

Now recover the original vector by taking the difference:
```lean
def recovered_vector : Vector2 := translated_point -ᵥ point_P

#eval translated_point                  -- Point2 (3, 4)
#eval recovered_vector                  -- Vector2 (3, 4)
#eval recovered_vector = vector_v       -- true
```

That last line is the `addVsub` axiom showing up as a computation rather than
a claim: `(v +ᵥ p) -ᵥ p = v`. Since we have actually *proven* `addVsub` for
this instance, the equality is guaranteed for every `v` and `p`, not just the
one pair we happened to evaluate.

Both operators work inside the statement below, too:
```lean
example : (vector_v +ᵥ point_P) -ᵥ point_P = vector_v :=
  AffineSpace.addVsub vector_v point_P
```

One residual wrinkle, worth stating precisely rather than leaving as folklore.
In `vsub : P → P → V` the vector type `V` appears only in the *result*, so the
arguments alone do not determine it. Wherever there is a result type to guide
elaboration -- a `def`'s type annotation, or the right-hand side of the `=`
above -- `-ᵥ` resolves fine. Where there is none, as in a nested position
like `(q -ᵥ p) +ᵥ p` stated for arbitrary points, the overloaded notation is
ambiguous and needs a nudge:
```lean
example (p q : Point2) : (q -ᵥ p : Vector2) +ᵥ p = q :=
  AffineSpace.vsubAdd p q
```

### Example 3: Geometric Relationships Without an Origin

Consider a line defined by two points. We can describe all points on the line
using just the affine structure — no special origin needed.
```lean
def line_point_1 : Point2 := ⟨(1, 1)⟩
def line_point_2 : Point2 := ⟨(2, 3)⟩

def direction : Vector2 := line_point_2 -ᵥ line_point_1  -- (1, 2)
```

A point at t=2 along this line (2 times the direction vector from point_1):
```lean
def point_on_line_t2 : Point2 :=
  (Vector2.ofPair (2 * direction.toPair.1, 2 * direction.toPair.2)) +ᵥ line_point_1

#eval direction         -- Vector2 (1, 2)
#eval point_on_line_t2  -- Point2 (3, 5)
```

Note what we had to do to scale the direction vector: we unwrapped it, reached
into the components, multiplied, and wrapped it back up. That is *not* an
affine operation. An affine space gives us a group of displacements, and a
group only lets us compose and invert them -- it has no notion of "twice this
vector." Scaling needs `V` to carry scalar multiplication, i.e. to be a vector
space, which is the structure the next lesson adds. The affine axioms alone
cannot parametrize a line.
The affine space structure lets us:
  - Define geometric objects (lines, triangles) by their points
  - Compute displacements between points without a global coordinate system
  - Verify geometric properties (like closure of a triangle)
  - Reconstruct vectors from differences

All of this works *purely relationally* — we never need to pick a special point
as "the origin." The geometry emerges from the group action alone.
The key insight: affine spaces capture *pure geometry* in the sense that
we can describe the relationships between points without choosing an origin.
The group action encodes all the geometric information we need.

In the next lesson we add the missing structure: scalar multiplication, which
turns the group of displacements into a *vector space*. Rather than build it
from scratch as we did here, we will switch strategy and use mathlib's
`Module` typeclass -- a deliberate contrast worth noticing, since it is the
difference between defining an abstraction to understand it and reusing one
to get work done.
```lean
end AffineSpace
```


<div class="issue-box">📝 <a href="https://github.com/kevinsullivan/Lean4CS1/issues/new">Report an issue</a> with this section</div>

