/- @@@
# Affine Space ℚ² Demo: Type-Safe Geometry

This demo uses the AffineSpace typeclass from E14_AffineSpace to work with
the rational plane (ℚ²). The key insight: **points and vectors are kept
distinct by the type system**.

This means:
- `p + q` (adding two points) is a TYPE ERROR ✗
- `v +ᵥ p` (point translated by vector) is well-typed ✓
- `q -ᵥ p` (displacement between points) is well-typed ✓
- The type system enforces geometric correctness

Mind the operand order: the vector goes on the **left** of `+ᵥ`, the point on
the right. `p +ᵥ v` is not merely unconventional, it does not typecheck --
`vadd` has type `Vector → Point → Point`.

This is what affine spaces are for: geometry without a chosen origin.
@@@ -/

import FPCourse.ClassNotes.E14_AffineSpace
import Mathlib.Tactic.Ring

namespace AffineSpace2DDemo

open AffineSpace

/- @@@
## Type Declarations: Points and Vectors as Distinct Types

We define Point and Vector as distinct types using structure, even though
they both represent pairs of rationals. This forces the type system to keep
them separate at the type level and prevent meaningless operations.
@@@ -/

structure Point : Type where
  x : Rat
  y : Rat
  deriving Repr, DecidableEq

structure Vector : Type where
  dx : Rat
  dy : Rat
  deriving Repr, DecidableEq

@[ext] theorem Point.ext {p q : Point} (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  cases p; cases q; simp at *; exact ⟨hx, hy⟩

@[ext] theorem Vector.ext {v w : Vector} (hdx : v.dx = w.dx) (hdy : v.dy = w.dy) : v = w := by
  cases v; cases w; simp at *; exact ⟨hdx, hdy⟩

/- @@@
## AffineSpace Instance for ℚ² Points and ℚ² Vectors

With distinct Point and Vector types, we instantiate the AffineSpace typeclass.
This gives us +ᵥ (translate point by vector) and -ᵥ (displacement between points).
@@@ -/

instance : AffineSpace.Group Vector where
  op      : Vector → Vector → Vector := fun v₁ v₂ => Vector.mk (v₁.dx + v₂.dx) (v₁.dy + v₂.dy)
  id      : Vector := Vector.mk 0 0
  assoc   : ∀ a b c : Vector, Vector.mk ((a.dx + b.dx) + c.dx) ((a.dy + b.dy) + c.dy) = Vector.mk (a.dx + (b.dx + c.dx)) (a.dy + (b.dy + c.dy)) :=
    fun a b c => by
      apply Vector.ext <;> simp [Rat.add_assoc]
  idLeft  : ∀ a : Vector, Vector.mk (0 + a.dx) (0 + a.dy) = a := fun a => by
    apply Vector.ext <;> simp
  idRight : ∀ a : Vector, Vector.mk (a.dx + 0) (a.dy + 0) = a := fun a => by
    apply Vector.ext <;> simp
  inv     : Vector → Vector := fun v => Vector.mk (-v.dx) (-v.dy)
  invLeft : ∀ a : Vector, Vector.mk (-a.dx + a.dx) (-a.dy + a.dy) = Vector.mk 0 0 := fun a => by
    apply Vector.ext <;> simp
  invRight: ∀ a : Vector, Vector.mk (a.dx + (-a.dx)) (a.dy + (-a.dy)) = Vector.mk 0 0 := fun a => by
    apply Vector.ext <;> simp

instance : AffineSpace Vector Point where
  groupV  := inferInstance
  vadd    : Vector → Point → Point := fun v p => Point.mk (v.dx + p.x) (v.dy + p.y)
  vsub    : Point → Point → Vector := fun q p => Vector.mk (q.x - p.x) (q.y - p.y)
  vaddAssoc := fun v w p => by
    apply Point.ext <;> simp [Group.op, Rat.add_assoc]
  vaddZero := fun p => by
    apply Point.ext <;> simp [Group.id]
  vsubAdd := fun p q => by
    apply Point.ext <;> simp
  addVsub := fun v p => by
    apply Vector.ext <;> simp

/- @@@
## Example 1: Simple Definitions

Define concrete points and vectors in the rational plane ℚ².
Note: These are now distinct types, enforced by the type system.
@@@ -/

def point1 : Point := Point.mk 1 2
def vector1 : Vector := Vector.mk 3 1
def point2 : Point := Point.mk 2 3

/- @@@
## Example 2: Vector Between Two Points

Compute the displacement vector from one point to another.
Using the -ᵥ operator (vector subtraction) from the AffineSpace instance.
@@@ -/

def vec_12 : Vector := point2 -ᵥ point1

#eval point1   -- { x := 1, y := 2 }
#eval vector1  -- { dx := 3, dy := 1 }
#eval vec_12   -- { dx := 1, dy := 1 }

/- Translating point1 by the displacement to point2 lands exactly on point2.
   This is `vsubAdd`, which we proved, so it holds for every pair of points. -/
#eval vec_12 +ᵥ point1          -- { x := 2, y := 3 }, i.e. point2

/- The `-ᵥ` here needs its result type spelled out. In `vsub : P → P → V` the
   vector type `V` appears only in the result, so the two point arguments do
   not determine it, and this file's `-ᵥ` and mathlib's are both in scope. In
   a `def` the declared type settles it; in a nested position like this one it
   does not, so we annotate. See the note in E14 on the same wrinkle. -/

example : (point2 -ᵥ point1 : Vector) +ᵥ point1 = point2 :=
  AffineSpace.vsubAdd point1 point2

/- @@@
## Example 3: Triangle Vertices and Sides

Define a triangle by its three vertices. Compute the sides as displacement vectors.
@@@ -/

def tri_A : Point := Point.mk 0 0
def tri_B : Point := Point.mk 4 0
def tri_C : Point := Point.mk 2 3

/- The displacement vectors forming the sides -/
def side_AB : Vector := tri_B -ᵥ tri_A  -- (4, 0)
def side_BC : Vector := tri_C -ᵥ tri_B  -- (-2, 3)
def side_CA : Vector := tri_A -ᵥ tri_C  -- (-2, -3)

/- @@@
## Example 4: Closure Around a Triangle

Walking around a closed triangle: the sum of all displacement vectors
is the zero vector.

AB + BC + CA = (4, 0) + (-2, 3) + (-2, -3) = (0, 0)

This works because displacement vectors form a group.
@@@ -/

def sum_sides : Vector := Group.op (Group.op side_AB side_BC) side_CA

#eval side_AB    -- { dx := 4, dy := 0 }
#eval side_BC    -- { dx := -2, dy := 3 }
#eval side_CA    -- { dx := -2, dy := -3 }
#eval sum_sides  -- { dx := 0, dy := 0 }

/- @@@
Note that we composed the sides with `Group.op`, the group operation on
`Vector` -- not by reaching into the `dx`/`dy` fields. Displacements compose
because they form a group, and that is the only structure we need here.
@@@ -/

/- @@@
## Example 5: Translation Property

If we translate all vertices of a triangle by the same vector, the
sides of the triangle remain unchanged. This is translation invariance.

Geometric property preserved: the triangle's shape doesn't change under translation.
@@@ -/

def translation_vector : Vector := Vector.mk 5 7

/- Translate each vertex using the +ᵥ operator -/
def tri_A' : Point := translation_vector +ᵥ tri_A
def tri_B' : Point := translation_vector +ᵥ tri_B
def tri_C' : Point := translation_vector +ᵥ tri_C

/- The sides of the translated triangle -/
def side_A'B' : Vector := tri_B' -ᵥ tri_A'

#eval tri_A'      -- { x := 5, y := 7 }
#eval tri_B'      -- { x := 9, y := 7 }
#eval side_A'B'   -- { dx := 4, dy := 0 }  -- same as side_AB
#eval side_A'B' = side_AB   -- true

/- @@@
Rather than assert that in a comment, let us prove it for all vectors and all
pairs of points -- which is a much stronger statement than checking one
triangle:
@@@ -/

theorem translation_invariant (v : Vector) (p q : Point) :
    (AffineSpace.vsub (AffineSpace.vadd v q) (AffineSpace.vadd v p) : Vector)
      = AffineSpace.vsub q p := by
  apply Vector.ext
  · show (v.dx + q.x) - (v.dx + p.x) = q.x - p.x
    ring
  · show (v.dy + q.y) - (v.dy + p.y) = q.y - p.y
    ring

example : side_A'B' = side_AB := translation_invariant translation_vector tri_A tri_B

/- @@@
One honest caveat, because it is the kind of thing that is easy to assert and
wrong. Translation invariance is *not* one of the four affine axioms, and it
does not follow from them alone. Unfolding it reduces to needing
`Group.op v d = Group.op d v` -- that is, the displacement group must be
**commutative**. Our `Vector` group is (it is ℚ² under componentwise
addition), which is why the proof above goes through by `ring`.

A torsor over an arbitrary group does not give you this. Real affine spaces
do, because their displacements form a vector space, and a vector space is an
abelian group by definition. So the property is true here for a reason that
lives outside the four axioms, and it is worth knowing which assumption is
doing the work.
@@@ -/

/- @@@
## Example 6: Parametric Points on a Line

A line through two points can be expressed parametrically without choosing
a special origin. Every point on the line is reachable from one endpoint
by adding a scaled direction vector.
@@@ -/

def line_start : Point := Point.mk 1 1
def line_end : Point := Point.mk 3 5

def direction : Vector := line_end -ᵥ line_start  -- (2, 4)

/- A point on the line at parameter t -/
def point_at_parameter (t : Rat) : Point :=
  (Vector.mk (t * direction.dx) (t * direction.dy)) +ᵥ line_start

#eval direction                 -- { dx := 2, dy := 4 }
#eval point_at_parameter 0      -- { x := 1, y := 1 }  = line_start
#eval point_at_parameter 1      -- { x := 3, y := 5 }  = line_end
#eval point_at_parameter (1/2)  -- { x := 2, y := 3 }  = midpoint
#eval point_at_parameter 2      -- { x := 5, y := 9 }  = beyond line_end

/- @@@
Scaling the direction by `t` required reaching into the `dx`/`dy` fields,
because scalar multiplication is *not* part of the affine structure. A group
of displacements lets us compose and invert them, never scale them. To
parametrize a line we need `Vector` to be a vector space, not merely a group --
which is precisely the structure the vector space lesson adds.
@@@ -/

/- @@@
## Key Property: Type Safety

The affine space prevents adding two points together. Try uncommenting:

  -- example : Point := tri_A + tri_B  -- TYPE ERROR: no `Add Point` instance

The operation `tri_A + tri_B` would be meaningless in affine geometry
(you can't add two locations). The type system enforces this:

- Allowed: `tri_A -ᵥ tri_B` (displacement from one point to the other)
- Allowed: `direction +ᵥ tri_A` (translate a point by a displacement)
- NOT ALLOWED: `tri_A + tri_B` (add two points -- type error)
- NOT ALLOWED: `tri_A +ᵥ direction` (operands reversed -- type error)

Note that the last one is a type error too. `+ᵥ` is not symmetric: it consumes
a vector and a point, in that order, and returns a point. Vectors form a group
and so *can* be added to each other (`Group.op side_AB side_BC`); points
cannot. That asymmetry is the whole content of the point/vector distinction.

This is the entire purpose of affine spaces: to capture the pure geometry
of a space without the arithmetic operations that would come with vector
space structure.
@@@ -/

/- @@@
## Summary: Affine Space Axioms

Everything in this demo flows from four axioms:

1. **Associativity of translation**:
   `v +ᵥ (w +ᵥ p) = (v + w) +ᵥ p`
   Moving by two vectors in sequence is the same as moving by their sum.

2. **Identity element**:
   `0 +ᵥ p = p`
   Adding the zero vector doesn't move anything.

3. **Recovery from difference**:
   `(q -ᵥ p) +ᵥ p = q`
   The displacement from p to q, when applied to p, recovers q.

4. **Freeness (unique displacement)**:
   `(v +ᵥ p) -ᵥ p = v`
   Translating p by v, then computing the displacement back, recovers v.

These four axioms are sufficient to capture the geometry of affine spaces, and
the `AffineSpace` typeclass makes Lean check them for every implementation --
including this one, where all four are now proven rather than assumed.

They are *not*, however, minimal. Axiom 2 is derivable from the other three.
Sketch: axiom 4 makes `vadd · p` injective, so from `(p -ᵥ p) +ᵥ p = p`
(axiom 3) one derives that `p -ᵥ p` is idempotent under the group operation,
and the only idempotent in a group is the identity; axiom 2 follows. We keep
axiom 2 anyway, because stating it makes the structure easier to read and
costs nothing -- but "these are the axioms" and "these are independent" are
different claims, and only the first one is true here.

The key insight: **An affine space is geometry without a distinguished origin.**
All relationships between points are expressed through the group action of
displacement vectors. This is why affine geometry is so powerful—it works
in any context where you want to reason about locations and movements, without
imposing the arithmetic of vector spaces.
@@@ -/

end AffineSpace2DDemo
