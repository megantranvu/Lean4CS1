import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

/- @@@
# Vector Spaces: Modules Over a Field

## What Vector Spaces Are: Linear Combinations and Dimension

A *vector space* is an algebraic structure that lets you add elements
together and scale them by numbers from a field (like ℚ or ℝ). The key
idea is *linearity*: the operations are simple, predictable, and compose
in a way that lets you reason about high-dimensional geometry using
low-dimensional intuitions.

More formally, a vector space `V` over a field `F` is:
  - An abelian (commutative) group under addition, with identity `0`
  - A scalar multiplication operation `• : F → V → V` for `f : F` and `v : V`
  - Compatibility laws that ensure scalar multiplication "respects" both
    the field structure and the vector space structure

Vector spaces are the language of linear algebra: every line, plane,
or hyperplane you've encountered is a vector space. The span of a set
of vectors is a vector space. The kernel of a linear map is a vector
space. The central concept of *linear independence* and *dimension*
emerge naturally from the structure.

In today's lesson, we formalize vector spaces using Lean's standard library
definitions. Rather than re-implementing everything from scratch, we'll
leverage mathlib's `Field` typeclass for scalars and the `Module` typeclass,
which bundles the vector space operations and laws together in Lean's
modern typeclass system.

## Why Use Mathlib Here?

Previous lessons (E11–E13) built custom typeclasses to understand structure.
Here, we shift strategy: Lean's mathlib has mature, battle-tested definitions
of fields and modules. Rather than re-derive everything, we leverage them.

This is realistic: in practice, you build custom types for *new* problems,
but reuse standard library abstractions for well-understood mathematics.

The Module typeclass is exactly what we need: a vector space is a module
over a field. Mathlib's instances automatically handle 1D, 2D, 3D, etc.
without requiring you to re-prove the axioms for each dimension.

**The payoff**: one theorem about modules instantly applies to ℚ, ℚ², ℚ³,
spaces of polynomials, and infinite-dimensional Hilbert spaces—anywhere
the Module structure holds.

## Why Vector Spaces Matter

Vector spaces unify a hundred different-looking problems into a single
framework:
  - Solutions to systems of linear equations
  - Probability distributions (if you drop the "must be positive" constraint)
  - Images and filters in computer graphics
  - Quantum states in quantum mechanics
  - Gradients and optimization in machine learning

The structure is so fundamental that once you understand one vector space,
you understand them all.
@@@ -/

namespace VectorSpaces

/- @@@
## Vector Space Instances in Lean's Mathlib

Mathlib has a mature definition of this structure, but it pays to be precise
about what it is *called*, because a reasonable expectation turns out to be
wrong: **mathlib has no `VectorSpace` typeclass.** Looking for one is a dead
end. There is only `Module`.

`Module R M` says that `M` is a module over the semiring `R`: `M` is an
additive commutative group, and `R` acts on it by a scalar multiplication
satisfying the usual compatibility laws.

A vector space is then not a separate structure but a *special case* of that
one: `Module K V` where the scalars `K` form a field. "Vector space" is
vocabulary for that situation rather than a class to instantiate, so there is
nothing additional to declare. If you have a `Module` and your scalars are a
field, you already have a vector space, and every `Module` lemma applies to
it unchanged.

What the field assumption adds is that non-zero scalars become invertible, so
a scaling can be undone. That is what gives vector spaces bases and a
well-defined dimension, which modules in general may lack.

The key operations are:
  - `+ : V → V → V` (addition)
  - `• : F → V → V` (scalar multiplication, written with the `•` symbol)
  - `0 : V` (additive identity)
  - `- : V → V` (negation)

These come with laws bundled into the typeclasses `Add`, `SMul`, `Zero`, `Neg`,
and the full `Module` structure.
@@@ -/

/- @@@
## Instance 1: ℚ as a Vector Space Over Itself

The rational numbers ℚ form a vector space over themselves. Addition is
ordinary rational addition, and scalar multiplication is ordinary rational
multiplication. This is the simplest non-trivial example.

In mathlib this instance is built-in: any field is a module over itself, and
being a field, it is therefore a vector space over itself.

Rather than assert that, we can ask Lean. The two `#check`s below are the
whole content of "ℚ is a ℚ-vector space" -- a `Module` instance plus the fact
that the scalars are a field. There is no third `VectorSpace` instance to
look for, which is the point made above.
@@@ -/

/- ℚ is a module over itself... -/
#check (inferInstance : Module Rat Rat)

/- ...and ℚ is a field. Together: ℚ is a vector space over ℚ. -/
#check (inferInstance : Field Rat)

/- Basic operations in the 1D vector space ℚ -/
#eval (2 : Rat) * (3 : Rat)  -- 6 (scalar multiplication)
#eval (1 : Rat) * (5 : Rat)  -- 5 (identity element: 1 • v = v)
#eval (2 : Rat) + (3 : Rat)  -- 5 (vector addition)

/- @@@
The rational numbers are a concrete representation of a 1-dimensional vector
space. Any two non-zero rationals are linearly independent in the sense that
neither is a scalar multiple of the other unless they're equal (up to sign).
Wait, that's not quite right for a 1D space...

In a 1-dimensional space, any two vectors are linearly *dependent*: one is a
scalar multiple of the other (or one is zero). This is true for ℚ: any rational
q₁ can be expressed as `c * q₂` for some c (as long as q₂ ≠ 0).
@@@ -/

/- @@@
## Naming Our Vector Types

Before the next two instances, a change of representation that matters for
everything that follows. So far the vectors have *been* ℚ, and the obvious
next step would be to let them be ℚ × ℚ. That works, and it is what mathlib's
generic product instance gives us for free -- but it leaves the vectors of the
plane indistinguishable from any other pair of rationals, including the
*points* of the plane, which the affine space lesson went to some trouble to
keep apart.

So we give the vectors their own types, `Vector2` and `Vector3`, each a
`structure` wrapping the representation it is implemented as. This is the same
device used for `Point2` and `Vector2` in the torsors and affine space
lessons, where it is what makes `p + q` for two points a type error.

It is not free. Mathlib's `Module ℚ (ℚ × ℚ)` instance is about `ℚ × ℚ`, and
`Vector2` is not `ℚ × ℚ` -- that is the entire point of declaring it. So the
structure has to be *transported* across the wrapper. The good news is that
transporting is not re-proving: mathlib has lemmas that take an injective map
into a known module and hand back the module structure on the source. Every
side condition we have to supply below is `rfl`, because unwrapping, operating
and rewrapping is definitionally the same as operating on the representation.

## Instance 2: `Vector2`, the Rational Plane

The canonical 2-dimensional vector space over ℚ. First the type, printing as
its underlying pair so the `#eval`s stay readable:
@@@ -/

structure Vector2 where
  ofPair ::
  toPair : Rat × Rat
deriving DecidableEq

instance : Repr Vector2 where reprPrec v _ := "Vector2 " ++ repr v.toPair

/- @@@
The wrapper is injective -- two `Vector2`s with the same pair are the same
`Vector2`. That is the map we transport along.
@@@ -/

theorem Vector2.toPair_injective : Function.Injective Vector2.toPair :=
  fun _ _ h => congrArg Vector2.ofPair h

/- @@@
Next the operations, each defined by unwrapping, deferring to ℚ × ℚ, and
wrapping back. The `ℕ` and `ℤ` scalar actions are not decoration: mathlib's
`AddCommGroup` carries them as fields, so the transport asks for them.
@@@ -/

instance : Zero Vector2     where zero     := ⟨0⟩
instance : Add Vector2      where add v w  := ⟨v.toPair + w.toPair⟩
instance : Neg Vector2      where neg v    := ⟨-v.toPair⟩
instance : Sub Vector2      where sub v w  := ⟨v.toPair - w.toPair⟩
instance : SMul Nat Vector2 where smul n v := ⟨n • v.toPair⟩
instance : SMul Int Vector2 where smul n v := ⟨n • v.toPair⟩
instance : SMul Rat Vector2 where smul a v := ⟨a • v.toPair⟩

/- @@@
And now the two transports. `Function.Injective.addCommGroup` takes the
injection plus a proof that it commutes with each operation, and returns the
additive group structure; `Function.Injective.module` does the same for scalar
multiplication, given the injection packaged as an additive homomorphism.

Note what is *absent*: not one of the module axioms is proved here. They are
mathlib's, already proved for ℚ × ℚ. The `rfl`s only say that our operations
agree with mathlib's through the wrapper.
@@@ -/

instance : AddCommGroup Vector2 :=
  Vector2.toPair_injective.addCommGroup Vector2.toPair
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

def Vector2.toPairHom : Vector2 →+ Rat × Rat where
  toFun := Vector2.toPair
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module Rat Vector2 :=
  Function.Injective.module Rat Vector2.toPairHom Vector2.toPair_injective
    (fun _ _ => rfl)

/- @@@
The payoff: `Vector2` is now a ℚ-vector space in mathlib's eyes, so the real
`+` and `•` work on it and every `Module` lemma applies.
@@@ -/

#check (inferInstance : Module Rat Vector2)

#eval Vector2.ofPair (2, 3) + Vector2.ofPair (1, -1)
      -- Vector2 (3, 2) (componentwise addition)

#eval (1/2 : Rat) • Vector2.ofPair (2, 3)
      -- Vector2 (1, (3 : Rat)/2) (scalar multiplication)

/- @@@
Compare this with the affine space lesson, which hand-wrote componentwise
arithmetic and proved each law. Here we wrote operations and no proofs. The
rational plane is our first "true" vector space: it has dimension 2, and
linear combinations of two independent vectors (say `(1, 0)` and `(0, 1)`)
span all of it.
@@@ -/

/- @@@
## Instance 3: `Vector3`, 3D Rational Space

The pattern extends to three dimensions without a new idea -- which is the
point of showing it. The representation is `ℚ × ℚ × ℚ`, mathlib's product
instances make that a module over ℚ, and the same two transports carry the
structure across the wrapper.
@@@ -/

structure Vector3 where
  ofTriple ::
  toTriple : Rat × Rat × Rat
deriving DecidableEq

instance : Repr Vector3 where reprPrec v _ := "Vector3 " ++ repr v.toTriple

theorem Vector3.toTriple_injective : Function.Injective Vector3.toTriple :=
  fun _ _ h => congrArg Vector3.ofTriple h

instance : Zero Vector3     where zero     := ⟨0⟩
instance : Add Vector3      where add v w  := ⟨v.toTriple + w.toTriple⟩
instance : Neg Vector3      where neg v    := ⟨-v.toTriple⟩
instance : Sub Vector3      where sub v w  := ⟨v.toTriple - w.toTriple⟩
instance : SMul Nat Vector3 where smul n v := ⟨n • v.toTriple⟩
instance : SMul Int Vector3 where smul n v := ⟨n • v.toTriple⟩
instance : SMul Rat Vector3 where smul a v := ⟨a • v.toTriple⟩

instance : AddCommGroup Vector3 :=
  Vector3.toTriple_injective.addCommGroup Vector3.toTriple
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

def Vector3.toTripleHom : Vector3 →+ Rat × Rat × Rat where
  toFun := Vector3.toTriple
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module Rat Vector3 :=
  Function.Injective.module Rat Vector3.toTripleHom Vector3.toTriple_injective
    (fun _ _ => rfl)

#eval Vector3.ofTriple (1, 2, 3) + Vector3.ofTriple (1, 1, 1)
      -- Vector3 (2, 3, 4) (componentwise addition)

#eval (1/2 : Rat) • Vector3.ofTriple (2, 4, 6)
      -- Vector3 (1, 2, 3) (scalar multiplication)

/- @@@
In 3D space, three linearly independent vectors (such as the standard basis
`(1, 0, 0)`, `(0, 1, 0)`, `(0, 0, 1)`) span the whole space. This is the
geometric foundation of 3D computer graphics, physics simulations, and much of
applied mathematics.

Note also what the types now prevent. `Vector2` and `Vector3` are different
types, so mixing dimensions -- adding a 2D vector to a 3D one -- is a type
error rather than a shape mismatch discovered at runtime. With bare `ℚ × ℚ`
and `ℚ × ℚ × ℚ` that was already true, but only by accident of their
representations; here it is true by declaration.
@@@ -/

/- @@@
## Vector Space Properties from Mathlib

Once we have the vector space structure in place, mathlib provides powerful
theorems that hold automatically:

- **Distributivity**: `s • (v + w) = s • v + s • w`
- **Compatibility**: `(s * t) • v = s • (t • v)`
- **Identity**: `1 • v = v`
- **Zero properties**: `0 • v = 0` and `s • 0 = 0`

These laws ensure that any computation we do with scalar multiplication and
addition is consistent and well-defined.

Unlike our custom formalization in the affine space lesson, we don't need to
re-prove these axioms for each instance. Mathlib's generic instances handle
the boilerplate, and we get the theorems "for free" as long as we build our
instances from mathlib's building blocks -- which is exactly what the two
transports above did. Naming our own vector types cost us a short list of
operation definitions; it cost us no proofs about those operations.
@@@ -/

/- @@@
## Linear Maps (Preview)

In the full theory of vector spaces, we're interested not just in the spaces
themselves, but in *functions between them that preserve the structure*.

A linear map `f : V → W` between vector spaces is one that satisfies:
  - `f (v₁ + v₂) = f v₁ + f v₂` (respects addition)
  - `f (s • v) = s • f v` (respects scalar multiplication)

Linear maps are crucial because they let us translate geometric intuitions
(rotation, projection, reflection) into algebraic calculations. The space of
all linear maps from `V` to `W` is itself a vector space!

Mathlib formalizes this through the `LinearMap` type, which bundles a function
with proofs of linearity. We'll explore linear maps more deeply in the next
lesson.

### An Example: A Shear on `Vector2`

Here is a concrete linear map on the rational plane we built above: the
*shear* that slides each vector sideways by an amount equal to its height.

  `(x, y) ↦ (x + y, y)`

The notation `V →ₗ[F] W` is mathlib's for `LinearMap F V W`: the type of
*bundled* linear maps, each one a function packaged together with proofs that
it respects addition and scalar multiplication. So defining one is not just
giving the function, `toFun`; it also means discharging those two obligations,
here called `map_add'` and `map_smul'`.

Both obligations are equations between `Vector2`s, and the way to prove one is
to prove it of the underlying pairs and appeal to injectivity of the wrapper --
which is what `apply Vector2.toPair_injective` does. After that we are back to
ordinary rational arithmetic, and `ring` finishes.
@@@ -/

def shear : Vector2 →ₗ[Rat] Vector2 where
  toFun v := ⟨(v.toPair.1 + v.toPair.2, v.toPair.2)⟩
  map_add' v w := by
    apply Vector2.toPair_injective
    show ((v.toPair.1 + w.toPair.1) + (v.toPair.2 + w.toPair.2), v.toPair.2 + w.toPair.2)
        = (v.toPair.1 + v.toPair.2, v.toPair.2) + (w.toPair.1 + w.toPair.2, w.toPair.2)
    rw [Prod.mk_add_mk]
    congr 1
    ring
  map_smul' s v := by
    apply Vector2.toPair_injective
    show (s * v.toPair.1 + s * v.toPair.2, s * v.toPair.2)
        = s • (v.toPair.1 + v.toPair.2, v.toPair.2)
    rw [Prod.smul_mk]
    congr 1
    simp [smul_eq_mul]
    ring

/- The map in action: the vector (3, 4) slides right by 4. -/
#eval shear (Vector2.ofPair (3, 4))       -- Vector2 (7, 4)

/- @@@
Because the linearity proofs are part of the value, the two laws are not
claims we have to check input by input; they hold for *all* inputs, and we can
ask Lean for them by name. The `#eval`s illustrate; the `example`s prove.
@@@ -/

#eval shear (Vector2.ofPair (1, 2) + Vector2.ofPair (3, 4))     -- Vector2 (10, 6)
#eval shear (Vector2.ofPair (1, 2)) + shear (Vector2.ofPair (3, 4))
                                                                -- Vector2 (10, 6)

#eval shear ((2 : Rat) • Vector2.ofPair (1, 2))                 -- Vector2 (6, 4)
#eval (2 : Rat) • shear (Vector2.ofPair (1, 2))                 -- Vector2 (6, 4)

example (v w : Vector2) : shear (v + w) = shear v + shear w :=
  shear.map_add v w

example (s : Rat) (v : Vector2) : shear (s • v) = s • shear v :=
  shear.map_smul s v

/- @@@
One consequence of linearity worth noticing: every linear map must send `0` to
`0`, since `f 0 = f (0 • 0) = 0 • f 0 = 0`. Mathlib has this as `map_zero`.
@@@ -/

example : shear 0 = 0 := shear.map_zero

/- @@@
That rules out maps you might otherwise call "linear" from school algebra. The
translation `(x, y) ↦ (x + 1, y)` sends `(0, 0)` to `(1, 0)`, so no amount of
cleverness will produce the `map_add'` and `map_smul'` proofs for it: it is
*affine*, not linear, which is exactly the distinction the affine space lesson
was drawing. Lines through the origin are linear; lines in general are not.
@@@ -/

/- @@@
## From Concrete to Abstract

What we've done here is take concrete types (ℚ itself, and our own `Vector2`
and `Vector3` over pairs and triples of rationals) and shown that they're all
instances of an abstract algebraic concept (a module over a field, aka a
vector space). This is the power of abstraction: write a theorem once, and it
applies to infinitely many instances.

For example, suppose we prove:
  `theorem span_of_two_independent_vecs (v w : V) (hind : ¬ LinearDependent (v, w)) :
    Submodule.span ℚ {v, w} = ⊤`

This theorem holds for *any* vector space V over ℚ (or any field). We don't
need to re-prove it for ℚ², ℚ³, spaces of polynomials, or any other instance.
The abstraction pays dividends.

## The Big Picture

Vector spaces are fundamental to modern mathematics and science. They appear in:

- **Linear algebra**: systems of equations, eigenvalues, matrix decompositions
- **Functional analysis**: infinite-dimensional spaces, Hilbert spaces, operators
- **Differential geometry**: tangent spaces, differential forms
- **Quantum mechanics**: state spaces, observables, probability amplitudes
- **Machine learning**: feature spaces, embeddings, neural network architectures
- **Signal processing**: Fourier analysis, wavelets, compression

By formalizing vector spaces, we're equipping ourselves to reason rigorously
about all of these domains. The structure is so universal that understanding
it well pays off across the entire landscape of mathematical and computational
practice.
@@@ -/

end VectorSpaces
