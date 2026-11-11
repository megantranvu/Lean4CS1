```lean
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
```

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
```lean
namespace VectorSpaces
```

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
```lean
/- ℚ is a module over itself... -/
#check (inferInstance : Module Rat Rat)

/- ...and ℚ is a field. Together: ℚ is a vector space over ℚ. -/
#check (inferInstance : Field Rat)

/- Basic operations in the 1D vector space ℚ -/
#eval (2 : Rat) * (3 : Rat)  -- 6 (scalar multiplication)
#eval (1 : Rat) * (5 : Rat)  -- 5 (identity element: 1 • v = v)
#eval (2 : Rat) + (3 : Rat)  -- 5 (vector addition)
```

In a 1-dimensional space, any two vectors are linearly *dependent*: one is a
scalar multiple of the other (or one is zero). This is true for ℚ: any rational
q₁ can be expressed as `c * q₂` for some c, as long as q₂ ≠ 0.
## Naming Our Vector Types

Before the next two instances, a change of representation that matters for
everything that follows. So far the vectors have *been* ℚ, and the obvious
next step would be to let them be ℚ × ℚ. That works, and it is what mathlib's
generic product instance gives us for free -- but it leaves the vectors of the
plane with no name of their own, and `ℚ × ℚ` says nothing about what the pair
is *for*.

So we give them names: `Vector2` and `Vector3`. Lean offers two devices for
"a new name for an existing representation", and choosing between them is a
real design decision rather than a formality.

### `def` or `structure`?

A **`structure`** with one field makes a genuinely *new* type. `Vector2` and
`ℚ × ℚ` become unrelated, and so do two structures over the same
representation. That is exactly what the torsors and affine space lessons
need: `Point2` and `Vector2` are both pairs of rationals there, and the whole
point is that `p + q` for two points must not typecheck.

A **`def`** makes an *abbreviation that instance search will not see through*.
`Vector2` is still definitionally `ℚ × ℚ`, so values pass back and forth
freely, but Lean will not automatically apply a `ℚ × ℚ` instance to it.

The cost of `structure` is that mathlib's `Module ℚ (ℚ × ℚ)` instance genuinely
does not apply to it -- a different type needs its own instance -- so the
structure must be *transported* across the wrapper: define every operation,
then invoke mathlib's transport lemmas (`Function.Injective.addCommGroup` and
`Function.Injective.module`, which take an injection into a known module and
hand back the structure on the source). That is around twenty lines per type.

The cost of `def` is that it buys no type safety at all. With
`def Vector2 := ℚ × ℚ` and `def Point2 := ℚ × ℚ`, a `Point2` is accepted
wherever a `Vector2` is expected, silently -- the two are the same type wearing
different names.

**This lesson has no points.** Its subject is vectors, there is no second role
to confuse them with, and nothing here needs `p + q` to fail. So we take the
cheap device and spend three lines instead of twenty:

  `def Vector2 := ℚ × ℚ` plus two `inferInstanceAs` lines

and mathlib's product instance carries straight across by definitional
equality. Where a second role *does* exist -- `Point2` against `Vector2` in
the affine lessons -- `def` is not an option and `structure` is worth its
twenty lines.

The principle is worth naming, because it recurs: **reach for the weakest
device that does the job.** A new type is a strong tool. It buys real
guarantees and it costs real work, so spend it where there is a confusion to
prevent, not by reflex.

## Instance 2: `Vector2`, the Rational Plane

The canonical 2-dimensional vector space over ℚ: the type, and the two
instances pulled across from `ℚ × ℚ`.
```lean
def Vector2 := Rat × Rat

instance : AddCommGroup Vector2 := inferInstanceAs (AddCommGroup (Rat × Rat))
instance : Module Rat Vector2   := inferInstanceAs (Module Rat (Rat × Rat))
```

`inferInstanceAs T` means "run instance search for `T`, and accept the result
here." The two types involved are definitionally equal, so the instance found
for `ℚ × ℚ` *is* an instance for `Vector2`; all `inferInstanceAs` does is
tell Lean where to look, since it will not unfold a `def` on its own while
searching.

Note what is absent: no operation definitions, no transport lemmas, no proofs.
Not one module axiom is restated, because the instance is mathlib's, unchanged.

Watch the output of the `#eval`s below, though, because it reports on the
bargain honestly. There is no `Vector2` tag on the results, and there cannot
be: asking Lean `#check ((2, 3) : Vector2) + ((1, -1) : Vector2)` gets the
answer `ℚ × ℚ`. The ascription is consumed during elaboration and the name
does not survive it. `Vector2` is a label for the reader and a signpost for
instance search; it is not a thing Lean carries around. Contrast the affine
space lesson, where `#eval` prints `Vector2 (3, 0)` because there the name
belongs to a real type with a real constructor.
```lean
#check (inferInstance : Module Rat Vector2)

#eval ((2, 3) : Vector2) + ((1, -1) : Vector2)
      -- (3, 2) -- componentwise addition; note: no `Vector2` tag

#eval (1/2 : Rat) • ((2, 3) : Vector2)
      -- (1, 3 / 2) -- scalar multiplication
```

Compare this with the affine space lesson, which hand-wrote componentwise
arithmetic and proved each law. Here we wrote no operations and no proofs at
all. The rational plane is our first "true" vector space: it has dimension 2,
and linear combinations of two independent vectors (say `(1, 0)` and `(0, 1)`)
span all of it.

One caveat for later, when you write proofs about these types. Tactics do not
see through a `def` any more than instance search does, so a `simp` aimed at a
goal stated at `Vector2` reports no progress and needs the goal restated at
`ℚ × ℚ` first. Term-mode proofs are unaffected -- the elaborator unfolds
definitions freely when checking a term against its type -- which is one
reason the proofs in this file are terms.
## Instance 3: `Vector3`, 3D Rational Space

The pattern extends to three dimensions without a new idea -- which is the
point of showing it. The representation is `ℚ × ℚ × ℚ`, mathlib's product
instances make that a module over ℚ, and the same two lines carry the
structure across.
```lean
def Vector3 := Rat × Rat × Rat

instance : AddCommGroup Vector3 := inferInstanceAs (AddCommGroup (Rat × Rat × Rat))
instance : Module Rat Vector3   := inferInstanceAs (Module Rat (Rat × Rat × Rat))

#eval ((1, 2, 3) : Vector3) + ((1, 1, 1) : Vector3)
      -- (2, 3, 4) -- componentwise addition

#eval (1/2 : Rat) • ((2, 4, 6) : Vector3)
      -- (1, 2, 3) -- scalar multiplication
```

In 3D space, three linearly independent vectors (such as the standard basis
`(1, 0, 0)`, `(0, 1, 0)`, `(0, 0, 1)`) span the whole space. This is the
geometric foundation of 3D computer graphics, physics simulations, and much of
applied mathematics.

Note what the types do and do not prevent here. Adding a 2D vector to a 3D one
is a type error, because `ℚ × ℚ` and `ℚ × ℚ × ℚ` are different types and our
two names inherit that difference. But `Vector2` *is* `ℚ × ℚ`, so nothing
stops a bare pair being used as a `Vector2`. That is the bargain we struck
above: separation between the dimensions, none between a vector and its
representation -- indeed, as the `#check` above showed, not even a name that
survives elaboration. In this lesson nothing needs the second kind, and the affine
lessons, which do, pay for it with a `structure`.
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
`inferInstanceAs` lines above did. Naming our vector types cost us nothing at
all here, because we chose the naming device that keeps the instances.
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

Each obligation is an equation between pairs, so `Prod.ext` reduces it to one
equation per component. `map_add'` needs
`(v₁ + w₁) + (v₂ + w₂) = (v₁ + v₂) + (w₁ + w₂)`, which is mathlib's
`add_add_add_comm`; its second component is `rfl`. `map_smul'` needs
`s * v₁ + s * v₂ = s * (v₁ + v₂)`, which is `mul_add` read backwards.

A remark on the `def` choice above, since this is where you would expect to
pay for it. Tactics decline to unfold a `def`: a `simp` aimed at these goals
reports making no progress, and would need the goal restated at `ℚ × ℚ` with
`show` first. Term-mode proofs have no such trouble, because the *elaborator*
does unfold definitions when it checks that a term has the required type. The
bill arrives only if you reach for tactics.
```lean
def shear : Vector2 →ₗ[Rat] Vector2 where
  toFun v := ((v.1 + v.2, v.2) : Rat × Rat)
  map_add' _ _  := Prod.ext (add_add_add_comm _ _ _ _) rfl
  map_smul' s v := Prod.ext (mul_add s v.1 v.2).symm rfl

/- The map in action: the vector (3, 4) slides right by 4. -/
#eval shear ((3, 4) : Vector2)                                 -- (7, 4)
```

Because the linearity proofs are part of the value, the two laws are not
claims we have to check input by input; they hold for *all* inputs, and we can
ask Lean for them by name. The `#eval`s illustrate; the `example`s prove.
```lean
#eval shear (((1, 2) : Vector2) + ((3, 4) : Vector2))          -- (10, 6)
#eval shear ((1, 2) : Vector2) + shear ((3, 4) : Vector2)      -- (10, 6)

#eval shear ((2 : Rat) • ((1, 2) : Vector2))                   -- (6, 4)
#eval (2 : Rat) • shear ((1, 2) : Vector2)                     -- (6, 4)

example (v w : Vector2) : shear (v + w) = shear v + shear w :=
  shear.map_add v w

example (s : Rat) (v : Vector2) : shear (s • v) = s • shear v :=
  shear.map_smul s v
```

One consequence of linearity worth noticing: every linear map must send `0` to
`0`, since `f 0 = f (0 • 0) = 0 • f 0 = 0`. Mathlib has this as `map_zero`.
```lean
example : shear 0 = 0 := shear.map_zero
```

That rules out maps you might otherwise call "linear" from school algebra. The
translation `(x, y) ↦ (x + 1, y)` sends `(0, 0)` to `(1, 0)`, so no amount of
cleverness will produce the `map_add'` and `map_smul'` proofs for it: it is
*affine*, not linear, which is exactly the distinction the affine space lesson
was drawing. Lines through the origin are linear; lines in general are not.
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
```lean
end VectorSpaces
```


<div class="issue-box">📝 <a href="https://github.com/kevinsullivan/Lean4CS1/issues/new">Report an issue</a> with this section</div>

