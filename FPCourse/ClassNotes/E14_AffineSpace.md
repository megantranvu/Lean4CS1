# Affine Spaces: Geometry Without an Origin

## Overview

An **affine space** is a set of points equipped with a notion of "displacement" via vectors from an underlying vector space (or group). The critical feature: **points and vectors are distinct types**. Unlike a vector space, an affine space has *no distinguished origin* — all points are equivalent, and geometry emerges purely from the relationships between them.

The key insight: an affine space is *more honest* about the structure of geometry than a vector space. It enforces a type distinction that matches physical reality:
- **Points** are locations (you cannot add two locations)
- **Vectors** are displacements (you can compose displacements)

While a vector space conflates these into a single type for computational convenience, an affine space preserves the conceptual distinction — making certain errors *impossible at the type level*.

### Core Structure

An affine space `(V, P)` consists of:
- **Vector group `V`**: an algebraic group whose elements represent displacements
- **Point set `P`**: locations in space (with no inherent ordering or special points)
- **Translation operation `+ᵥ : V → P → P`**: given vector `v` and point `p`, compute the point `p` moved by displacement `v`
- **Subtraction operation `-ᵥ : P → P → V`**: given two points, compute the unique vector relating them

## Operators and Notation

| Operator | Notation | Type | Meaning |
|----------|----------|------|---------|
| Vector addition | `v + w` | `V → V → V` | Compose two displacements |
| Vector identity | `0` | `V` | The "no displacement" vector |
| Vector negation | `-v` | `V → V` | Reverse a displacement |
| Point translation | `v +ᵥ p` | `V → P → P` | Move point `p` by vector `v` |
| Vector subtraction | `q -ᵥ p` | `P → P → V` | The displacement from `p` to `q` |

## Laws and Identities

An affine space must satisfy five axioms:

### 1. **Translation Associativity**
```
v +ᵥ (w +ᵥ p) = (v + w) +ᵥ p
```
Composing two translations is the same as translating by the sum of the vectors.

### 2. **Identity Translation**
```
0 +ᵥ p = p
```
Translating by the zero vector (no displacement) leaves the point unchanged.

### 3. **Subtraction-Translation Inverse I** (Reconstruction)
```
(q -ᵥ p) +ᵥ p = q
```
The vector from `p` to `q`, when applied to `p`, recovers `q`.

### 4. **Subtraction-Translation Inverse II** (Recovery)
```
(v +ᵥ p) -ᵥ p = v
```
The difference between a translated point and the original is the translation vector.

### 5. **Vector Group Laws** (inherited)
- Vector addition is associative
- Vector addition is commutative (for points in ℚⁿ)
- Every vector has an inverse

## Concrete Instances: Affine Spaces Over ℚⁿ

### Affine 1D: `ℚ` as an Affine Space

The rational numbers form an affine space over themselves.

**Points and vectors:** Both are elements of ℚ
**Translation:** `v +ᵥ p = p + v` (ordinary addition)
**Subtraction:** `q -ᵥ p = q - p` (ordinary subtraction)

**Example:**
- Points: 2, 5, -3.5, 100
- Vector: 3
- Translation: `3 +ᵥ 2 = 5`
- Difference: `5 -ᵥ 2 = 3`

**New capability:** We can describe "locations on a line" without privileging any point as special. Three points at 0, 1, 3 don't form a triangle (they're collinear), but their geometric relationships are captured: the distance from 0 to 1 is 1, from 1 to 3 is 2.

---

### Affine 2D: `ℚ × ℚ` as an Affine Space Over `ℚ × ℚ`

The rational plane forms an affine space over itself.

**Points:** Pairs `(p₁, p₂)` representing locations
**Vectors:** Pairs `(v₁, v₂)` representing displacements
**Translation:** `(v₁, v₂) +ᵥ (p₁, p₂) = (p₁ + v₁, p₂ + v₂)` (componentwise)
**Subtraction:** `(q₁, q₂) -ᵥ (p₁, p₂) = (q₁ - p₁, q₂ - p₂)` (componentwise)

**Example:**
- Points: `(0, 0)`, `(1, 0)`, `(1, 1)` (vertices of a right angle)
- Vector: `(2, 1)` (displacement: 2 right, 1 up)
- Translation: `(2, 1) +ᵥ (0, 0) = (2, 1)`
- Difference: `(1, 1) -ᵥ (0, 0) = (1, 1)`

**New capability:** We can describe geometric figures (points, lines, triangles, polygons) purely in terms of relative positions. No point is "the origin" — the plane is homogeneous. If we translate all vertices of a triangle by the same vector, we get a congruent triangle. The relationship structure is preserved.

---

### Affine 3D: `ℚ × ℚ × ℚ` as an Affine Space Over `ℚ × ℚ × ℚ`

The rational 3D space forms an affine space over itself.

**Points:** Triples `(p₁, p₂, p₃)` representing locations in 3D space
**Vectors:** Triples `(v₁, v₂, v₃)` representing displacements
**Translation:** `(v₁, v₂, v₃) +ᵥ (p₁, p₂, p₃) = (p₁ + v₁, p₂ + v₂, p₃ + v₃)` (componentwise)
**Subtraction:** `(q₁, q₂, q₃) -ᵥ (p₁, p₂, p₃) = (q₁ - p₁, q₂ - p₂, q₃ - p₃)` (componentwise)

**Example:**
- Points: `(0, 0, 0)`, `(1, 0, 0)`, `(0, 1, 0)`, `(0, 0, 1)` (unit cube corners)
- Vector: `(1, 1, 1)` (displacement: 1 unit along each axis)
- Translation: `(1, 1, 1) +ᵥ (0, 0, 0) = (1, 1, 1)`
- Difference: `(1, 0, 0) -ᵥ (0, 0, 0) = (1, 0, 0)` (unit vector along x-axis)

**New capability:** We can model 3D geometry without a privileged coordinate system. Objects in space are described by their relative positions. This is essential for:
- Computer graphics (object transformations)
- Physics simulations (positions in space)
- Robotics (end-effector positions)

## The Conceptual Advantage: Type Safety for Geometry

Affine spaces have a crucial advantage over vector spaces: **the type system enforces correct geometric thinking**.

In an affine space formalism:
- You **cannot** accidentally add two points (type error)
- You **must** be explicit about which vector you're using to translate
- You **cannot** confuse a location with a displacement
- The formalism itself prevents nonsensical operations

By contrast, in vector space formalism (used throughout classical physics), points and vectors collapse into a single type. This means:
- Code/proofs are less type-safe
- You can perform meaningless operations (add two positions)
- The distinction relies on *human intention*, not mathematical structure
- Errors are caught by physical intuition, not by the formalism

**Historical note:** Classical physics adopted vector spaces as its foundation because they were computationally convenient and adequate for describing phenomena around a fixed reference frame. But this choice obscured the conceptual structure. A more honest foundation would separate points (events/locations) from vectors (displacements/forces), preserving the type distinction throughout.

---

## Why This Abstraction Matters

### 1. **No Special Point (Conceptual Honesty)**

In a vector space like ℚⁿ, the zero vector `0 = (0, ..., 0)` is both an algebraic identity and a geometric origin. This is artificial when modeling space — why should the origin be special? Affine spaces capture the intuition that *space is homogeneous*: all locations are equivalent until we choose a coordinate system.

### 2. **Separates Algebra from Geometry**

- **Vectors (V)** handle the algebra: how displacements compose, what the inverse of a displacement is
- **Points (P)** handle the geometry: locations that have no inherent operations (you can't "add" two locations meaningfully, but you can measure the gap between them)

### 3. **Automatic Invariance**

Any construction in an affine space automatically respects translation invariance: if we translate all points by the same vector, all geometric properties are preserved. This is crucial for defining things like "perpendicularity" or "distance" in a coordinate-free way.

### 4. **Generalization of Coordinate Systems**

Given an affine space `(V, P)` and any choice of *origin* point `o ∈ P`, we can recover a vector space structure on `P` by mapping each point `p` to its displacement from `o`: `p ↦ p -ᵥ o`. Different choices of origin give different (but isomorphic) vector spaces. This shows that vector spaces are really affine spaces *with a chosen origin*.

## Connected Concepts

### Affine Transformations

A function `f : P → P'` between affine spaces is *affine* if it preserves the affine structure:
```
f (v +ᵥ p) = v +ᵥ f(p)
```
(up to appropriate translations on the vector spaces)

Examples:
- Translation: `p ↦ p +ᵥ v₀` for fixed `v₀`
- Rotation about a point
- Scaling from a point

All affine transformations preserve the relative geometry of points.

### Affine Subspaces

Given an affine space `(V, P)` and a subgroup `W ⊆ V` and a point `p₀ ∈ P`, the *affine subspace* through `p₀` in direction `W` is:
```
{p₀ +ᵥ v : v ∈ W}
```

Examples:
- In ℚ²: lines and points
- In ℚ³: planes, lines, and points

These capture geometric substructures while preserving the absence of a canonical origin.

## Affine Spaces in the Lean Formalization

The `AffineSpace` typeclass in E14_AffineSpace.lean enforces the type distinction:

```lean
class AffineSpace (V : Type) (P : Type) where
  vadd : V → P → P      -- vectors act on points
  vsub : P → P → V      -- subtract points to get a vector
  -- (P is separate from V; they're distinct types)
```

**What this buys you:**
- Lean's type checker prevents `vadd p q` (doesn't type-check; p is not a vector)
- You cannot accidentally write `p + p` (addition not defined on points)
- The distinction between points and vectors is *enforced by the compiler*

Contrast this with the vector space formalization in E14_VectorSpace.lean:

```lean
class VectorSpace (F V : Type) ... where
  smul : F → V → V    -- scalars act on vectors
  -- (everything is a V; no separate point type)
```

Here, `V + V` is always meaningful—there's no type safety preventing you from treating a point as a vector inappropriately.

**Why Lean makes this distinction matter:** When you formalize mathematics in a dependently-typed language, the type system becomes a tool for expressing *what you mean*, not just *what you compute*. Affine spaces force you to be explicit. Vector spaces trade that clarity for convenience.

---

## Summary: Key Takeaways

| Aspect | Vector Space | Affine Space |
|--------|--------------|--------------|
| **Types** | One type: everything is a vector | Two types: points distinct from vectors |
| **Elements** | Displacements from an implicit origin | Locations with no special point |
| **Structure** | Group with scalar multiplication | Group acts transitively and freely on point set |
| **"Zero"** | Special element: `0` | No distinguished point |
| **Addition** | `v + w` makes sense | `p + q` does *not* make sense (type error) |
| **Subtraction** | `v - w` makes sense | `q - p` makes sense (gives a vector) |
| **Translation** | Not applicable | `v +ᵥ p` is the fundamental operation |
| **Type Safety** | Weaker (relies on programmer discipline) | Stronger (formalism prevents errors) |
| **Computational** | More convenient | Requires explicit reasoning about displacements |

**Conclusion:** An affine space is the natural, conceptually honest abstraction for modeling pure geometry. It preserves the type distinction between locations and displacements—a distinction that classical physics obscured by adopting vector spaces as its foundation. In a formal setting (like Lean), this distinction becomes a feature, not a limitation: the type system helps us write correct geometric code.
