# Vector Spaces: Modules Over a Field

## Overview

A **vector space** is an algebraic structure that captures the essence of *linear combinations*: we can add elements together and scale them by numbers from a field (like ℚ or ℝ), and these operations behave in a predictable, composable way.

Formally, a vector space `V` over a field `F` is:
- A single set of elements (all treated uniformly as "vectors")
- An abelian group under addition (with identity `0`)
- A scalar multiplication operation that respects both field and vector structure
- Laws ensuring closure, associativity, distributivity, and other linear properties

Vector spaces are the lingua franca of classical physics and linear algebra. However, this universality comes at a conceptual cost: they conflate two fundamentally different geometric objects—**points** (locations) and **vectors** (displacements)—into a single type.

This is a pragmatic trade-off: we gain computational convenience and algebraic closure, but we lose conceptual clarity. The more honest geometric foundation is the **affine space** (see E14_AffineSpace.md), which preserves the type distinction.

### How Vector Spaces Differ From Affine Spaces

This is the critical distinction:

| Aspect | Affine Space | Vector Space |
|--------|--------------|--------------|
| **Points vs. Vectors** | Points are *different* from vectors. Points have no operations. | Everything is a vector. Points, displacements, and scalings all belong to the same set. |
| **Can you add points?** | **No.** Adding two locations makes no sense. | **Yes.** `v + w` is always meaningful. |
| **Zero element** | No distinguished point; `0` only exists as a vector. | **The zero vector `0` is a point.** It's both an algebraic identity and a geometric location. |
| **Closure of addition** | Not applicable to points. Only vectors add: `v₁ + v₂ ∈ V`. | Points add to points: `v + w ∈ V`. |
| **How it arises** | Pure geometry: space without coordinates. | Geometry with a *chosen origin*. |
| **Relationship** | Fundamental; affine spaces are more general. | A vector space is an affine space with an arbitrary choice of origin. |

**Key insight:** Every vector space can be viewed as an affine space by "forgetting" that `0` is special. Conversely, every affine space becomes a vector space once you *choose* a point to call the origin.

**The transformation:** Given an affine space `(V, P)` and a choice of origin `o ∈ P`, we define a vector space structure on `P` by:
```
v ⊕ p := v +ᵥ p    (translate p by vector v)
p ⊕ q := (q -ᵥ o) + ((p -ᵥ o))    (add displacements from origin)
```
Now `P` has all vector space operations, but this structure *depends on the choice of o*. Different origins give different (but isomorphic) vector space structures.

---

### Core Structure

A vector space `V` over field `F` consists of:
- **Field F**: numbers we use as scalars (ℚ in our examples)
- **Vector set V**: elements we add and scale (all are treated uniformly; there's no separate "point" type)
- **Addition `+`**: `V → V → V`, combining two vectors
- **Scalar multiplication `•`**: `F → V → V`, scaling a vector
- **Identity elements**: `0 ∈ V` (additive identity, the origin), `1 ∈ F` (multiplicative identity)
- **Negation**: each vector `v` has an inverse `-v`

## Operators and Notation

| Operator | Notation | Type | Meaning |
|----------|----------|------|---------|
| Vector addition | `v + w` | `V → V → V` | Combine two vectors |
| Vector scaling | `s • v` | `F → V → V` | Scale vector `v` by scalar `s` |
| Additive identity | `0` | `V` | Zero vector |
| Multiplicative identity | `1` | `F` | The field's multiplicative identity |
| Negation | `-v` | `V → V` | Additive inverse of `v` |
| Field multiplication | `s * t` | `F → F → F` | Multiply two scalars |
| Field addition | `s + t` | `F → F → F` | Add two scalars |

## Laws and Identities

A vector space must satisfy eight axioms (four from the additive group, four from scalar multiplication):

### Additive Group Axioms

#### 1. **Closure of Addition**
```
∀ v w : V, v + w : V
```
Adding two vectors produces another vector.

#### 2. **Associativity of Addition**
```
∀ u v w : V, (u + v) + w = u + (v + w)
```
Order of grouping doesn't matter when adding three or more vectors.

#### 3. **Commutativity of Addition**
```
∀ v w : V, v + w = w + v
```
Order doesn't matter when adding vectors.

#### 4. **Additive Identity**
```
∀ v : V, 0 + v = v = v + 0
```
The zero vector is an additive identity.

#### 5. **Additive Inverses**
```
∀ v : V, ∃ (-v) : V, v + (-v) = 0
```
Every vector has an additive inverse.

### Scalar Multiplication Axioms

#### 6. **Multiplicative Identity**
```
∀ v : V, 1 • v = v
```
Scaling by the field's multiplicative identity doesn't change the vector.

#### 7. **Compatibility of Scalar Multiplication**
```
∀ s t : F, ∀ v : V, (s * t) • v = s • (t • v)
```
Scaling by the product of two scalars equals composing two scalings.

#### 8a. **Left Distributivity**
```
∀ s t : F, ∀ v : V, (s + t) • v = s • v + t • v
```
Scaling by a sum of scalars distributes over addition.

#### 8b. **Right Distributivity**
```
∀ s : F, ∀ v w : V, s • (v + w) = s • v + s • w
```
Scaling a sum of vectors distributes over both summands.

## Concrete Instances: Vector Spaces Over ℚ

### 1D Vector Space: ℚ

The rational numbers form a 1-dimensional vector space over themselves.

**Underlying affine space:** The affine line (ℚ, ℚ) with translation `v +ᵥ p = p + v`.

**Origin chosen:** `0 ∈ ℚ`

**Vectors:** Rational numbers ℚ
**Scalars:** Rational numbers ℚ
**Addition:** `q₁ + q₂` (ordinary addition, derived from affine translation)
**Scalar multiplication:** `s • q = s * q` (ordinary multiplication, scaling a displacement)
**Zero element:** `0` (the chosen origin point)
**Identity scalar:** `1`

**Example:**
```
2 • (1/3) = 2/3    (scale displacement 1/3 by factor 2)
(1/2) • 5 = 5/2    (scale displacement 5 by factor 1/2)
(2 + 3) • 4 = 2•4 + 3•4 = 8 + 12 = 20    (distributivity)
```

**Dimension:** 1 (any non-zero rational is a basis)

---

### 2D Vector Space: ℚ²

Pairs of rationals form a 2-dimensional vector space over ℚ.

**Underlying affine space:** The affine plane (ℚ², ℚ²) with translation `(v₁, v₂) +ᵥ (p₁, p₂) = (p₁ + v₁, p₂ + v₂)`.

**Origin chosen:** `(0, 0) ∈ ℚ²`

**Vectors:** Pairs `(v₁, v₂)` with `v₁, v₂ ∈ ℚ` (displacements from origin, but also treated as points)
**Scalars:** Rational numbers ℚ
**Addition:** `(v₁, v₂) + (w₁, w₂) = (v₁ + w₁, v₂ + w₂)` (componentwise; derived from affine translation)
**Scalar multiplication:** `s • (v₁, v₂) = (s * v₁, s * v₂)` (componentwise; scaling displacements)
**Zero element:** `(0, 0)` (the chosen origin)
**Identity scalar:** `1`

**Example:**
```
(1, 2) + (3, -1) = (4, 1)    [add displacements]
2 • (1/2, 3) = (1, 6)         [scale displacement by 2]
3 • ((2, 1) + (1, -1)) = 3 • (3, 0) = (9, 0)
              = 3•(2, 1) + 3•(1, -1) = (6, 3) + (3, -3) = (9, 0)  ✓
```

**Basis:** `{(1, 0), (0, 1)}` (standard basis)

**Dimension:** 2 (any two linearly independent vectors form a basis)

**Geometric interpretation:** The Cartesian plane with the origin *privileged as the zero point*. Vectors represent displacements and also locations. The vector `(3, 2)` means "3 units right, 2 units up" from the origin.

**Comparison to affine ℚ²:** The affine plane treats all points equally (no origin). Here, `(0, 0)` is special and acts as the identity for addition. We've *gained* the ability to add points (`p + q`), but *lost* the symmetry of treating all locations as equivalent.

---

### 3D Vector Space: ℚ³

Triples of rationals form a 3-dimensional vector space over ℚ.

**Underlying affine space:** The affine 3D space (ℚ³, ℚ³) with translation `(v₁, v₂, v₃) +ᵥ (p₁, p₂, p₃) = (p₁ + v₁, p₂ + v₂, p₃ + v₃)`.

**Origin chosen:** `(0, 0, 0) ∈ ℚ³`

**Vectors:** Triples `(v₁, v₂, v₃)` with `vᵢ ∈ ℚ` (displacements from origin, also treated as points)
**Scalars:** Rational numbers ℚ
**Addition:** `(v₁, v₂, v₃) + (w₁, w₂, w₃) = (v₁ + w₁, v₂ + w₂, v₃ + w₃)` (componentwise)
**Scalar multiplication:** `s • (v₁, v₂, v₃) = (s * v₁, s * v₂, s * v₃)` (componentwise)
**Zero element:** `(0, 0, 0)` (the chosen origin)
**Identity scalar:** `1`

**Example:**
```
(1, 0, 1) + (0, 1, 0) = (1, 1, 1)    [add displacements]
(1/2) • (2, 4, 6) = (1, 2, 3)        [scale displacements]
2 • ((1, 1, 0) + (0, 1, 1)) = 2 • (1, 2, 1) = (2, 4, 2)
```

**Basis:** `{(1, 0, 0), (0, 1, 0), (0, 0, 1)}` (standard basis)

**Dimension:** 3 (any three linearly independent vectors form a basis)

**Geometric interpretation:** 3D Euclidean space with the origin at `(0, 0, 0)`. We can now perform algebraic operations on points. Used in:
- Computer graphics (vertex positions, camera orientations)
- Physics (forces, accelerations, velocities relative to a frame)
- Engineering (displacements, stresses relative to a reference point)

**Comparison to affine ℚ³:** The affine 3D space treats all locations as equivalent. Here, `(0, 0, 0)` is the privileged zero point. This is convenient for physics (where we often choose a fixed reference frame) and computation, but less symmetric geometrically.

---

## Derived Concepts and Capabilities

### Linear Combinations

Any vector in a vector space can be written as a linear combination of basis vectors:
```
v = c₁ • v₁ + c₂ • v₂ + ... + cₙ • vₙ
```

In ℚ²:
```
(5, 3) = 5 • (1, 0) + 3 • (0, 1)
```

### Span and Subspaces

The **span** of a set of vectors is the set of all linear combinations:
```
span(S) = {c₁ • v₁ + ... + cₙ • vₙ : vᵢ ∈ S, cᵢ ∈ F}
```

Any span is itself a vector space (a **subspace**).

**Example in ℚ³:** The set of vectors on the xy-plane:
```
span((1,0,0), (0,1,0)) = {(a, b, 0) : a, b ∈ ℚ}
```
This is a 2D subspace of the 3D space.

### Linear Independence

Vectors `v₁, ..., vₙ` are **linearly independent** if:
```
c₁ • v₁ + ... + cₙ • vₙ = 0  ⟹  c₁ = ... = cₙ = 0
```

In ℚ²:
- `(1, 0)` and `(0, 1)` are linearly independent
- `(1, 0)` and `(2, 0)` are linearly *dependent* (the second is 2× the first)

### Basis and Dimension

A **basis** of a vector space is a minimal spanning set (linearly independent vectors whose span is the whole space).

Every vector has a *unique* representation in terms of any basis.

**Dimension** = size of any basis.

| Space | Dimension | Basis |
|-------|-----------|-------|
| ℚ | 1 | `{1}` |
| ℚ² | 2 | `{(1,0), (0,1)}` |
| ℚ³ | 3 | `{(1,0,0), (0,1,0), (0,0,1)}` |

### Linear Maps

A function `f : V → W` between vector spaces is **linear** if:
```
f(v₁ + v₂) = f(v₁) + f(v₂)           (additivity)
f(s • v) = s • f(v)                   (homogeneity)
```

**Examples:**
- Scaling: `f(v) = 2 • v`
- Projection to first component: `f(v₁, v₂) = (v₁, 0)`
- Rotation by angle θ in ℚ²

Linear maps preserve the vector space structure and let us translate geometric intuitions (like rotation or reflection) into algebraic calculations.

### Kernel and Image

For a linear map `f : V → W`:
- **Kernel:** `ker(f) = {v ∈ V : f(v) = 0}` (always a subspace of V)
- **Image:** `im(f) = {f(v) : v ∈ V}` (always a subspace of W)

**Rank-Nullity Theorem:**
```
dim(V) = dim(ker(f)) + dim(im(f))
```

This relates the "loss of information" (kernel) to the "effective output dimension" (image).

## From Affine Space to Vector Space: The Role of Choosing an Origin

The relationship between affine and vector spaces is *not* that vector spaces are more general. Rather, **a vector space is a special case of an affine space where we've chosen a distinguished origin.**

### The Construction

Given an affine space `(V, P)` where:
- `V` is a group (vectors with addition and negation)
- `P` is a set of points
- `+ᵥ : V → P → P` is the translation operation
- `-ᵥ : P → P → V` is the subtraction operation

We can construct a vector space on the *same point set* `P` by choosing any point `o ∈ P` as the origin. Define:

**Vector addition on points:**
```
p ⊕ q = (q -ᵥ o) +ᵥ (p -ᵥ o) +ᵥ o
     = o +ᵥ ((q -ᵥ o) + (p -ᵥ o))    [using associativity]
```
(Add the displacements of p and q from the origin, then apply to origin)

**Scalar multiplication on points:**
```
s • p = s • (p -ᵥ o) +ᵥ o
```
(Scale the displacement from origin, then translate back)

**Zero element (the origin):**
```
0 := o
```

With these definitions, `P` becomes a vector space over `F`.

### Concrete Example: Affine ℚ² → Vector ℚ²

**Starting with the affine space:** Points and displacement vectors are both pairs of rationals, with translation `v +ᵥ p = (p₁ + v₁, p₂ + v₂)`.

**Choose origin:** `o = (0, 0)`

**Vector addition becomes:**
```
(a, b) ⊕ (c, d) = ((c,d) - (0,0)) + ((a,b) - (0,0)) + (0,0)
                = (c, d) + (a, b) + (0, 0)
                = (a+c, b+d)    ← ordinary vector addition!
```

**Scalar multiplication becomes:**
```
s • (a, b) = s • ((a,b) - (0,0)) + (0,0)
           = s • (a, b)
           = (s*a, s*b)    ← ordinary scalar multiplication!
```

So by choosing the origin `(0, 0)`, the affine structure automatically recovers the standard vector space operations.

### What Changes With a Different Origin?

Now choose origin `o' = (1, 1)`:

**Vector addition becomes:**
```
(a, b) ⊕' (c, d) = ((c,d) - (1,1)) + ((a,b) - (1,1)) + (1,1)
                  = (c-1, d-1) + (a-1, b-1) + (1,1)
                  = (a+c-1, b+d-1)    ← different from ordinary addition!
```

The point `(1, 1)` now acts like the zero vector in this new system:
```
(1, 1) ⊕' (a, b) = ((a,b) - (1,1)) + ((1,1) - (1,1)) + (1,1)
                  = (a-1, b-1) + (0,0) + (1,1)
                  = (a, b)    ✓
```

The vector space structure *is the same algebraically*, but coordinates are shifted.

### The Key Insight

- **In an affine space:** All points are equivalent; there's no "zero." We describe geometry through relative displacements.
- **In a vector space:** We've chosen one point to be the origin/zero element. Now points *are* vectors, and we can add them.

**Affine ℚⁿ is more general** (fewer assumptions), but **vector ℚⁿ is more convenient** (we can add points, apply algebraic operations directly).

### Why Both Matter

**Use affine spaces when:**
- The geometry is inherently *coordinatefree* (e.g., describing transformations that work regardless of origin)
- You want to emphasize *pure geometry* without algebra
- You're modeling "locations" without a privileged reference point

**Use vector spaces when:**
- You have a natural choice of origin (e.g., physics with a fixed reference frame)
- You want to perform algebraic operations (solving equations, linear combinations)
- You're doing computational linear algebra (matrices, eigenvectors, etc.)

---

## The Trade-Off: Convenience vs. Conceptual Clarity

Vector spaces are *convenient* but they hide conceptual structure. Here's what we trade away by adopting them instead of affine spaces:

### What We Lose

**1. Type Safety**
- In affine spaces, `p + q` (adding two points) is a *type error*
- In vector spaces, `p + q` is always meaningful—you can accidentally add positions
- Errors rely on human intuition ("that doesn't make physical sense") rather than the formalism

**2. The Explicit Origin**
- In affine spaces, the origin is a *choice* you make when constructing coordinates
- In vector spaces, the origin (the zero vector `0`) is *built-in and implicit*
- You can lose track of what `0` means: is it a location or just the identity?

**3. Coordinate-Freeness**
- Affine spaces are naturally coordinate-free; geometry is described without choosing axes
- Vector spaces are coordinate-hungry; you need to choose an origin and basis to do anything
- We hide the "choice of coordinates" in the formalism itself

**4. Scalability to Curved Spaces**
- Affine geometry generalizes beautifully to curved manifolds (differential geometry)
- Vector space formalism breaks down on curved spaces; you need *local* vector spaces at each point
- The loss of clarity becomes acute: you're forced to introduce tangent spaces and re-explain what vectors mean

### What We Gain

**1. Algebraic Closure**
- `v + w` always makes sense, always gives another vector
- `s • v` always makes sense
- You can perform arbitrary linear combinations without restriction

**2. Computational Convenience**
- Everything is just a tuple of numbers
- Linear algebra algorithms (Gaussian elimination, eigenvalues, matrix operations) work directly
- Computer code is simpler and faster

**3. Simplicity for Computation**
- One type instead of two simplifies implementation
- Matrix representations are natural
- Composition of linear maps is just matrix multiplication

### Why Physics Made This Choice

Classical physics adopted vector spaces as its foundation in the 19th century because:
1. **Computation was hard.** Affine geometry with explicit origin choices is verbose.
2. **Fixed reference frames were standard.** In classical mechanics, there's always a chosen lab frame, so an implicit origin wasn't problematic.
3. **It works.** For phenomena near a fixed origin, vector spaces are adequate.

But this choice obscured the distinction between locations and displacements, making it harder to teach why they're different and harder to generalize beyond fixed reference frames (as relativity would later require).

---

## Why This Abstraction Matters

### 1. **Universality (at a Cost)**

Vector spaces appear everywhere:
- **Linear equations:** Solutions to `Ax = b` form a vector space
- **Polynomials:** The space of polynomials of degree ≤ n
- **Functions:** The space of all continuous functions ℝ → ℝ
- **Matrices:** m × n matrices form a vector space
- **Quantum mechanics:** State spaces are complex vector spaces
- **Machine learning:** Feature spaces, embeddings, neural network activations

Write one theorem about vector spaces, and it applies to all of these.

### 2. **Computational Power**

Linear algebra gives us tools:
- **Solving systems:** Gaussian elimination, matrix factorizations
- **Eigen-analysis:** Understanding dominant directions via eigenvalues
- **Optimization:** Least squares, gradient descent
- **Data analysis:** Principal component analysis, singular value decomposition

All leverage the linear structure.

### 3. **Dimension as a Measure of Complexity**

The dimension of a vector space quantifies its "degrees of freedom":
- 1D: a line (movements in one direction)
- 2D: a plane (two independent directions)
- 3D: ordinary space (three independent directions)
- 1000D: a high-dimensional feature space in machine learning

This gives us intuition for high-dimensional problems.

### 4. **Change of Basis**

The same vector space can be represented using different bases. Change of basis is just a linear transformation, and many problems become easier in the "right" coordinate system (e.g., diagonalizing a matrix).

### 5. **Approximation and Projection**

In high-dimensional spaces, we can project onto lower-dimensional subspaces to find best approximations (e.g., least-squares fitting, dimensionality reduction).

## Connected Concepts

### Inner Product Spaces

An inner product `⟨v, w⟩` on a vector space adds:
- A notion of "angle" between vectors
- A notion of "length" of a vector: `‖v‖ = √⟨v, v⟩`
- A notion of "orthogonality": `v ⊥ w` iff `⟨v, w⟩ = 0`

### Normed Vector Spaces

A norm `‖·‖` assigns a "size" to each vector, letting us measure distance and convergence.

### Banach and Hilbert Spaces

Infinite-dimensional vector spaces with analysis (limits, continuity) built in. Essential for:
- Functional analysis
- Quantum mechanics
- Signal processing

## Vector Spaces in the Lean Formalization

The `VectorSpace` typeclass in E14_VectorSpace.lean reflects the choice to collapse distinctions:

```lean
class VectorSpace (F V : Type) ... where
  smul : F → V → V    -- everything in V gets scalar multiplication
  -- V is just one type; all elements can be added and scaled
```

**What this means:**
- No type distinction between "locations" and "displacements"
- `v + w` always works (no need to think about what you're adding)
- The zero element `0` is automatically the origin
- Coordinates are implicit in the structure

Compare to affine spaces:

```lean
class AffineSpace (V : Type) (P : Type) where
  vadd : V → P → P    -- vectors *act on* points
  vsub : P → P → V    -- only subtraction gives vectors
  -- P and V are different types; keeps the distinction explicit
```

**The type-theoretic lesson:** When you formalize in a dependently-typed language, you gain the ability to *express* distinctions precisely. Vector spaces show the cost: by using a single type, we lose the type system's help in preventing conceptual errors. Affine spaces show the benefit: by keeping types separate, we force ourselves—and help the compiler help us—to think clearly.

This is why mathematical foundations matter in formal proof assistants. The choice of which abstraction to formalize shapes what kinds of errors the system can catch for you.

---

## Summary: Vector Space at a Glance

```
Vector Space V over Field F:
(An Affine Space with a Chosen Origin—Collapsed into One Type)

Relationship to Affine Space (V, P):
  • We've chosen an origin point o ∈ P
  • We've collapsed points and vectors into one type V
  • The zero element 0 is the chosen origin (but this is now hidden)
  • Addition is defined everywhere (no type checking to prevent mistakes)

Operations:
  • Addition:        v + w ∈ V       [add any two elements]
  • Scalar mult:     s • v ∈ V       [scale vector by scalar]
  • Negation:        -v ∈ V          [additive inverse]
  • Additive id:     0 ∈ V           [the implicit origin]

Laws:
  • (V, +) is an abelian group
  • Scalar multiplication is associative: (s*t)•v = s•(t•v)
  • Identities: 0 + v = v,  1•v = v
  • Distributivity: (s+t)•v = s•v + t•v,  s•(v+w) = s•v + s•w

Key Concepts:
  • Linear combination: c₁•v₁ + ... + cₙ•vₙ
  • Span: all possible linear combinations
  • Linear independence: no redundant vectors in a set
  • Basis: minimal spanning set
  • Dimension: size of any basis
  • Linear map: function preserving vector structure

Trade-off Summary:
  ✓ Gained: Computational convenience, algebraic closure, simplicity
  ✗ Lost: Type safety, conceptual clarity, coordinate-freeness
```

## Hierarchy of Structures

```
Set (no structure)
  ↓
Group (addition with identity and inverses)
  ↓
Affine Space (group acts transitively & freely on points)
  ↓
Vector Space (affine space with a chosen origin)
  ↓
Inner Product Space (vector space + geometry via inner product)
  ↓
Hilbert Space (inner product space + analysis/limits)
```

**Key relationship:** Every vector space can be viewed as an affine space by ignoring the special role of the origin. Conversely, every affine space becomes a vector space once an origin is chosen.

Vector spaces sit at the junction between pure algebra and geometry, making them one of the most powerful and widely-used abstractions in mathematics and applied science. They trade the geometric elegance of affine spaces (no privileged point) for the algebraic convenience of being able to add elements and perform linear operations directly.
