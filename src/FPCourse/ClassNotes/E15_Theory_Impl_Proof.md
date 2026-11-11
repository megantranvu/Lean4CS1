```lean
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
```

# E15: Theory, Implementation, and Proof

## Architecture

This lesson demonstrates a fundamental pattern in mathematics and software:

1. **Theory Layer**: Abstract definitions and axioms
   - `AffineSpaceTheory` and `VectorSpaceTheory` state what properties structures must have
   - No specific types; works over arbitrary type parameters

2. **Implementation Layer**: Concrete instances
   - Three implementations, over ℚ, ℚ² and ℚ³, each giving points and vectors
     their own distinct types
   - Each satisfies the abstract theory

3. **Proof Bridge**: Theorems showing each implementation satisfies the theory
   - Proves that concrete instances meet abstract requirements
   - Justifies using abstract reasoning to derive facts about implementations

This pattern separates *what we require* (theory) from *what we provide* (implementation),
with proofs connecting them. This is the essence of abstraction.
```lean
namespace TheoryImplProof
```

## Theory Layer: Abstract Requirements for Geometric Structures

We abstract the essential properties that make something an affine or vector space,
without committing to any specific type. Rather than re-documenting Group and
AffineSpace axioms (see E13 and E14), we provide a minimal recap here.
### Abstract Theory: Recap and Abstraction

From E13, a Group has operation, identity, associativity, and inverses.
From E14, an AffineSpace has a Group acting on points via vadd/vsub.
Now we formalize these patterns generically over arbitrary types.
```lean
class Group (α : Type) where
  op      : α → α → α
  id      : α
  assoc   : ∀ a b c : α, op (op a b) c = op a (op b c)
  idLeft  : ∀ a : α, op id a = a
  idRight : ∀ a : α, op a id = a
  inv     : α → α
  invLeft : ∀ a : α, op (inv a) a = id
  invRight: ∀ a : α, op a (inv a) = id

instance [Group α] : Add α where add := Group.op
instance [Group α] : Neg α where neg := Group.inv
instance [Group α] : Zero α where zero := Group.id

class AffineSpaceTheory (V : Type) (P : Type) where
  [groupV : Group V]
  vadd    : V → P → P
  vsub    : P → P → V
  vaddAssoc : ∀ v w : V, ∀ p : P, vadd v (vadd w p) = vadd (groupV.op v w) p
  vaddZero  : ∀ p : P, vadd groupV.id p = p
  vsubAdd   : ∀ p q : P, vadd (vsub q p) p = q
  addVsub   : ∀ v : V, ∀ p : P, vsub (vadd v p) p = v

/- Standard notation typeclasses -/
class VAdd (V : Type) (P : Type) where vadd : V → P → P
class VSub (P : Type) (V : Type) where vsub : P → P → V

instance [AffineSpaceTheory V P] : VAdd V P where vadd := AffineSpaceTheory.vadd
instance [AffineSpaceTheory V P] : VSub P V where vsub := AffineSpaceTheory.vsub

-- Both at precedence 65, matching mathlib. `-ᵥ` must bind tighter than `=`
-- (precedence 50), or a goal like `q -ᵥ p = v` fails to parse.
infixl:65 " +ᵥ " => VAdd.vadd
infixl:65 " -ᵥ " => VSub.vsub
```

### Abstract Theory: VectorSpaceTheory

A vector space requires:
- scalars `F`, carrying multiplication, a `1`, and an additive group structure
- vectors `V`, carrying an additive group structure
- a scalar multiplication `smul : F → V → V`
- four axioms relating the scalar operations to the vector ones

We reuse our own `Group` class for the additive structure of *both* `F` and
`V`, which is why `groupF` and `groupV` appear below. `groupF.op` is addition
on scalars and `groupF.id` is the scalar `0`; likewise for vectors. Scalar
multiplication and `1` come from Lean's `Mul` and `One`.

### Module or Vector Space? The Precise Difference

A qualification about the name, since these four axioms are exactly the
*module* axioms. The two notions have **identical axioms**; the difference is
entirely a condition on the scalars:

  - a **module** over `R` needs `R` to be a ring: scalars have `+`, `*`, `0`, `1`
  - a **vector space** over `K` needs `K` to be a *field*: additionally every
    non-zero scalar has a multiplicative inverse

So a vector space is not a different structure. It is a module whose scalars
can be divided by. Nothing in the axioms changes, which is exactly why every
theorem below holds in both settings.

What invertible scalars buy is the ability to *undo* a scaling. Over a field,
if `a ≠ 0` then `a⁻¹ • (a • v) = (a⁻¹ * a) • v = 1 • v = v`, by `mulSmul`
then `oneSmul`. Over a mere ring there is no `a⁻¹` to apply: working over ℤ
you can double a vector but not halve it.

The sharpest symptom of that gap is *torsion*. In a module, `a • v = 0` can
happen with `a ≠ 0` and `v ≠ 0` -- take ℤ/6 as a module over ℤ, where
`2 • 3 = 6 = 0` though neither factor is zero. In a vector space this is
impossible: scale by `a⁻¹` and `v = a⁻¹ • 0 = 0`, using `vector_scalar_zero`
proven later in this file. Torsion is in turn why a module need not have a
basis or a well-defined dimension, while every vector space has both; ℤ/6 has
no ℤ-basis at all.

Modules over ℤ are precisely the abelian groups, so this is a genuinely wider
notion rather than a technicality. Mathlib reflects all of this: it provides
`Module R M` for a semiring `R`, and a vector space is just `Module K V` with
`K` a field -- there is no separate `VectorSpace` class.

We do not state the field requirement here, because none of the theorems
below need it. So `VectorSpaceTheory F V` says "`V` is a module over `F`",
and it is a vector space exactly when `F` is a field, as ℚ is in all three
implementations.
```lean
class VectorSpaceTheory (F V : Type) [Mul F] [One F] where
  [groupF : Group F]
  [groupV : Group V]
  smul    : F → V → V
  -- Scaling by 1 does nothing.
  oneSmul : ∀ v : V, smul 1 v = v
  -- Scaling by a product is scaling twice.
  mulSmul : ∀ a b : F, ∀ v : V, smul (a * b) v = smul a (smul b v)
  -- Scalar multiplication distributes over vector addition.
  smulAdd : ∀ a : F, ∀ v w : V,
    smul a (groupV.op v w) = groupV.op (smul a v) (smul a w)
  -- ...and over scalar addition.
  addSmul : ∀ a b : F, ∀ v : V,
    smul (groupF.op a b) v = groupV.op (smul a v) (smul b v)

instance [Mul F] [One F] [VectorSpaceTheory F V] : SMul F V where
  smul := VectorSpaceTheory.smul
```

### Two Cancellation Facts

Proved once for any group, so that two of the four affine laws become single
terms at every dimension below. Each is a `calc` chain naming the axiom it
uses at each step: associativity, then an inverse law, then an identity law.
```lean
theorem op_inv_op_cancel {α : Type} [Group α] (a b : α) :
    Group.op (Group.op a (Group.inv b)) b = a :=
  calc Group.op (Group.op a (Group.inv b)) b
      = Group.op a (Group.op (Group.inv b) b) := Group.assoc a (Group.inv b) b
    _ = Group.op a Group.id                   := congrArg (Group.op a) (Group.invLeft b)
    _ = a                                     := Group.idRight a

theorem op_op_inv_cancel {α : Type} [Group α] (a b : α) :
    Group.op (Group.op a b) (Group.inv b) = a :=
  calc Group.op (Group.op a b) (Group.inv b)
      = Group.op a (Group.op b (Group.inv b)) := Group.assoc a b (Group.inv b)
    _ = Group.op a Group.id                   := congrArg (Group.op a) (Group.invRight b)
    _ = a                                     := Group.idRight a
```

## Implementation Layer: Three Concrete Instances

Each implementation provides both an AffineSpaceTheory and VectorSpaceTheory instance.

### Points and Vectors Get Their Own Types

One decision shapes every instance below. The theory layer takes *two* type
parameters, `AffineSpaceTheory V P`, and we honour that separation in the
implementations: at each dimension there is a `PointN` type and a `VectorN`
type, and they are different types even though each is implemented as the
same tuple of rationals.

Instantiating both parameters with one type -- `AffineSpaceTheory (ℚ × ℚ)
(ℚ × ℚ)` -- satisfies the axioms, but it lets you add two points, an
operation with no geometric meaning. Declaring a `structure` with a single
field costs a few lines and makes that a type error instead. The torsors and
affine space lessons introduced the same device; here it recurs at three
dimensions, which is why the names carry the dimension.

The scalars stay bare `Rat`. They are not a geometric carrier, and ℚ needs to
remain ℚ for `VectorSpaceTheory`'s `Mul` and `One` constraints to be the
familiar ones.
### Implementation 1: ℚ (1-Dimensional)

The rational line. First the group of scalars, which is both the scalar
structure `groupF` for every vector space below and the representation that
the 1-dimensional point and vector types wrap.
```lean
instance : Group Rat where
  op      : Rat → Rat → Rat := (· + ·)
  id      : Rat := 0
  assoc   : ∀ a b c : Rat, (a + b) + c = a + (b + c) := Rat.add_assoc
  idLeft  : ∀ a : Rat, 0 + a = a := Rat.zero_add
  idRight : ∀ a : Rat, a + 0 = a := Rat.add_zero
  inv     : Rat → Rat := fun q => -q
  invLeft : ∀ a : Rat, (-a) + a = 0 := Rat.neg_add_cancel
  invRight: ∀ a : Rat, a + (-a) = 0 := Rat.add_neg_cancel

structure Vector1 where
  ofScalar ::
  toScalar : Rat
deriving DecidableEq

structure Point1 where
  ofScalar ::
  toScalar : Rat
deriving DecidableEq

instance : Repr Vector1 where reprPrec v _ := "Vector1 " ++ repr v.toScalar
instance : Repr Point1  where reprPrec p _ := "Point1 "  ++ repr p.toScalar
```

`Vector1` becomes a group by *transporting* the instance above across the
wrapper: unwrap, defer to ℚ, wrap the result. Each law follows from the
corresponding law on ℚ by `congrArg`, which lifts an equation on scalars to an
equation on `Vector1`. No arithmetic is redone.
```lean
instance : Group Vector1 where
  op v w      := ⟨Group.op v.toScalar w.toScalar⟩
  id          := ⟨Group.id⟩
  inv v       := ⟨Group.inv v.toScalar⟩
  assoc a b c := congrArg Vector1.ofScalar (Group.assoc a.toScalar b.toScalar c.toScalar)
  idLeft a    := congrArg Vector1.ofScalar (Group.idLeft a.toScalar)
  idRight a   := congrArg Vector1.ofScalar (Group.idRight a.toScalar)
  invLeft a   := congrArg Vector1.ofScalar (Group.invLeft a.toScalar)
  invRight a  := congrArg Vector1.ofScalar (Group.invRight a.toScalar)
```

The affine space. `vsub` is "compose with the inverse": the displacement from
`p` to `q` is `q` combined with the undoing of `p`. For ℚ that computes the
ordinary difference, and stating it group-theoretically makes `vsubAdd` and
`addVsub` one rewrite each.
```lean
instance : AffineSpaceTheory Vector1 Point1 where
  groupV   := inferInstance
  vadd v p := ⟨Group.op v.toScalar p.toScalar⟩
  vsub q p := ⟨Group.op q.toScalar (Group.inv p.toScalar)⟩
  vaddAssoc v w p :=
    congrArg Point1.ofScalar (Group.assoc v.toScalar w.toScalar p.toScalar).symm
  vaddZero p := congrArg Point1.ofScalar (Group.idLeft p.toScalar)
  vsubAdd p q := congrArg Point1.ofScalar (op_inv_op_cancel q.toScalar p.toScalar)
  addVsub v p := congrArg Vector1.ofScalar (op_op_inv_cancel v.toScalar p.toScalar)
```

And the vector space: scaling a 1-dimensional vector is multiplying its single
coordinate. Each axiom is then one library fact about rational multiplication,
lifted through the constructor by `congrArg` exactly as the group laws were:
`one_mul`, `mul_assoc`, `mul_add` and `add_mul` in turn. No axiom is restated
and no arithmetic is redone.
```lean
instance : VectorSpaceTheory Rat Vector1 where
  groupF    := inferInstance
  groupV    := inferInstance
  smul a v  := ⟨a * v.toScalar⟩
  oneSmul v     := congrArg Vector1.ofScalar (one_mul v.toScalar)
  mulSmul a b v := congrArg Vector1.ofScalar (mul_assoc a b v.toScalar)
  smulAdd a v w := congrArg Vector1.ofScalar (mul_add a v.toScalar w.toScalar)
  addSmul a b v := congrArg Vector1.ofScalar (add_mul a b v.toScalar)
```

### Implementation 2: ℚ × ℚ (2-Dimensional)

The rational plane. Same three instances, same shape of proof; the only change
is that the representation is a pair, so the group of the representation does
its arithmetic componentwise.
```lean
instance : Group (Rat × Rat) where
  op      : Rat × Rat → Rat × Rat → Rat × Rat := fun (a, b) (c, d) => (a + c, b + d)
  id      : Rat × Rat := (0, 0)
  assoc   : ∀ a b c : Rat × Rat, ((a.1 + b.1) + c.1, (a.2 + b.2) + c.2) = (a.1 + (b.1 + c.1), a.2 + (b.2 + c.2)) :=
    fun a b c => Prod.ext (Rat.add_assoc a.1 b.1 c.1) (Rat.add_assoc a.2 b.2 c.2)
  idLeft  : ∀ a : Rat × Rat, (0 + a.1, 0 + a.2) = a :=
    fun a => Prod.ext (Rat.zero_add a.1) (Rat.zero_add a.2)
  idRight : ∀ a : Rat × Rat, (a.1 + 0, a.2 + 0) = a :=
    fun a => Prod.ext (Rat.add_zero a.1) (Rat.add_zero a.2)
  inv     : Rat × Rat → Rat × Rat := fun (a, b) => (-a, -b)
  invLeft : ∀ a : Rat × Rat, (-a.1 + a.1, -a.2 + a.2) = (0, 0) :=
    fun a => Prod.ext (Rat.neg_add_cancel a.1) (Rat.neg_add_cancel a.2)
  invRight: ∀ a : Rat × Rat, (a.1 + (-a.1), a.2 + (-a.2)) = (0, 0) :=
    fun a => Prod.ext (Rat.add_neg_cancel a.1) (Rat.add_neg_cancel a.2)

structure Vector2 where
  ofPair ::
  toPair : Rat × Rat
deriving DecidableEq

structure Point2 where
  ofPair ::
  toPair : Rat × Rat
deriving DecidableEq

instance : Repr Vector2 where reprPrec v _ := "Vector2 " ++ repr v.toPair
instance : Repr Point2  where reprPrec p _ := "Point2 "  ++ repr p.toPair

instance : Group Vector2 where
  op v w      := ⟨Group.op v.toPair w.toPair⟩
  id          := ⟨Group.id⟩
  inv v       := ⟨Group.inv v.toPair⟩
  assoc a b c := congrArg Vector2.ofPair (Group.assoc a.toPair b.toPair c.toPair)
  idLeft a    := congrArg Vector2.ofPair (Group.idLeft a.toPair)
  idRight a   := congrArg Vector2.ofPair (Group.idRight a.toPair)
  invLeft a   := congrArg Vector2.ofPair (Group.invLeft a.toPair)
  invRight a  := congrArg Vector2.ofPair (Group.invRight a.toPair)

instance : AffineSpaceTheory Vector2 Point2 where
  groupV   := inferInstance
  vadd v p := ⟨Group.op v.toPair p.toPair⟩
  vsub q p := ⟨Group.op q.toPair (Group.inv p.toPair)⟩
  vaddAssoc v w p :=
    congrArg Point2.ofPair (Group.assoc v.toPair w.toPair p.toPair).symm
  vaddZero p := congrArg Point2.ofPair (Group.idLeft p.toPair)
  vsubAdd p q := congrArg Point2.ofPair (op_inv_op_cancel q.toPair p.toPair)
  addVsub v p := congrArg Vector2.ofPair (op_op_inv_cancel v.toPair p.toPair)

instance : VectorSpaceTheory Rat Vector2 where
  groupF   := inferInstance
  groupV   := inferInstance
  smul a v := ⟨(a * v.toPair.1, a * v.toPair.2)⟩
  oneSmul v := congrArg Vector2.ofPair
    (Prod.ext (one_mul v.toPair.1) (one_mul v.toPair.2))
  mulSmul a b v := congrArg Vector2.ofPair
    (Prod.ext (mul_assoc a b v.toPair.1) (mul_assoc a b v.toPair.2))
  smulAdd a v w := congrArg Vector2.ofPair
    (Prod.ext (mul_add a v.toPair.1 w.toPair.1) (mul_add a v.toPair.2 w.toPair.2))
  addSmul a b v := congrArg Vector2.ofPair
    (Prod.ext (add_mul a b v.toPair.1) (add_mul a b v.toPair.2))
```

### Implementation 3: ℚ × ℚ × ℚ (3-Dimensional)

Three dimensions, no new ideas -- which is the point of showing it. Note that
`Vector2` and `Vector3` are distinct types, so mixing dimensions is a type
error and not a silently wrong computation.
```lean
instance : Group (Rat × Rat × Rat) where
  op      : Rat × Rat × Rat → Rat × Rat × Rat → Rat × Rat × Rat := fun (a, b, c) (d, e, f) => (a + d, b + e, c + f)
  id      : Rat × Rat × Rat := (0, 0, 0)
  assoc   : ∀ a b c : Rat × Rat × Rat, ((a.1 + b.1) + c.1, (a.2.1 + b.2.1) + c.2.1, (a.2.2 + b.2.2) + c.2.2) = (a.1 + (b.1 + c.1), a.2.1 + (b.2.1 + c.2.1), a.2.2 + (b.2.2 + c.2.2)) :=
    fun a b c => Prod.ext (Rat.add_assoc a.1 b.1 c.1)
      (Prod.ext (Rat.add_assoc a.2.1 b.2.1 c.2.1) (Rat.add_assoc a.2.2 b.2.2 c.2.2))
  idLeft  : ∀ a : Rat × Rat × Rat, (0 + a.1, 0 + a.2.1, 0 + a.2.2) = a :=
    fun a => Prod.ext (Rat.zero_add a.1)
      (Prod.ext (Rat.zero_add a.2.1) (Rat.zero_add a.2.2))
  idRight : ∀ a : Rat × Rat × Rat, (a.1 + 0, a.2.1 + 0, a.2.2 + 0) = a :=
    fun a => Prod.ext (Rat.add_zero a.1)
      (Prod.ext (Rat.add_zero a.2.1) (Rat.add_zero a.2.2))
  inv     : Rat × Rat × Rat → Rat × Rat × Rat := fun (a, b, c) => (-a, -b, -c)
  invLeft : ∀ a : Rat × Rat × Rat, (-a.1 + a.1, -a.2.1 + a.2.1, -a.2.2 + a.2.2) = (0, 0, 0) :=
    fun a => Prod.ext (Rat.neg_add_cancel a.1)
      (Prod.ext (Rat.neg_add_cancel a.2.1) (Rat.neg_add_cancel a.2.2))
  invRight: ∀ a : Rat × Rat × Rat, (a.1 + (-a.1), a.2.1 + (-a.2.1), a.2.2 + (-a.2.2)) = (0, 0, 0) :=
    fun a => Prod.ext (Rat.add_neg_cancel a.1)
      (Prod.ext (Rat.add_neg_cancel a.2.1) (Rat.add_neg_cancel a.2.2))

structure Vector3 where
  ofTriple ::
  toTriple : Rat × Rat × Rat
deriving DecidableEq

structure Point3 where
  ofTriple ::
  toTriple : Rat × Rat × Rat
deriving DecidableEq

instance : Repr Vector3 where reprPrec v _ := "Vector3 " ++ repr v.toTriple
instance : Repr Point3  where reprPrec p _ := "Point3 "  ++ repr p.toTriple

instance : Group Vector3 where
  op v w      := ⟨Group.op v.toTriple w.toTriple⟩
  id          := ⟨Group.id⟩
  inv v       := ⟨Group.inv v.toTriple⟩
  assoc a b c := congrArg Vector3.ofTriple (Group.assoc a.toTriple b.toTriple c.toTriple)
  idLeft a    := congrArg Vector3.ofTriple (Group.idLeft a.toTriple)
  idRight a   := congrArg Vector3.ofTriple (Group.idRight a.toTriple)
  invLeft a   := congrArg Vector3.ofTriple (Group.invLeft a.toTriple)
  invRight a  := congrArg Vector3.ofTriple (Group.invRight a.toTriple)

instance : AffineSpaceTheory Vector3 Point3 where
  groupV   := inferInstance
  vadd v p := ⟨Group.op v.toTriple p.toTriple⟩
  vsub q p := ⟨Group.op q.toTriple (Group.inv p.toTriple)⟩
  vaddAssoc v w p :=
    congrArg Point3.ofTriple (Group.assoc v.toTriple w.toTriple p.toTriple).symm
  vaddZero p := congrArg Point3.ofTriple (Group.idLeft p.toTriple)
  vsubAdd p q := congrArg Point3.ofTriple (op_inv_op_cancel q.toTriple p.toTriple)
  addVsub v p := congrArg Vector3.ofTriple (op_op_inv_cancel v.toTriple p.toTriple)

instance : VectorSpaceTheory Rat Vector3 where
  groupF   := inferInstance
  groupV   := inferInstance
  smul a v := ⟨(a * v.toTriple.1, a * v.toTriple.2.1, a * v.toTriple.2.2)⟩
  oneSmul v := congrArg Vector3.ofTriple
    (Prod.ext (one_mul v.toTriple.1)
      (Prod.ext (one_mul v.toTriple.2.1) (one_mul v.toTriple.2.2)))
  mulSmul a b v := congrArg Vector3.ofTriple
    (Prod.ext (mul_assoc a b v.toTriple.1)
      (Prod.ext (mul_assoc a b v.toTriple.2.1) (mul_assoc a b v.toTriple.2.2)))
  smulAdd a v w := congrArg Vector3.ofTriple
    (Prod.ext (mul_add a v.toTriple.1 w.toTriple.1)
      (Prod.ext (mul_add a v.toTriple.2.1 w.toTriple.2.1)
        (mul_add a v.toTriple.2.2 w.toTriple.2.2)))
  addSmul a b v := congrArg Vector3.ofTriple
    (Prod.ext (add_mul a b v.toTriple.1)
      (Prod.ext (add_mul a b v.toTriple.2.1) (add_mul a b v.toTriple.2.2)))
```

## Proof Bridge Layer: Theorems About the Abstract Theory

Now we prove facts about the abstract theory. These theorems apply to *all* implementations.
The proofs work generically over any type satisfying the theory, then apply to all three
concrete instances for free.
### General Theorems About Affine Spaces

These theorems hold for *any* affine space satisfying `AffineSpaceTheory`.
```lean
theorem affine_translation_inversion {V P : Type} [aff : AffineSpaceTheory V P] (p q : P) :
    aff.vadd (aff.vsub q p) p = q :=
  aff.vsubAdd p q

theorem affine_vector_recovery {V P : Type} [aff : AffineSpaceTheory V P] (v : V) (p : P) :
    aff.vsub (aff.vadd v p) p = v :=
  aff.addVsub v p
```

This one is the real content: the displacement from `p` to `r` is the
composition of the displacements `p → q` and `q → r`. It follows from the
axioms alone, with no appeal to commutativity and no reference to ℚ -- which
is the whole claim of the theory layer.
```lean
theorem affine_transitivity {V P : Type} [aff : AffineSpaceTheory V P] (p q r : P) :
    aff.groupV.op (aff.vsub r q) (aff.vsub q p) = aff.vsub r p :=
  calc aff.groupV.op (aff.vsub r q) (aff.vsub q p)
      -- `addVsub` says a displacement is recovered by applying it and
      -- differencing back, so rewrite the left side into that shape.
      = aff.vsub (aff.vadd (aff.groupV.op (aff.vsub r q) (aff.vsub q p)) p) p :=
        (aff.addVsub _ _).symm
      -- Split the composed translation into two translations.
    _ = aff.vsub (aff.vadd (aff.vsub r q) (aff.vadd (aff.vsub q p) p)) p :=
        congrArg (fun x => aff.vsub x p) (aff.vaddAssoc _ _ _).symm
      -- The inner one carries p to q ...
    _ = aff.vsub (aff.vadd (aff.vsub r q) q) p :=
        congrArg (fun x => aff.vsub (aff.vadd (aff.vsub r q) x) p) (aff.vsubAdd p q)
      -- ... and the outer one carries q to r.
    _ = aff.vsub r p :=
        congrArg (fun x => aff.vsub x p) (aff.vsubAdd q r)
```

### General Theorems About Vector Spaces

These theorems hold for *any* vector space satisfying `VectorSpaceTheory` (with appropriate type constraints).
The pattern demonstrates reusable proofs: write once over the abstract theory, apply to all implementations.
First, two small facts about any group. Both vector space theorems below need
them, so we prove them once rather than twice.
```lean
theorem Group.eq_id_of_idem {α : Type} (g : Group α) {a : α}
    (h : g.op a a = a) : a = g.id :=
  -- An idempotent element of a group is the identity: cancel one copy of `a`.
  calc a = g.op g.id a             := (g.idLeft a).symm
    _ = g.op (g.op (g.inv a) a) a  := congrArg (fun x => g.op x a) (g.invLeft a).symm
    _ = g.op (g.inv a) (g.op a a)  := g.assoc (g.inv a) a a
    _ = g.op (g.inv a) a           := congrArg (g.op (g.inv a)) h
    _ = g.id                       := g.invLeft a

theorem Group.inv_eq_of_op_eq_id {α : Type} (g : Group α) {a b : α}
    (h : g.op a b = g.id) : b = g.inv a :=
  -- Inverses in a group are unique.
  calc b = g.op g.id b             := (g.idLeft b).symm
    _ = g.op (g.op (g.inv a) a) b  := congrArg (fun x => g.op x b) (g.invLeft a).symm
    _ = g.op (g.inv a) (g.op a b)  := g.assoc (g.inv a) a b
    _ = g.op (g.inv a) g.id        := congrArg (g.op (g.inv a)) h
    _ = g.inv a                    := g.idRight (g.inv a)
```

Now the vector space theorems. Note that `0 • v = 0` and `a • 0 = 0` are
*not* axioms -- they are consequences, and the derivation is the same trick
in both cases: show the thing is idempotent, then invoke the group fact above.

For `0 • v`: distributing `(0 + 0) • v` gives `0 • v + 0 • v`, but `0 + 0 = 0`,
so `0 • v` equals its own double and must therefore be the zero vector.
```lean
theorem vector_zero_scalar {F V : Type} [Mul F] [One F] [vs : VectorSpaceTheory F V]
    (v : V) : vs.smul vs.groupF.id v = vs.groupV.id :=
  Group.eq_id_of_idem vs.groupV
    (calc vs.groupV.op (vs.smul vs.groupF.id v) (vs.smul vs.groupF.id v)
        = vs.smul (vs.groupF.op vs.groupF.id vs.groupF.id) v :=
            (vs.addSmul vs.groupF.id vs.groupF.id v).symm
      _ = vs.smul vs.groupF.id v :=
            congrArg (fun x => vs.smul x v) (vs.groupF.idLeft vs.groupF.id))

theorem vector_scalar_zero {F V : Type} [Mul F] [One F] [vs : VectorSpaceTheory F V]
    (a : F) : vs.smul a vs.groupV.id = vs.groupV.id :=
  Group.eq_id_of_idem vs.groupV
    (calc vs.groupV.op (vs.smul a vs.groupV.id) (vs.smul a vs.groupV.id)
        = vs.smul a (vs.groupV.op vs.groupV.id vs.groupV.id) :=
            (vs.smulAdd a vs.groupV.id vs.groupV.id).symm
      _ = vs.smul a vs.groupV.id :=
            congrArg (vs.smul a) (vs.groupV.idLeft vs.groupV.id))
```

And scaling a negated vector negates the result, because `a • v` and
`a • (-v)` sum to `a • 0 = 0`, so the second is the inverse of the first.
```lean
theorem vector_neg_scalar {F V : Type} [Mul F] [One F] [vs : VectorSpaceTheory F V]
    (a : F) (v : V) :
    vs.smul a (vs.groupV.inv v) = vs.groupV.inv (vs.smul a v) :=
  Group.inv_eq_of_op_eq_id vs.groupV
    (calc vs.groupV.op (vs.smul a v) (vs.smul a (vs.groupV.inv v))
        = vs.smul a (vs.groupV.op v (vs.groupV.inv v)) :=
            (vs.smulAdd a v (vs.groupV.inv v)).symm
      _ = vs.smul a vs.groupV.id := congrArg (vs.smul a) (vs.groupV.invRight v)
      _ = vs.groupV.id           := vector_scalar_zero a)
```

## Summary: The Theory-Implementation-Proof Pattern

**Theory Layer**: Abstract axioms define what properties a structure must have.
- `AffineSpaceTheory V P`: what axioms make something an affine space
- `VectorSpaceTheory F V`: what axioms make `V` a module over the scalars `F`
  (a vector space when `F` is a field)

**Implementation Layer**: Concrete types satisfy the theory.
- `Point1`/`Vector1`, `Point2`/`Vector2` and `Point3`/`Vector3` are the
  implementations, over ℚ, ℚ × ℚ and ℚ × ℚ × ℚ respectively
- Points and vectors are distinct types at each dimension, so adding two
  points is a type error rather than a meaningless value
- Proofs that they satisfy the abstract axioms

**Proof Bridge Layer**: Generic theorems about the theory apply to all implementations.
- `affine_translation_inversion` and `affine_transitivity`: true for any
  affine space
- `vector_zero_scalar`, `vector_scalar_zero` and `vector_neg_scalar`: true for
  any module, hence for any vector space. None of these is an axiom; each is
  derived from the four scalar axioms plus two facts about groups.

This separation allows:
1. Reasoning abstractly (proving once for all implementations)
2. Checking concreteness (verifying implementations satisfy theory)
3. Reusing results (generic theorems apply everywhere)

The pattern scales: one abstract theory + many implementations + shared proofs.
## Concrete Demonstration: One Proof, Three Implementations

`affine_translation_inversion` and `affine_transitivity` were each proven once,
over an arbitrary `AffineSpaceTheory V P`. Below they are applied at all three
dimensions. Note what is *absent*: there is no proof in any of these, only the
name of the generic theorem. That is the payoff the whole lesson is about.
```lean
/- The type ascription on `vsub` is needed because the vector type `V` appears
   only in that field's *result*, so Lean cannot infer it from `p` and `q`
   alone. It is a hint to instance search, not an extra assumption. -/

example (p q : Point1) :
    AffineSpaceTheory.vadd (AffineSpaceTheory.vsub q p : Vector1) p = q :=
  affine_translation_inversion p q

example (p q : Point2) :
    AffineSpaceTheory.vadd (AffineSpaceTheory.vsub q p : Vector2) p = q :=
  affine_translation_inversion p q

example (p q : Point3) :
    AffineSpaceTheory.vadd (AffineSpaceTheory.vsub q p : Vector3) p = q :=
  affine_translation_inversion p q

/- The composition law, likewise proven once and reused at each dimension. -/

example (p q r : Point1) :
    Group.op (AffineSpaceTheory.vsub r q : Vector1) (AffineSpaceTheory.vsub q p : Vector1)
      = (AffineSpaceTheory.vsub r p : Vector1) :=
  affine_transitivity p q r

example (p q r : Point2) :
    Group.op (AffineSpaceTheory.vsub r q : Vector2) (AffineSpaceTheory.vsub q p : Vector2)
      = (AffineSpaceTheory.vsub r p : Vector2) :=
  affine_transitivity p q r

example (p q r : Point3) :
    Group.op (AffineSpaceTheory.vsub r q : Vector3)
             (AffineSpaceTheory.vsub q p : Vector3)
      = (AffineSpaceTheory.vsub r p : Vector3) :=
  affine_transitivity p q r
```

And because the axioms are now proven rather than assumed, the instances are
computable: the operations actually run. The printed type on each result says
which role the value plays -- a displacement or a location.
```lean
#eval (AffineSpaceTheory.vsub (Point2.ofPair (7, 9)) (Point2.ofPair (2, 3)) : Vector2)
      -- Vector2 (5, 6): the displacement from (2,3) to (7,9)

#eval (AffineSpaceTheory.vadd (Vector2.ofPair (5, 6)) (Point2.ofPair (2, 3)) : Point2)
      -- Point2 (7, 9): applying that displacement to (2,3) returns to (7,9)

#eval (AffineSpaceTheory.vsub (Point3.ofTriple (1, 2, 3)) (Point3.ofTriple (1, 1, 1))
       : Vector3)
      -- Vector3 (0, 1, 2)
```

And what the types rule out. Each of these is rejected:

  `Group.op (Point2.ofPair (1, 1)) (Point2.ofPair (2, 2))`
      -- no `Group Point2` instance: points do not add
  `AffineSpaceTheory.vadd (Point2.ofPair (1, 1)) (Point2.ofPair (2, 2))`
      -- `vadd` takes a vector first, and a point is not a vector
  `AffineSpaceTheory.vadd (Vector2.ofPair (1, 1)) (Point3.ofTriple (2, 2, 2))`
      -- no instance relates 2D vectors to 3D points: dimensions cannot mix

Lean reports each as a failure to synthesize the instance that would be needed
for the expression to mean anything -- which is the type checker saying,
correctly, that there is no such operation.
## The Same Pattern on the Vector Space Side

`vector_zero_scalar`, `vector_scalar_zero` and `vector_neg_scalar` were each
proven once over an arbitrary `VectorSpaceTheory F V`. Here they are at all
three dimensions -- again with no proof, only the theorem's name.

Recall that `Group.id` *is* the zero: the scalar `0` in ℚ, and the wrapped
zero tuple in `Vector1`, `Vector2` and `Vector3`.
```lean
/- `0 • v = 0`, for every vector in every one of the three spaces. -/

example (v : Vector1) :
    VectorSpaceTheory.smul (Group.id : Rat) v = (Group.id : Vector1) :=
  vector_zero_scalar v

example (v : Vector2) :
    VectorSpaceTheory.smul (Group.id : Rat) v = (Group.id : Vector2) :=
  vector_zero_scalar v

example (v : Vector3) :
    VectorSpaceTheory.smul (Group.id : Rat) v = (Group.id : Vector3) :=
  vector_zero_scalar v

/- `a • 0 = 0`, for every scalar. -/

example (a : Rat) :
    VectorSpaceTheory.smul a (Group.id : Vector2) = (Group.id : Vector2) :=
  vector_scalar_zero a

/- `a • (-v) = -(a • v)`. -/

example (a : Rat) (v : Vector2) :
    VectorSpaceTheory.smul a (Group.inv v) = Group.inv (VectorSpaceTheory.smul a v) :=
  vector_neg_scalar a v
```

And the scalar multiplications compute, too.
```lean
#eval (VectorSpaceTheory.smul (2 : Rat) (Vector2.ofPair (3, 4)) : Vector2)
      -- Vector2 (6, 8)
#eval (VectorSpaceTheory.smul (0 : Rat) (Vector2.ofPair (3, 4)) : Vector2)
      -- Vector2 (0, 0), as vector_zero_scalar guarantees
#eval (VectorSpaceTheory.smul (1 : Rat) (Vector2.ofPair (3, 4)) : Vector2)
      -- Vector2 (3, 4), as the oneSmul axiom requires
#eval (VectorSpaceTheory.smul (1/2 : Rat) (Vector3.ofTriple (1, 2, 3)) : Vector3)
      -- Vector3 ((1 : Rat)/2, 1, (3 : Rat)/2)

end TheoryImplProof
```


<div class="issue-box">📝 <a href="https://github.com/kevinsullivan/Lean4CS1/issues/new">Report an issue</a> with this section</div>

