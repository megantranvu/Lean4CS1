-- FPCourse/T04_SetsAndRelations/W10_SetsRelations.lean
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Logic.Relation

/-! @@@
# Sets and Relations

## Sets as predicates

In Lean (and in Mathlib), a *set* over type `α` is simply a predicate:

```lean
def Set (α : Type u) : Type u := α → Prop
```

A set `s : Set α` is a function that takes an element `x : α` and
returns a proposition `s x : Prop` — the claim that `x` belongs to `s`.

This definition is mathematically natural and computationally illuminating:
membership is a proposition, and propositions are types.  A proof that
`x ∈ s` is a term of type `s x`.

The connection to the course themes: sets are logical types indexed by
their elements.  Every operation on sets is an operation on propositions.
@@@ -/

namespace W10

/-! @@@
## 10.1  Set membership and basic notation
@@@ -/

-- Set α is defined in Mathlib as α → Prop
#check @Set        -- (α : Type u) → Type u
#print Set         -- def Set (α : Type u) := α → Prop

-- Membership: x ∈ s is notation for s x
example : (3 : Nat) ∈ ({1, 2, 3} : Set Nat) := by decide
example : (5 : Nat) ∉ ({1, 2, 3} : Set Nat) := by decide

/-! @@@
> **Checkpoint — set membership.** `x ∈ s` is just `s x`, the proposition that `x`
> satisfies the predicate. **Predict** the Boolean below — is `3` one of the listed
> elements? — then check.
@@@ -/

#eval decide ((3 : Nat) ∈ ({1, 2, 3} : Set Nat))   -- predict first

-- The universal set (all elements)
#check @Set.univ   -- Set α  (= fun _ => True)

-- The empty set
#check (∅ : Set _)  -- Set α  (= fun _ => False)

-- Membership in univ and empty:
theorem mem_univ (x : α) : x ∈ (Set.univ : Set α) :=
  trivial

theorem not_mem_empty (x : α) : x ∉ (∅ : Set α) :=
  False.elim

/-! @@@
> **Checkpoint — `Set.univ` and `∅`.** `univ = fun _ => True` and `∅ = fun _ => False`
> are the two constant sets. **Predict** both Booleans — everything is in `univ`, nothing
> is in `∅` — then check.
@@@ -/

#eval decide ((7 : Nat) ∈ (Set.univ : Set Nat))   -- predict first
#eval decide ((7 : Nat) ∈ (∅ : Set Nat))          -- predict first

/-! @@@
## 10.2  Set operations as proposition operations

Because sets are predicates, every set operation corresponds to a
propositional connective.

| Set operation | Logical meaning | Notation |
|--------------|----------------|---------|
| `s ∩ t` (intersection) | `s x ∧ t x` | `∩` |
| `s ∪ t` (union) | `s x ∨ t x` | `∪` |
| `sᶜ` (complement) | `¬ s x` | `·ᶜ` |
| `s \ t` (difference) | `s x ∧ ¬ t x` | `\` |
| `s ⊆ t` (subset) | `∀ x, s x → t x` | `⊆` |

Read `s ⊆ t` aloud: "for every `x`, if `x` belongs to `s` then `x` belongs to `t`."
Read `s ∩ t = s ∪ t` would mean: "for every `x`, `x ∈ s ∧ x ∈ t` iff `x ∈ s ∨ x ∈ t`" — which is false.

Notice the pattern: **every set statement reduces to a statement about propositions, quantified over elements.**  When you prove something about sets, you are doing propositional logic with `∀` threading through.
@@@ -/

-- Intersection is ∧:
theorem mem_inter_iff (x : α) (s t : Set α) :
    x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t :=
  Set.mem_inter_iff x s t

/-! @@@
> **Checkpoint — intersection `∩`.** By `mem_inter_iff`, `x ∈ s ∩ t` means `x ∈ s ∧ x ∈ t`.
> **Predict** whether `3` is in *both* sets below, then check.
@@@ -/

#eval decide ((3 : Nat) ∈ (({1, 2, 3} ∩ {3, 4, 5}) : Set Nat))   -- predict first

-- Union is ∨:
theorem mem_union_iff (x : α) (s t : Set α) :
    x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t :=
  Set.mem_union x s t

/-! @@@
> **Checkpoint — union `∪`.** By `mem_union_iff`, `x ∈ s ∪ t` means `x ∈ s ∨ x ∈ t`.
> **Predict** whether `1` is in *either* set below, then check.
@@@ -/

#eval decide ((1 : Nat) ∈ (({1, 2, 3} ∪ {3, 4, 5}) : Set Nat))   -- predict first

-- Subset is ∀/→:
theorem subset_def (s t : Set α) :
    s ⊆ t ↔ ∀ x, x ∈ s → x ∈ t :=
  Iff.intro (fun h _x hx => h hx) (fun h x hx => h x hx)

/-! @@@
> **Checkpoint — complement `ᶜ`.** `x ∈ sᶜ` means `¬ (x ∈ s)`. **Predict** whether `5`,
> which is not listed, belongs to the complement below, then check.
@@@ -/

#eval decide ((5 : Nat) ∈ (({1, 2, 3} : Set Nat)ᶜ))   -- predict first

/-! @@@
> **Checkpoint — difference `\`.** `x ∈ s \ t` means `x ∈ s ∧ ¬ (x ∈ t)`. **Predict**
> whether `1` survives removing `{3, 4}` from `{1, 2, 3}`, then check.
@@@ -/

#eval decide ((1 : Nat) ∈ (({1, 2, 3} \ {3, 4}) : Set Nat))   -- predict first

/-! @@@
> **Checkpoint — subset `⊆`.** `s ⊆ t` is `∀ x, x ∈ s → x ∈ t` — one implication *per
> element*, so it is not decidable over all of `Nat`. **Predict** that single implication
> at `x = 2` (is `2 ∈ {1,2} → 2 ∈ {1,2,3}` true?), then check.
@@@ -/

#eval decide ((2 : Nat) ∈ ({1, 2} : Set Nat) → (2 : Nat) ∈ ({1, 2, 3} : Set Nat))   -- predict first

/-! @@@
## 10.3  Set algebraic laws as propositions

These laws are propositions that hold for all sets.  The proofs are
provided as term-mode proofs.
@@@ -/

-- Commutativity:
theorem inter_comm (s t : Set α) : s ∩ t = t ∩ s :=
  Set.inter_comm s t

theorem union_comm (s t : Set α) : s ∪ t = t ∪ s :=
  Set.union_comm s t

/-! @@@
> **Checkpoint — `∩` commutativity.** `inter_comm` says `s ∩ t = t ∩ s`, so membership
> must agree on either side. **Predict** the Boolean (an `↔` of memberships at `x = 2`),
> then check.
@@@ -/

#eval decide ((2 : Nat) ∈ (({1, 2, 3} ∩ {2, 3, 4}) : Set Nat) ↔ (2 : Nat) ∈ (({2, 3, 4} ∩ {1, 2, 3}) : Set Nat))   -- predict first

-- Distributivity:
theorem inter_union_distrib (r s t : Set α) :
    r ∩ (s ∪ t) = (r ∩ s) ∪ (r ∩ t) :=
  Set.inter_union_distrib_left r s t

/-! @@@
> **Checkpoint — `∩`/`∪` distributivity.** `r ∩ (s ∪ t) = (r ∩ s) ∪ (r ∩ t)`. **Predict**
> the membership `↔` below at `x = 2`, then check.
@@@ -/

#eval decide ((2 : Nat) ∈ (({1, 2} ∩ ({2, 3} ∪ {4, 5})) : Set Nat) ↔ (2 : Nat) ∈ ((({1, 2} ∩ {2, 3}) ∪ ({1, 2} ∩ {4, 5})) : Set Nat))   -- predict first

-- De Morgan:
theorem compl_union (s t : Set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
  Set.compl_union s t

/-! @@@
> **Checkpoint — De Morgan.** `(s ∪ t)ᶜ = sᶜ ∩ tᶜ`: not-in-either equals not-in-each.
> **Predict** the membership `↔` at `x = 5` (in neither `{1,2}` nor `{3,4}`), then check.
@@@ -/

#eval decide ((5 : Nat) ∈ ((({1, 2} ∪ {3, 4}) : Set Nat)ᶜ) ↔ (5 : Nat) ∈ ((({1, 2} : Set Nat)ᶜ ∩ ({3, 4} : Set Nat)ᶜ)))   -- predict first

-- Subset is transitive:
theorem subset_trans {s t u : Set α} (h1 : s ⊆ t) (h2 : t ⊆ u) : s ⊆ u :=
  Set.Subset.trans h1 h2

/-! @@@
## 10.4  Relations

A *relation* between types `α` and `β` is a predicate on pairs:

```lean
def Rel (α β : Type u) : Type u := α → β → Prop
```

A term `r : Rel α β` applied to `a : α` and `b : β` gives a proposition
`r a b`: the claim that `a` and `b` are related.

Sets are the special case `Rel α α` (homogeneous relations), or `Rel α Prop`
(which is just `Set α`).
@@@ -/

-- Rel is a binary predicate (defined locally for compatibility)
abbrev Rel (α β : Type*) := α → β → Prop

-- Example relations:
def divides : Rel Nat Nat := fun m n => ∃ k, n = m * k
def sameLength : Rel (List α) (List β) := fun xs ys => xs.length = ys.length
def lePair : Rel Nat Nat := (· ≤ ·)

-- Membership in a relation:
example : divides 3 12 := ⟨4, rfl⟩
example : divides 1 n := ⟨n, (Nat.one_mul n).symm⟩   -- for any n

/-! @@@
> **Checkpoint — `divides`.** `divides m n` is `∃ k, n = m * k`; the example above
> witnesses `divides 3 12` with `k = 4`. **Predict** whether that witness equation holds,
> then check.
@@@ -/

#eval decide (12 = 3 * 4)   -- predict first (the witness for divides 3 12)

/-! @@@
> **Checkpoint — `sameLength`.** `sameLength xs ys` unfolds to `xs.length = ys.length`.
> **Predict** whether a 3-element list and a 3-element list are related, then check.
@@@ -/

#eval decide ([1, 2, 3].length = ['a', 'b', 'c'].length)   -- predict first (sameLength unfolded)

/-! @@@
> **Checkpoint — `lePair`.** `lePair` is `(· ≤ ·)` packaged as a `Rel Nat Nat`. **Predict**
> whether `3` and `5` are related, then check (using `≤` directly).
@@@ -/

#eval decide ((3 : Nat) ≤ 5)   -- predict first (lePair 3 5)

/-! @@@
## 10.5  Properties of relations

Key relational properties are propositions.  We state each as a type
so that checking a relation has the property means inhabiting the type.
@@@ -/

-- Reflexive: every element is related to itself
def RelReflexive (r : Rel α α) : Prop := ∀ a, r a a

-- Symmetric: if a is related to b then b is related to a
def RelSymmetric (r : Rel α α) : Prop := ∀ a b, r a b → r b a

-- Transitive: r a b and r b c implies r a c
def RelTransitive (r : Rel α α) : Prop := ∀ a b c, r a b → r b c → r a c

-- An equivalence relation satisfies all three:
def Equivalence' (r : Rel α α) : Prop :=
  RelReflexive r ∧ RelSymmetric r ∧ RelTransitive r

-- ≤ on Nat is reflexive and transitive but not symmetric:
example : RelReflexive (· ≤ · : Rel Nat Nat) :=
  fun a => Nat.le_refl a

example : RelTransitive (· ≤ · : Rel Nat Nat) :=
  fun _ _ _ => Nat.le_trans

example : ¬ RelSymmetric (· ≤ · : Rel Nat Nat) :=
  fun h => absurd (h 0 1 (Nat.zero_le 1)) (by decide)

-- = on Nat is an equivalence relation:
example : Equivalence' (· = · : Rel Nat Nat) :=
  ⟨fun _ => rfl,
   fun _ _ h => h.symm,
   fun _ _ _ h1 h2 => h1.trans h2⟩

/-! @@@
> **Checkpoint — reflexivity.** `RelReflexive r` is `∀ a, r a a`; over all `Nat` it is not
> decidable, but any single instance is. **Predict** the reflexivity instance `3 ≤ 3`, then check.
@@@ -/

#eval decide ((3 : Nat) ≤ 3)   -- predict first

/-! @@@
> **Checkpoint — symmetry fails for `≤`.** Symmetry would need `r a b → r b a` for *all*
> `a, b`. **Predict** the witness that breaks it — `0 ≤ 1` holds but `1 ≤ 0` does not —
> then check.
@@@ -/

#eval decide ((0 : Nat) ≤ 1 ∧ ¬ ((1 : Nat) ≤ 0))   -- predict first (a counterexample to symmetry)

/-! @@@
> **Checkpoint — transitivity.** `RelTransitive r` needs `r a b → r b c → r a c`. **Predict**
> this instance chaining `1 ≤ 2` and `2 ≤ 3`, then check.
@@@ -/

#eval decide (((1 : Nat) ≤ 2) → ((2 : Nat) ≤ 3) → ((1 : Nat) ≤ 3))   -- predict first

/-! @@@
> **Checkpoint — equivalence (`=`).** `=` on `Nat` is reflexive, symmetric, and transitive.
> **Predict** this bundle — `2 = 2` and (`2 = 3 → 3 = 2`) — then check.
@@@ -/

#eval decide ((2 : Nat) = 2 ∧ ((2 : Nat) = 3 → (3 : Nat) = 2))   -- predict first

/-! @@@
## 10.6  Relational composition and image

*Composition* of relations: `r` composed with `s` relates `a` to `c`
if there exists a `b` such that `r a b` and `s b c`.

*Image* of a set under a relation: the set of all elements reachable
from `s` by following `r`.
@@@ -/

-- Relational composition:
def relComp (r : Rel α β) (s : Rel β γ) : Rel α γ :=
  fun a c => ∃ b, r a b ∧ s b c

/-! @@@
> **Checkpoint — relational composition.** `relComp (· ≤ ·) (· ≤ ·) 1 3` is `∃ b, 1 ≤ b ∧ b ≤ 3`.
> The `∃` over `Nat` is not decidable, but a *witness* settles it. **Predict** whether `b = 2`
> works — `1 ≤ 2 ∧ 2 ≤ 3` — then check.
@@@ -/

#eval decide (((1 : Nat) ≤ 2) ∧ ((2 : Nat) ≤ 3))   -- predict first (b = 2 witnesses relComp)

-- Image of a set under a function (as a relation):
#check @Set.image
-- Set.image : (α → β) → Set α → Set β
-- (Set.image f s) b ↔ ∃ a ∈ s, f a = b

-- Preimage:
#check @Set.preimage
-- Set.preimage : (α → β) → Set β → Set α
-- (Set.preimage f t) a ↔ f a ∈ t

-- Image of the universal set is the range:
theorem image_univ (f : α → β) :
    Set.image f Set.univ = Set.range f :=
  Set.image_univ

/-! @@@
> **Checkpoint — image / range.** `b ∈ Set.image f s` means `∃ a ∈ s, f a = b`, and
> `image f univ = range f`. A witness `a` settles one such membership. **Predict** whether
> `6` lies in the image of `(· * 2)` because `3 ↦ 6`, i.e. that `(· * 2) 3 = 6`, then check.
@@@ -/

#eval decide ((fun (x : Nat) => x * 2) 3 = 6)   -- predict first (3 ↦ 6, so 6 ∈ image)

/-! @@@
## 10.7  Functions as total relations

A function `f : α → β` determines a *functional relation*: the set of
pairs `{(a, f a) | a : α}`.  A relation is *functional* if every element
of the domain is related to exactly one element of the codomain.

Sets and relations are the language in which we write specifications for
programs dealing with collections of data.  The Dict type class (Week 11)
is a partial function — a relation where each key relates to at most one
value.  Sorting is about relations between the input and output lists.
@@@ -/

/-! @@@
> **Checkpoint — functional relation.** A function `f` induces the relation
> `fun a b => f a = b`, in which each input relates to *exactly one* output. **Predict**
> whether `2` relates to `4` under `(· * 2)`, i.e. that `(· * 2) 2 = 4`, then check.
@@@ -/

#eval decide ((fun (x : Nat) => x * 2) 2 = 4)   -- predict first

/-! @@@
## Exercises

Each exercise carries a banner — `[id] · competency · tier · level · target` — and,
where it asks you to build something, an **acceptance check**: paste it beneath your
definition in your own file and it must succeed.  `#guard` is silent on success and
errors on failure, so the compiler is your grader.  See `EXERCISE_CONVENTIONS.md` for
the schema.  Do every **core** exercise; **stretch** exercises go deeper and are
optional.

---

**[E10.1]** · *specification writing* · tier 1 (+ tier-3 reading) · **core** · target `DeMorganInterSpec`

State, as a `Prop`, De Morgan's law for intersection: *"for all sets `s t` and every `x`,
`x ∈ (s ∩ t)ᶜ ↔ x ∈ sᶜ ∪ tᶜ`."*  Do **not** prove the general statement — that proof is
`Set.compl_inter` (§10.3 provides the union form `Set.compl_union`; read it, tier 3).
Confirm the spec on concrete sets, covering an element in **both**, in **neither**, and in
**exactly one**:

```lean
-- def DeMorganInterSpec : Prop :=
--   ∀ (s t : Set Nat) (x : Nat), x ∈ (s ∩ t)ᶜ ↔ x ∈ sᶜ ∪ tᶜ
#guard decide ((2 : Nat) ∈ ((({1,2} ∩ {2,3}) : Set Nat)ᶜ) ↔ (2 : Nat) ∈ ((({1,2} : Set Nat)ᶜ) ∪ (({2,3} : Set Nat)ᶜ)))   -- 2 in both
#guard decide ((5 : Nat) ∈ ((({1,2} ∩ {2,3}) : Set Nat)ᶜ) ↔ (5 : Nat) ∈ ((({1,2} : Set Nat)ᶜ) ∪ (({2,3} : Set Nat)ᶜ)))   -- 5 in neither
#guard decide ((1 : Nat) ∈ ((({1,2} ∩ {2,3}) : Set Nat)ᶜ) ↔ (1 : Nat) ∈ ((({1,2} : Set Nat)ᶜ) ∪ (({2,3} : Set Nat)ᶜ)))   -- 1 in exactly one
```

In one line: which tier does the *general* statement live in, and which the three checks?

---

**[E10.2]** · *decidability identification* · tier 1 · **core**

For each proposition, say **whether `decide` can close it and why** — a *finite literal
set* is decidable, but `⊆` and an unbounded `∀` both range over *all* of `Nat` — the
judgment is the point, not the tool-use.  *Then* check only the decidable ones:

(a) `(3 : Nat) ∈ ({1, 2, 3} : Set Nat)`
(b) `({1, 2} : Set Nat) ⊆ {1, 2, 3}`
(c) `∀ a : Nat, a ≤ a`
(d) `(1 : Nat) ∈ (({1, 2} ∪ {3}) : Set Nat)`

```lean
#guard decide ((3 : Nat) ∈ ({1, 2, 3} : Set Nat)) = true
#guard decide ((1 : Nat) ∈ (({1, 2} ∪ {3}) : Set Nat)) = true
-- (b) and (c) have no check on purpose: say why decide cannot close each
--     (both quantify over every Nat, not over a finite literal set).
```

---

**[E10.3]** · *counterexample finding* · tier 1 · **core**

A student claims *"`divides` is symmetric: if `m` divides `n` then `n` divides `m`."*  It
is **wrong**.  On `Nat`, `divides m n` (`∃ k, n = m * k`, §10.4) is exactly `m ∣ n`.  Find a
witness where one direction holds and the other fails, and encode it as the fact that
**must hold**, so the check **succeeds**:

```lean
#guard decide ((3 : Nat) ∣ 12 ∧ ¬ ((12 : Nat) ∣ 3)) = true
#guard decide (¬ ((2 : Nat) ∣ 3)) = true
```

Which single property of `≤` (§10.5) also fails, with the *same shape* of witness?

---

**[E10.4]** · *type-directed derivation* · tier 2 · **core** · target `converseB`

Derive `converseB : (α → β → Bool) → (β → α → Bool)`, the *converse* of a Boolean relation
— swap the two arguments (cf. the `Rel` converse behind symmetry, §10.5).  Produce a
**derivation trace** in the Week 2 §2.6 format — the trace is the graded artifact — then
the `def`.  *First-step hint:* the result type is `β → α → Bool`, so introduce the relation
`r`, then `b : β`, then `a : α`; only `r a b` type-checks as the body.  Effort: ~3 trace
steps, 1 line of code.

```lean
#guard converseB (fun a b => decide (a ≤ b)) 5 3 = true    -- swaps to decide (3 ≤ 5)
#guard converseB (fun a b => decide (a ≤ b)) 3 5 = false   -- swaps to decide (5 ≤ 3)
#guard converseB (fun a b => a == b) 2 (2 : Nat) = true
```

---

**[E10.5]** · *specification writing + decidability identification* · tier 1 · **stretch** · target `IsOrder`

State, as a `Prop`, what it means for `r : Rel Nat Nat` to be an *order*: reflexive,
transitive, and **antisymmetric** (`∀ a b, r a b → r b a → a = b`).  Do not prove the
general claim for `≤`; instead confirm each of the three clauses on concrete `Nat`
instances — antisymmetry holds *vacuously* when the two `≤`s cannot both point the
same way:

```lean
-- def IsOrder (r : Rel Nat Nat) : Prop :=
--   (∀ a, r a a) ∧ (∀ a b c, r a b → r b c → r a c) ∧ (∀ a b, r a b → r b a → a = b)
#guard decide ((3 : Nat) ≤ 3) = true                                         -- reflexive instance
#guard decide (((1 : Nat) ≤ 2) → ((2 : Nat) ≤ 5) → ((1 : Nat) ≤ 5)) = true   -- transitive instance
#guard decide (((2 : Nat) ≤ 3) → ((3 : Nat) ≤ 2) → (2 : Nat) = 3) = true     -- antisymmetric instance
```

Why is the general `IsOrder (· ≤ ·)` statement itself **not** `decide`-checkable?

---

**[E10.6]** · *type reading (free theorems)* · tier 2 · **stretch**

Look **only** at the type of `relComp`, namely `Rel α β → Rel β γ → Rel α γ`, polymorphic
in `α`, `β`, `γ`.  Without running anything, state two things *every* inhabitant must
respect (can it manufacture a bridging `b : β` out of nowhere?  can it inspect the elements
it threads through?) and one thing the type *forbids*.  This is the inverse of E10.4 and
echoes the free theorems of Week 7 (§7.2).  No code to submit.
---

**[E10.7]** · *specification writing + decidability identification* · tier 1 · **stretch** · target `IsPrefix`

Define the relation `IsPrefix : Rel (List α) (List α)` — `xs` is a prefix of `ys` when some
`zs` extends it:

```lean
def IsPrefix (xs ys : List α) : Prop := ∃ zs, xs ++ zs = ys
```

Using the §10.4 vocabulary (`RelReflexive`, `RelTransitive`), state — do not prove — that
`IsPrefix` is reflexive and transitive.  *Hint for reflexivity:* which `zs` witnesses
`xs ++ zs = xs`?  The bare `∃ zs` ranges over an unbounded domain, so `decide` cannot close
it; check instances through the decidable Boolean `List.isPrefixOf` instead, and say in one
line why that one computes while the `∃` does not:

```lean
#guard ([1, 2] : List Nat).isPrefixOf [1, 2, 3]
#guard ([] : List Nat).isPrefixOf [1, 2, 3]
#guard ([1, 2, 3] : List Nat).isPrefixOf [1, 2, 3]   -- reflexivity, on an instance
#guard !(([2, 3] : List Nat).isPrefixOf [1, 2, 3])
```

---

**[E10.8]** · *specification reading + counterexample finding* · tier 3 (reading) + tier 1 · **stretch**

State the specification *"the image of `s ∩ t` under `f` is a subset of
`Set.image f s ∩ Set.image f t`."*  This is Mathlib's `Set.image_inter_subset`, whose type is
`f '' (s ∩ t) ⊆ f '' s ∩ f '' t` — look it up and read it.  Then explain in two or three
sentences why this is only a **subset** and not an equality, exhibit concrete `f`, `s`, `t`
over `Nat` for which the two sides genuinely differ, and name the property of `f` that would
buy you the reverse inclusion.  No code to submit.

@@@ -/

end W10
