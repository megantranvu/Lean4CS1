-- FPCourse/T03_HigherOrderAndSpecification/W09_Specifications.lean
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Pairwise

open scoped List

/-! @@@
# Specifications in Practice

## What is a correct sort?

Sorting is one of the most studied problems in computer science, yet
most textbooks define correctness informally.  We will define it
precisely as a type.

A correct sorting function must satisfy two independent conditions:
1. **Sorted output**: the result list is in non-decreasing order.
2. **Permutation**: the result contains exactly the same elements as
   the input, in the same multiplicity.

Both conditions are needed.  Without "sorted": returning the empty list
or a constant list would satisfy "permutation" alone.  Without "permutation":
returning `[]` would satisfy "sorted" alone.

Together, they express exactly what we mean by "correctly sorts."
@@@ -/

namespace W09

-- List.Sorted is now List.Pairwise in Lean 4.28 / Mathlib
abbrev List.Sorted (r : α → α → Prop) (xs : List α) : Prop := List.Pairwise r xs

/-! @@@
## 9.1  The Sorted predicate

`List.Sorted r xs` holds iff every adjacent pair in `xs` satisfies `r`.
We use `(· ≤ ·)` for ascending order.
@@@ -/

-- Sorted is now an alias for List.Pairwise:
#check @List.Pairwise   -- (r : α → α → Prop) → List α → Prop

-- Examples — use decide on concrete lists:
example : List.Sorted (· ≤ ·) ([1, 2, 3, 4] : List Nat) := by decide
example : ¬ List.Sorted (· ≤ ·) ([1, 3, 2] : List Nat) := by decide
example : List.Sorted (· ≤ ·) ([] : List Nat) := by decide   -- vacuously

/-! @@@
> **Checkpoint — `Sorted`.** `List.Sorted (· ≤ ·)` holds iff every adjacent pair is
> non-decreasing. **Predict** the Boolean below — is `[1, 2, 3, 4]` in order? — then check.
@@@ -/

#eval decide (List.Sorted (· ≤ ·) ([1, 2, 3, 4] : List Nat))   -- predict first

/-! @@@
## 9.2  The Perm predicate

`List.Perm xs ys` (written `xs ~ ys`) holds iff `xs` is a permutation
of `ys`.  Equivalently: both lists contain the same elements with the
same multiplicities.
@@@ -/

#check @List.Perm   -- List α → List α → Prop

-- Examples:
example : ([1, 2, 3] : List Nat) ~ [3, 1, 2] := by decide
example : ([1, 2, 3] : List Nat) ~ [1, 2, 3] := List.Perm.refl _
example : ¬ ([1, 2] : List Nat) ~ [1, 2, 3] := by decide

-- Perm is symmetric, transitive, and congruent with respect to cons.
theorem perm_symm (xs ys : List α) : xs ~ ys → ys ~ xs :=
  List.Perm.symm

/-! @@@
> **Checkpoint — `Perm`.** `xs ~ ys` holds iff the two lists have the same elements with
> the same multiplicities (order aside). **Predict** the Boolean below — is `[1, 2, 3]` a
> rearrangement of `[3, 1, 2]`? — then check.
@@@ -/

#eval decide (([1, 2, 3] : List Nat) ~ [3, 1, 2])   -- predict first

/-! @@@
## 9.3  The CorrectSort specification

This is the heart of the week: a single type that captures what it means
for a function to be a correct sorting function.
@@@ -/

-- Read aloud: "for every list xs of Nat,
--   (sort xs is sorted) AND (sort xs is a permutation of xs)"
-- The ∀ quantifies over all possible inputs.
-- The ∧ bundles the two conditions that must BOTH hold.
def CorrectSort (sort : List Nat → List Nat) : Prop :=
  ∀ xs : List Nat,
    List.Sorted (· ≤ ·) (sort xs) ∧   -- output is sorted
    sort xs ~ xs                        -- output is a permutation of input

/-! @@@
> **Checkpoint — `CorrectSort` needs BOTH conjuncts.** The constant-empty function
> `fun _ => []` returns a sorted list but *loses* elements. **Predict** the Boolean below
> — which of the two conjuncts fails on input `[1]`? — then check that the bundle is `false`.
@@@ -/

#eval decide (List.Sorted (· ≤ ·) ([] : List Nat) ∧ (([] : List Nat) ~ [1]))   -- predict first

/-! @@@
## 9.4  Insertion sort: implementation

Insertion sort inserts each element of the input into the correct
position in an already-sorted list.
@@@ -/

def insert' (x : Nat) : List Nat → List Nat
  | []      => [x]
  | h :: t  => if x ≤ h then x :: h :: t else h :: insert' x t

/-! @@@
> **Checkpoint — `insert'`.** `insert'` drops `x` into an already-sorted list at the first
> position where `x ≤ h`. **Predict** the result of inserting `4` into `[1, 3, 5]` before
> reading it.
@@@ -/

#eval insert' 4 [1, 3, 5]   -- predict first

def insertionSort : List Nat → List Nat
  | []      => []
  | h :: t  => insert' h (insertionSort t)

#eval insertionSort [5, 3, 1, 4, 2]    -- [1, 2, 3, 4, 5]
#eval insertionSort []                  -- []

/-! @@@
> **Checkpoint — `insertionSort`.** `insertionSort` folds `insert'` over the input, one
> element at a time. **Predict** its output on `[3, 1, 2]` — what does insertion sort always
> return? — then check.
@@@ -/

#eval insertionSort [3, 1, 2]   -- predict first

/-! @@@
## 9.5  Proving CorrectSort — provided term-mode proofs

Proving `CorrectSort insertionSort` requires two sub-proofs.  Both
are provided here as term-mode proofs for you to read.

**Helper 1**: inserting preserves the permutation relation — `insert' x xs` is a
permutation of `x :: xs`.  Both `insert_sorted` (Helper 2) and `insertionSort_perm`
(Helper 4) reuse this single lemma.
@@@ -/

theorem insert_perm (x : Nat) :
    ∀ xs : List Nat, insert' x xs ~ x :: xs
  | []      => List.Perm.refl _
  | h :: t  => by
    simp only [insert']
    split_ifs with hle
    · exact List.Perm.refl _
    · exact List.Perm.trans
        (List.Perm.cons h (insert_perm x t))
        (List.Perm.swap x h t)

/-! @@@
> **Checkpoint — `insert_perm`.** The provided proof guarantees: `insert' x xs` is a
> permutation of `x :: xs` (nothing added or lost). **Predict** the Boolean below, then check.
@@@ -/

#eval decide (insert' 4 [1, 3, 5] ~ 4 :: [1, 3, 5])   -- predict first

/-! @@@
**Helper 2**: inserting into a sorted list produces a sorted list.
@@@ -/

theorem insert_sorted (x : Nat) :
    ∀ xs : List Nat, List.Sorted (· ≤ ·) xs →
      List.Sorted (· ≤ ·) (insert' x xs)
  | [], _ => List.pairwise_singleton (· ≤ ·) x
  | h :: t, hst => by
    simp only [insert']
    split_ifs with hle
    · -- x ≤ h: insert x at front
      apply List.Pairwise.cons
      · intro y hy
        simp only [List.mem_cons] at hy
        cases hy with
        | inl heq =>
          exact heq ▸ hle
        | inr hmem =>
          exact Nat.le_trans hle ((List.pairwise_cons.mp hst).1 y hmem)
      · exact hst
    · -- x > h: insert into tail
      have hxh : h ≤ x := Nat.le_of_not_le hle
      apply List.Pairwise.cons
      · intro y hy
        have : y ∈ x :: t := (insert_perm x t).subset hy
        simp only [List.mem_cons] at this
        cases this with
        | inl heq => exact heq ▸ hxh
        | inr hmem => exact (List.pairwise_cons.mp hst).1 y hmem
      · exact insert_sorted x t (List.pairwise_cons.mp hst).2

/-! @@@
> **Checkpoint — `insert_sorted`.** The provided proof guarantees: insert into a sorted
> list, stay sorted. **Predict** the Boolean below — is `insert' 4 [1, 3, 5]` sorted? — then
> check that the theorem's conclusion holds on this instance.
@@@ -/

#eval decide (List.Sorted (· ≤ ·) (insert' 4 [1, 3, 5]))   -- predict first

/-! @@@
**Helper 3**: insertion sort produces a sorted list.
@@@ -/

theorem insertionSort_sorted :
    ∀ xs : List Nat, List.Sorted (· ≤ ·) (insertionSort xs)
  | []      => List.Pairwise.nil
  | h :: t  => insert_sorted h (insertionSort t) (insertionSort_sorted t)

/-! @@@
> **Checkpoint — `insertionSort_sorted`.** This chains `insert_sorted` down the recursion,
> so every output is sorted. **Predict** the Boolean below, then check.
@@@ -/

#eval decide (List.Sorted (· ≤ ·) (insertionSort [5, 3, 1, 4, 2]))   -- predict first

/-! @@@
**Helper 4**: insertion sort is a permutation.
@@@ -/

theorem insertionSort_perm :
    ∀ xs : List Nat, insertionSort xs ~ xs
  | []      => List.Perm.refl _
  | h :: t  =>
    List.Perm.trans
      (insert_perm h (insertionSort t))
      (List.Perm.cons h (insertionSort_perm t))

/-! @@@
> **Checkpoint — `insertionSort_perm`.** This chains `insert_perm` down the recursion, so
> the output always has exactly the input's elements. **Predict** the Boolean below, then check.
@@@ -/

#eval decide (insertionSort [5, 3, 1, 4, 2] ~ [5, 3, 1, 4, 2])   -- predict first

/-! @@@
**Main theorem**: insertion sort is correct.
@@@ -/

theorem insertionSort_correct : CorrectSort insertionSort :=
  fun xs => ⟨insertionSort_sorted xs, insertionSort_perm xs⟩

/-! @@@
> **Checkpoint — `insertionSort_correct`.** The main theorem simply *pairs* the two helpers
> `⟨sorted, perm⟩`. **Predict** the Boolean below — both conjuncts hold on `[4, 2, 3, 1]` —
> then check.
@@@ -/

#eval decide (List.Sorted (· ≤ ·) (insertionSort [4, 2, 3, 1]) ∧ insertionSort [4, 2, 3, 1] ~ [4, 2, 3, 1])   -- predict first

/-! @@@
## 9.6  Verifying on concrete instances

Because `Sorted` and `Perm` are decidable on `List Nat`, we can check
correctness on concrete examples with `decide`.
@@@ -/

example : List.Sorted (· ≤ ·) (insertionSort [3, 1, 4, 1, 5, 9]) := by decide
example : insertionSort [3, 1, 4, 1, 5] ~ [3, 1, 4, 1, 5] := by decide

/-! @@@
> **Checkpoint — decidable verification on instances.** `Perm` on `List Nat` is decidable,
> so `decide` settles it — and it tracks *multiplicity*, not just membership. **Predict** the
> Boolean below (note the repeated `1`), then check.
@@@ -/

#eval decide (insertionSort [3, 1, 4, 1, 5, 9] ~ [3, 1, 4, 1, 5, 9])   -- predict first

/-! @@@
## 9.7  Specifications with pre- and postconditions

A more general specification pattern uses explicit pre- and postconditions
attached to function types.  This is the proof-carrying type pattern
generalized.
@@@ -/

-- A function with a precondition in its type:
def sortedMerge
    (xs ys : List Nat)
    (_hxs : List.Sorted (· ≤ ·) xs)
    (_hys : List.Sorted (· ≤ ·) ys) :
    { zs : List Nat // List.Sorted (· ≤ ·) zs ∧ zs ~ xs ++ ys } :=
  -- Implementation omitted; the TYPE is the specification.
  -- Any implementation must produce a Σ-type (subtype) carrying the proof.
  ⟨(xs ++ ys).mergeSort (· ≤ ·),
   ⟨List.pairwise_mergeSort' (· ≤ ·) (xs ++ ys),
    List.mergeSort_perm (xs ++ ys) (· ≤ ·)⟩⟩

/-! @@@
> **Checkpoint — the postcondition value.** `sortedMerge`'s subtype `{ zs // Sorted zs ∧ zs
> ~ xs ++ ys }` is *carried by the value* `(xs ++ ys).mergeSort (· ≤ ·)`. **Predict** what
> that value computes for `[1, 3] ++ [2, 4]`, then check.
@@@ -/

#eval (([1, 3] ++ [2, 4] : List Nat)).mergeSort (· ≤ ·)   -- predict first

/-! @@@
## Exercises

Each exercise carries a banner — `[id] · competency · tier · level · target` — and,
where it asks you to build something, an **acceptance check**: paste it beneath your
definition in your own file and it must succeed.  `#guard` is silent on success and
errors on failure, so the compiler is your grader.  See `EXERCISE_CONVENTIONS.md` for
the schema.  Do every **core** exercise; **stretch** exercises go deeper and are
optional.

---

**[E9.1]** · *specification reading* · tier 1 · **core**

`CorrectSort` (§9.3) demands **both** `Sorted` *and* `Perm`; §9.3 argued each is needed
because a bogus sorter can satisfy one alone.  Make that concrete.  For the two bogus
sorters below, say **which single conjunct each violates**, then encode the witnesses so
every check **succeeds** (each is decidable on `List Nat`):

```lean
-- `fun _ => []` : sorted, but NOT a permutation of a non-empty input →
#guard List.Sorted (· ≤ ·) ([] : List Nat)
#guard decide (¬ (([] : List Nat) ~ [1, 2])) = true
-- `id` : a permutation, but NOT always sorted →
#guard ([3, 1, 2] : List Nat) ~ [3, 1, 2]
#guard decide (¬ List.Sorted (· ≤ ·) ([3, 1, 2] : List Nat)) = true
```

In one line: which conjunct fails for `fun _ => []`, and which for `id`?

---

**[E9.2]** · *specification writing* · tier 1 · **core** · target `dedup`

Define `dedup : List Nat → List Nat` that removes duplicate elements, and state its
specification `DedupSpec : Prop` — *"the result has no duplicates, and it has exactly the
elements of the input."*  You need not prove `DedupSpec`; confirm it on instances with
decidable, order-independent checks (any correct implementation passes):

```lean
#guard (dedup [1, 1, 2, 3, 3, 3]).Nodup
#guard decide (∀ x ∈ ([1, 1, 2, 3, 3, 3] : List Nat), x ∈ dedup [1, 1, 2, 3, 3, 3]) = true
#guard dedup ([] : List Nat) = []
```

*First-step hint:* recurse on the list; on `h :: t`, test `h ∈ t` (decidable, `Nat` has
`DecidableEq`) to decide whether to keep `h`.  Effort: ~4 lines.

---

**[E9.3]** · *counterexample finding* · tier 1 · **core** · target `CorrectSortDesc`

Define `CorrectSortDesc` — `CorrectSort` but for **descending** order, i.e.
`List.Sorted (· ≥ ·)` in place of `(· ≤ ·)`.  Insertion sort does **not** satisfy it.
Find an input on which the output is not `(· ≥ ·)`-sorted, and encode the witness so the
check **succeeds** (a correct counterexample makes the negation `true`):

```lean
#guard decide (¬ List.Sorted (· ≥ ·) (insertionSort [2, 1, 3])) = true
#guard List.Sorted (· ≥ ·) ([3, 2, 1] : List Nat)   -- what a descending-sorted list looks like
```

In one line: which conjunct of `CorrectSortDesc` does `insertionSort` break, and which
does it still satisfy?

---

**[E9.4]** · *specification reading* · tier 3 · **core**

Read the **provided** proof of `insertionSort_correct` (§9.5) — do **not** write a proof.
In prose, answer: (a) `insertionSort_correct` is `fun xs => ⟨_, _⟩`; what are the two
components, and which conjunct of `CorrectSort` does each discharge?  (b) `insertionSort_sorted`
depends on `insert_sorted`, and `insertionSort_perm` on `insert_perm`; explain in one
sentence each what property of `insert'` the two helpers establish, and why the recursion
needs them.  (c) The `[]` case of `insertionSort_sorted` is `List.Pairwise.nil`; why is the
empty list vacuously sorted?  No code to submit.

---

**[E9.5]** · *decidability identification* · tier 1 · **stretch**

For each proposition, say **whether `decide` can close it and why** (finite domain?
decidable predicate?) *before* checking — the judgment is the point, not the tool-use:

(a) `List.Sorted (· ≤ ·) (insertionSort [9, 1, 3, 7, 2, 6])`
(b) `insertionSort [3, 1, 2] ~ [3, 1, 2]`
(c) `CorrectSort insertionSort`

```lean
#guard decide (List.Sorted (· ≤ ·) (insertionSort [9, 1, 3, 7, 2, 6])) = true
#guard decide (insertionSort [3, 1, 2] ~ [3, 1, 2]) = true
-- (c) has no check on purpose: say why `decide` cannot close `CorrectSort insertionSort`,
--     and name the term that settles it instead (hint: it is in §9.5).
```

---

**[E9.6]** · *type-directed derivation* · tier 2 (+ tier-3 reading) · **stretch** · target `correctSorter`

The subtype `{ f : List Nat → List Nat // CorrectSort f }` is a *proof-carrying* type: an
inhabitant bundles a sorting function **with** a proof it is correct.  Build one inhabitant,
`correctSorter`, by **reusing** the provided term `insertionSort_correct` (§9.5) as the
proof component — you author no proof:

```lean
-- def correctSorter : { f : List Nat → List Nat // CorrectSort f } :=
--   ⟨insertionSort, insertionSort_correct⟩
#guard (correctSorter.val [4, 2, 3, 1] : List Nat) = [1, 2, 3, 4]
#guard (correctSorter.val ([] : List Nat)) = []
```

*First-step hint:* the anonymous constructor `⟨_, _⟩` for a subtype takes the value then
its proof; the value is `insertionSort`, the proof is already proved for you.  In one line:
what does `.val` project out, and what guarantee did the second component add to the type?
@@@ -/

end W09
