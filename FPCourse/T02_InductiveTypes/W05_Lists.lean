-- FPCourse/T02_InductiveTypes/W05_Lists.lean
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas

/-! @@@
# Lists

## Lists as the canonical inductive type

`List α` is defined inductively:
- `[]` (nil) — the empty list
- `h :: t` (cons) — a head element `h : α` followed by a tail `t : List α`

Every function on lists follows this structure: one clause for `[]`, one
clause for `h :: t` (which may recurse on `t`).

The specifications for list functions are propositions that quantify over
all lists.  Some of these propositions are decidable — when the element
type has `DecidableEq` and the list is finite, we can check them with
`decide`.
@@@ -/

namespace W05

/-! @@@
## 5.1  Standard list functions and their specifications

The specifications below are ALL provided as term-mode proofs.
Read them; understand the proposition being stated; observe how the
proof term mirrors the function definition.
@@@ -/

-- Length
theorem length_nil : ([] : List α).length = 0 := rfl
theorem length_cons (h : α) (t : List α) :
    (h :: t).length = t.length + 1 := rfl

-- Append
theorem append_nil (xs : List α) : xs ++ [] = xs :=
  List.append_nil xs

theorem nil_append (xs : List α) : [] ++ xs = xs :=
  List.nil_append xs

theorem append_assoc (xs ys zs : List α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
  List.append_assoc xs ys zs

-- Length distributes over append
theorem length_append (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length :=
  List.length_append

-- Membership and append: ∈ distributes over ++
theorem mem_append_iff (a : α) (xs ys : List α) :
    a ∈ xs ++ ys ↔ a ∈ xs ∨ a ∈ ys :=
  List.mem_append

/-! @@@
> **Checkpoint — specifications of `++`.** Using `length_append` and `mem_append_iff`
> (not evaluation), **predict** both values below, then check.
@@@ -/

#eval (([1, 2, 3] ++ [4, 5] : List Nat)).length          -- predict from length_append
#eval decide (3 ∈ (([1, 2, 3] ++ [4, 5]) : List Nat))    -- predict from mem_append_iff

/-! @@@
## 5.2  Decide on finite lists

When the element type has `DecidableEq`, propositions of the form
`∀ x ∈ xs, P x` are decidable for finite `xs` (when `P` is decidable).
This means `decide` can verify them automatically.
@@@ -/

-- Evaluation: `decide` checks finite-list claims by evaluating the predicate
-- on each element in turn.  ∀ x ∈ [2,4,6,8], x%2=0 becomes:
--   2%2=0 ↝ true,  4%2=0 ↝ true,  6%2=0 ↝ true,  8%2=0 ↝ true  ✓
example : ∀ x ∈ ([2, 4, 6, 8] : List Nat), x % 2 = 0 := by decide
example : ∀ x ∈ ([1, 3, 5, 7] : List Nat), x % 2 = 1 := by decide
example : ∃ x ∈ ([10, 20, 30] : List Nat), x > 15    := by decide

-- Membership in a concrete list:
example : 3 ∈ ([1, 2, 3, 4] : List Nat) := by decide
example : ¬ (5 ∈ ([1, 2, 3, 4] : List Nat)) := by decide

-- Equality of concrete lists:
example : ([1, 2] ++ [3, 4] : List Nat) = [1, 2, 3, 4] := by decide

/-! @@@
> **Checkpoint — `decide` on finite lists.** Before evaluating, **predict** the Boolean,
> and say *why* `decide` can settle it (finite list, decidable predicate).  Then check.
@@@ -/

#eval decide (∀ x ∈ ([2, 4, 7] : List Nat), x % 2 = 0)   -- predict first (note the 7)

/-! @@@
## 5.3  Reverse and the auxiliary lemma pattern

`reverse` is defined recursively.  Its specification — that reversing
twice returns the original list — requires a helper lemma about how
`reverse` interacts with `++`.

This illustrates a general pattern: when a direct proof gets stuck,
look at what the inductive step requires and name it as a separate lemma.
The provided proofs below demonstrate this pattern explicitly.
@@@ -/

theorem reverse_append (xs ys : List α) :
    (xs ++ ys).reverse = ys.reverse ++ xs.reverse :=
  List.reverse_append

theorem reverse_reverse (xs : List α) : xs.reverse.reverse = xs :=
  List.reverse_reverse xs

-- The proof of reverse_reverse in Mathlib uses reverse_append.
-- The dependency is: reverse_reverse requires reverse_append,
-- which in turn requires nil_append and append_assoc.
-- Each lemma is proved by structural recursion on the first list.

/-! @@@
> **Checkpoint — `reverse`.** Using `reverse_reverse` (not evaluation), **predict** the
> second value; predict the first from what `reverse` does.  Then check.
@@@ -/

#eval ([1, 2, 3].reverse : List Nat)           -- predict
#eval ([1, 2, 3].reverse.reverse : List Nat)   -- predict from reverse_reverse

/-! @@@
## 5.4  Map and its specification

`List.map f` applies `f` to every element.  Its specification:
1. Map preserves length.
2. Map distributes over append.
3. Mapping the identity function is the identity on lists.
4. Mapping a composition equals composing two maps.
@@@ -/

theorem map_length (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length :=
  List.length_map f

theorem map_append (f : α → β) (xs ys : List α) :
    (xs ++ ys).map f = xs.map f ++ ys.map f :=
  List.map_append

theorem map_id_eq (xs : List α) : xs.map id = xs :=
  List.map_id xs

theorem map_comp (f : β → γ) (g : α → β) (xs : List α) :
    xs.map (f ∘ g) = (xs.map g).map f := by
  simp [← List.map_map]

/-! @@@
> **Checkpoint — `map` preserves length.** Use `map_length` (not evaluation) to
> **predict** the value below, then check it.
@@@ -/

#eval ([1, 2, 3, 4].map (· + 100)).length   -- predict from the spec, then read

/-! @@@
## 5.5  Specifications students should practice writing

Reading a specification is easier than writing one.  The following are
propositions about list functions.  Practice writing them yourself,
then check against these.

"filter keeps exactly the elements satisfying the predicate":
@@@ -/

-- ∀ x, x ∈ filter p xs ↔ x ∈ xs ∧ p x = true
theorem mem_filter_iff (p : α → Bool) (xs : List α) (x : α) :
    x ∈ xs.filter p ↔ x ∈ xs ∧ p x = true :=
  List.mem_filter

-- "length of filter is at most length of input"
theorem filter_length_le (p : α → Bool) (xs : List α) :
    (xs.filter p).length ≤ xs.length :=
  List.length_filter_le p xs

/-! @@@
> **Checkpoint — `filter`.** Using `mem_filter_iff` and `filter_length_le`, **predict**
> the filtered list and its length (note it is ≤ 6), then check.
@@@ -/

#eval ([1, 2, 3, 4, 5, 6].filter (· % 2 == 0) : List Nat)       -- predict
#eval (([1, 2, 3, 4, 5, 6].filter (· % 2 == 0)).length : Nat)   -- predict; ≤ 6

/-! @@@
## Exercises

Each exercise carries a banner — `[id] · competency · tier · level · target` — and,
where it asks you to build something, an **acceptance check**: paste it beneath your
definition in your own file and it must succeed.  `#guard` is silent on success and
errors on failure, so the compiler is your grader.  See `EXERCISE_CONVENTIONS.md` for
the schema.  Do every **core** exercise; **stretch** exercises go deeper and are
optional.

---

**[E5.1]** · *specification writing* · tier 1 (+ tier-3 reading) · **core** · target `MemAppendSpec`

State, as a `Prop`, the specification *"if `n ∈ xs` then `n ∈ xs ++ ys`."*  Do **not**
prove the general statement — that proof is `List.mem_append`, given in §5.1 for you to
*read* (tier 3).  Instead confirm the spec on instances where the hypothesis holds:

```lean
-- def MemAppendSpec : Prop := ∀ (n : Nat) (xs ys : List Nat), n ∈ xs → n ∈ xs ++ ys
-- 3 ∈ [1,2,3] holds, so the spec predicts:
#guard 3 ∈ (([1, 2, 3] ++ [4, 5]) : List Nat)
#guard 9 ∈ (([9] ++ ([] : List Nat)))
```

In one line: which tier does the *general* statement live in, and which the two checks?

---

**[E5.2]** · *decidability identification* · tier 1 · **core**

For each proposition, say **whether `decide` can close it and why** (finite domain?
decidable predicate?) *before* checking — the judgment is the point, not the tool-use:

(a) `∀ x ∈ ([2,4,6,8,10] : List Nat), x % 2 = 0`
(b) `∃ x ∈ ([3,7,12,5] : List Nat), x > 10`
(c) `∀ xs : List Nat, xs.reverse.reverse = xs`

```lean
#guard ∀ x ∈ ([2, 4, 6, 8, 10] : List Nat), x % 2 = 0
#guard ∃ x ∈ ([3, 7, 12, 5] : List Nat), x > 10
-- (c) has no check on purpose: say why `decide` cannot close it, and name the
--     term that settles it instead (hint: it is in §5.3).
```

---

**[E5.3]** · *counterexample finding* · tier 1 · **core** · target `zipLenCounterexample`

A student proposes this length spec for pairing two lists:
*"`(zip xs ys).length = xs.length + ys.length`."*  It is **wrong**.  Find concrete
inputs witnessing the mismatch and encode the witness so the check **succeeds** (it
confirms the two sides differ).  `List.zip` is in Mathlib.

```lean
#guard (List.zip [1, 2, 3] [10]).length ≠ ([1, 2, 3].length + [10].length)
```

Then state the *correct* length spec in one line (you will build it in E5.5).

---

**[E5.4]** · *type-directed derivation* · tier 2 · **core** · target `headOr`

Derive `headOr : α → List α → α` (return the head, or the default on `[]`).  Produce a
**derivation trace** in the Week 2 §2.6 format — the trace is the graded
artifact — then the `def`.  *First-step hint:* the second argument is a `List α`; its
constructor (`[]` vs `h :: t`) is what you eliminate first (⊕E-style `match`).  Effort:
~4 trace steps, 3 lines of code.

```lean
#guard headOr 0 ([] : List Nat) = 0
#guard headOr 0 [7, 8, 9] = 7
```

---

**[E5.5]** · *inhabitation + specification writing* · tier 1 · **stretch** · target `myZip`

Write `myZip : List α → List β → List (α × β)` pairing corresponding elements and
stopping at the shorter list.  State its length spec as a `Prop`
(`(myZip xs ys).length = min xs.length ys.length`) and confirm on instances.  Effort:
one `match` on both lists at once; ~5 lines.

```lean
#guard myZip [1, 2, 3] ['a', 'b'] = [(1, 'a'), (2, 'b')]
#guard (myZip ([1, 2, 3, 4] : List Nat) ([10, 20] : List Nat)).length = 2   -- min 4 2
#guard (myZip ([] : List Nat) ([1] : List Nat)).length = 0
```

---

**[E5.6]** · *type reading (free theorems)* · tier 2 · **stretch**

Look **only** at the type of `List.map`, namely `(α → β) → List α → List β`, polymorphic
in `α` and `β`.  Without running anything, state two things *every* inhabitant of this
type must do, and one thing it *cannot* do (can it invent a `β` from nowhere?  change
the length?  inspect an `α` it was not handed a function for?).  This is the inverse of
E5.4 and previews the free theorems of Week 7 (§7.2).  No code to submit.
---

**[E5.7]** · *specification writing* · tier 1 (+ tier-3 reading) · **stretch**

State, as a `Prop`, the specification *"mapping after reversing is reversing after
mapping."*  The general statement is Mathlib's `List.map_reverse`, whose type is
`List.map f l.reverse = (List.map f l).reverse` — *read* it (tier 3) rather than proving it.
Confirm the spec on instances, covering the empty and singleton boundaries:

```lean
#guard ([1, 2, 3] : List Nat).reverse.map (· * 10) = (([1, 2, 3] : List Nat).map (· * 10)).reverse
#guard ([] : List Nat).reverse.map (· + 1) = (([] : List Nat).map (· + 1)).reverse
#guard ([7] : List Nat).reverse.map (· + 1) = (([7] : List Nat).map (· + 1)).reverse
```

In one line: which orientation does `List.map_reverse` state, and why does the orientation
matter if you want to use it as a left-to-right rewrite?

@@@ -/

end W05
