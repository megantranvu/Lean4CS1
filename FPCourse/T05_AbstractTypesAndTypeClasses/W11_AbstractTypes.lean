-- FPCourse/T05_AbstractTypesAndTypeClasses/W11_AbstractTypes.lean
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

/-! @@@
# Abstract Types

## Abstraction via type classes

An *abstract type* presents an interface — a collection of operations
with specified types — while hiding the implementation.  Callers program
against the interface; the implementation can change without affecting
callers.

In Lean, type classes express abstract types.  A class declaration is an
interface.  An instance declaration is an implementation.  Laws stated in
the class are the *specification*: propositions that every implementation
must satisfy.

The connection to Week 10: the specification for `Dict` is relational.
A dictionary is a partial function — a relation where each key maps to
at most one value.  The laws of `Dict` are laws of partial functions.
@@@ -/

namespace W11

/-! @@@
## 11.1  The Dict interface

A dictionary maps keys to values.  Operations: empty dict, insert,
lookup, and delete.
@@@ -/

class Dict (d : Type → Type → Type) where
  empty  : d k v
  insert : k → v → d k v → d k v
  lookup : [DecidableEq k] → k → d k v → Option v
  delete : [DecidableEq k] → k → d k v → d k v

/-! @@@
## 11.2  Laws: the specification for Dict

The laws below are propositions that every `Dict` implementation must
satisfy.  They define what it MEANS to be a dictionary.

These are relational specifications in the sense of Week 10: they
describe how the abstract state (a partial function from keys to values)
changes under each operation.
@@@ -/

class LawfulDict (d : Type → Type → Type) [DecidableEq k] extends Dict d where
  lookup_empty  : ∀ (key : k), lookup key (empty : d k v) = none
  lookup_insert_same : ∀ (key : k) (val : v) (m : d k v),
      lookup key (insert key val m) = some val
  lookup_insert_diff : ∀ (k1 k2 : k) (val : v) (m : d k v),
      k1 ≠ k2 → lookup k1 (insert k2 val m) = lookup k1 m
  lookup_delete_same : ∀ (key : k) (m : d k v),
      lookup key (delete key m) = none
  lookup_delete_diff : ∀ (k1 k2 : k) (m : d k v),
      k1 ≠ k2 → lookup k1 (delete k2 m) = lookup k1 m

/-! @@@
## 11.3  Association list implementation

An association list stores key-value pairs in a list.
@@@ -/

def AList (k v : Type) := List (k × v)

def AList.empty : AList k v := []

def AList.insert (key : k) (val : v) (m : AList k v) : AList k v :=
  (key, val) :: m

def AList.lookup [DecidableEq k] (key : k) : AList k v → Option v
  | []            => none
  | (k, v) :: t  => if key == k then some v else AList.lookup key t

def AList.delete [DecidableEq k] (key : k) : AList k v → AList k v
  | []            => []
  | (k, v) :: t  => if key == k then AList.delete key t
                    else (k, v) :: AList.delete key t

instance : Dict AList where
  empty  := AList.empty
  insert := AList.insert
  lookup := AList.lookup
  delete := AList.delete

-- Verify the laws hold.  Provided as term-mode proofs:
theorem alist_lookup_empty [DecidableEq k] (key : k) :
    AList.lookup key (AList.empty : AList k v) = none :=
  rfl

theorem alist_lookup_insert_same [DecidableEq k] (key : k) (val : v) (m : AList k v) :
    AList.lookup key (AList.insert key val m) = some val := by
  simp [AList.lookup, AList.insert]

theorem alist_lookup_insert_diff [DecidableEq k] {k1 k2 : k} (val : v)
    (m : AList k v) (hne : k1 ≠ k2) :
    AList.lookup k1 (AList.insert k2 val m) = AList.lookup k1 m := by
  simp [AList.lookup, AList.insert, hne]

theorem alist_lookup_delete_same [DecidableEq k] (key : k) (m : AList k v) :
    AList.lookup key (AList.delete key m) = none := by
  induction m with
  | nil => rfl
  | cons hd t ih =>
    obtain ⟨k', v'⟩ := hd
    by_cases h : key = k'
    · subst h; simp [AList.delete, ih]
    · simp [AList.delete, AList.lookup, h, ih]

theorem alist_lookup_delete_diff [DecidableEq k] {k1 k2 : k} (m : AList k v)
    (hne : k1 ≠ k2) :
    AList.lookup k1 (AList.delete k2 m) = AList.lookup k1 m := by
  induction m with
  | nil => rfl
  | cons hd t ih =>
    obtain ⟨k', v'⟩ := hd
    by_cases h : k2 = k'
    · subst h; simp [AList.delete, AList.lookup, ih, hne]
    · by_cases h1 : k1 = k'
      · subst h1; simp [AList.delete, AList.lookup, h]
      · simp [AList.delete, AList.lookup, h, h1, ih]

/-! @@@
All five laws now hold for `AList`, so we can package the implementation together with
its proofs as a `LawfulDict` instance — the formal claim that `AList` *satisfies the
dictionary specification*, not merely that it type-checks against the `Dict` interface.
@@@ -/

instance {k : Type} [DecidableEq k] : LawfulDict (d := AList) (k := k) where
  toDict := inferInstance
  lookup_empty := alist_lookup_empty
  lookup_insert_same := alist_lookup_insert_same
  lookup_insert_diff := fun _ _ val m h => alist_lookup_insert_diff val m h
  lookup_delete_same := alist_lookup_delete_same
  lookup_delete_diff := fun _ _ m h => alist_lookup_delete_diff m h

/-! @@@
> **Checkpoint — `AList.insert` then `AList.lookup`.** `insert` conses `(key, val)` onto
> the front; `lookup` scans front-to-back. **Predict** what looking up a just-inserted key
> returns, then check.
@@@ -/

#eval (AList.lookup 1 (AList.insert 1 100 (AList.empty : AList Nat Nat)))   -- predict first

/-! @@@
> **Checkpoint — `AList.lookup` on an absent key (`lookup_empty`).** **Predict**, from
> `lookup_empty`, what `lookup` returns for a key that was never inserted, then check.
@@@ -/

#eval (AList.lookup 5 (AList.insert 1 100 (AList.empty : AList Nat Nat)))   -- predict first

/-! @@@
> **Checkpoint — the most recent `insert` wins (`lookup_insert_same`).** `insert` never
> deletes the old pair, but `lookup` finds the front one first. **Predict**, from
> `lookup_insert_same`, which value survives after inserting key `1` twice, then check.
@@@ -/

#eval (AList.lookup 1 (AList.insert 1 200 (AList.insert 1 100 (AList.empty : AList Nat Nat))))   -- predict first

/-! @@@
> **Checkpoint — `AList.delete` removes a key (`lookup_delete_same`).** **Predict**, from
> `lookup_delete_same`, what `lookup` returns for a key after it is deleted, then check.
@@@ -/

#eval (AList.lookup 1 (AList.delete 1 (AList.insert 1 100 (AList.empty : AList Nat Nat))))   -- predict first

/-! @@@
> **Checkpoint — `delete` leaves other keys alone (`lookup_delete_diff`).** Deleting key
> `1` must not disturb key `2`. **Predict**, from `lookup_delete_diff`, the lookup of `2`,
> then check.
@@@ -/

#eval (AList.lookup 2 (AList.delete 1 (AList.insert 2 20 (AList.insert 1 10 (AList.empty : AList Nat Nat)))))   -- predict first

/-! @@@
## 11.4  Opaque types: hiding implementation details

The `opaque` keyword makes an identifier's definition irreducible to
the elaborator.  Proofs about an `opaque` value must work through the
interface, not by unfolding the definition.

This is abstraction enforced by the type system: callers cannot depend
on the implementation details even if they tried.
@@@ -/

-- A counter type with an opaque implementation
opaque Counter : Type := Nat

@[instance] axiom Counter.instNonempty : Nonempty Counter

noncomputable opaque Counter.zero  : Counter
noncomputable opaque Counter.incr  : Counter → Counter
noncomputable opaque Counter.value : Counter → Nat

-- The specification is stated separately as axioms about the interface:
axiom Counter.value_zero : Counter.value Counter.zero = 0
axiom Counter.value_incr : ∀ c, Counter.value (Counter.incr c) =
                                Counter.value c + 1

-- Note: in a production library, these axioms would be proved as theorems
-- using the concrete implementation.  The opaque/axiom pattern separates
-- the interface (what callers see) from the implementation.

/-! @@@
> **Checkpoint — an `opaque` value cannot be evaluated.** Unlike `AList`, a `Counter` has
> no reducible definition, so `#eval Counter.value Counter.zero` would fail to compute —
> everything you can know about it lives in the axioms. So here we `#check` instead of
> `#eval`. **Predict** the *type* Lean reports for `Counter.value_incr` (a `∀`-statement
> about the interface), then check.
@@@ -/

#check @Counter.value_incr   -- predict the ∀-statement; opaque, so no #eval

/-! @@@
## 11.5  Stack: another abstract type

A stack supports push, pop, and peek, with a size operation.
The specification: push then pop returns the original element and stack.
@@@ -/

class Stack (s : Type → Type) where
  empty : s α
  push  : α → s α → s α
  pop   : s α → Option (α × s α)
  size  : s α → Nat

class LawfulStack (s : Type → Type) extends Stack s where
  pop_empty  : pop (empty : s α) = none
  pop_push   : ∀ (x : α) (st : s α),
      pop (push x st) = some (x, st)
  size_empty : size (empty : s α) = 0
  size_push  : ∀ (x : α) (st : s α),
      size (push x st) = size st + 1

-- List implementation of Stack:
instance : Stack List where
  empty := []
  push  := List.cons
  pop   := fun
    | []      => none
    | h :: t  => some (h, t)
  size  := List.length

instance : LawfulStack List where
  pop_empty  := rfl
  pop_push   := fun _ _ => rfl
  size_empty := rfl
  size_push  := fun _ _ => rfl

/-! @@@
> **Checkpoint — `pop` undoes `push` (`pop_push`).** For the `List` stack, `push` is
> `cons` and `pop` splits head from tail. **Predict**, from `pop_push`, the pair returned
> after pushing `5`, then check.
@@@ -/

#eval (Stack.pop (Stack.push 5 ([1, 2, 3] : List Nat)))   -- predict first

/-! @@@
> **Checkpoint — `push` grows `size` by one (`size_push`).** **Predict**, from
> `size_push`, the size after one `push` onto a 3-element stack, then check.
@@@ -/

#eval (Stack.size (Stack.push 5 ([1, 2, 3] : List Nat)))   -- predict first

/-! @@@
> **Checkpoint — `pop` on the empty stack (`pop_empty`).** **Predict**, from `pop_empty`,
> what `pop` returns when there is nothing to remove, then check.
@@@ -/

#eval (Stack.pop ([] : List Nat))   -- predict first

/-! @@@
## 11.6  Representation independence

The key property of abstract types: any two implementations satisfying
the laws are *observationally equivalent* from the caller's perspective.

This is not just informal.  Given two `LawfulDict` instances `D1` and `D2`,
any sequence of `empty`, `insert`, `lookup`, `delete` operations produces
the same `lookup` results in both.

This can be stated as a theorem schema — for each sequence of operations,
the `lookup` results agree.  We will not prove this in full generality;
stating it precisely is the skill being practiced.
@@@ -/

/-! @@@
> **Checkpoint — observations are what implementations must share.** Representation
> independence says two lawful stacks agree on every *observation* (`pop`, `size`), even
> if their internals differ. A push-push-pop sequence is such an observation. **Predict**
> the LIFO result below, then check.
@@@ -/

#eval (Stack.pop (Stack.push 9 (Stack.push 8 ([] : List Nat))))   -- predict first (LIFO)

/-! @@@
## 11.7  Representation invariants and abstraction functions

A concrete representation usually admits values the abstract type should never observe.
An `AList` can hold *duplicate keys* — `[(1, 10), (1, 20)]` — yet a dictionary is a
partial function, so a key must map to at most one value.  A **representation invariant**
carves the legal representations out of the concrete type, and an **abstraction function**
maps each legal representation to the abstract value it denotes.

Lean expresses "the values satisfying an invariant" with a *refinement type* (subtype)
`{ x // Inv x }`: a pair of a value `x` and a proof that `Inv x` holds.  The invariant
below is *"keys are distinct"* — `(m.map Prod.fst).Nodup`.  The provided value carries a
machine-checked proof that its three keys are distinct.  You will *read* this proof in the
exercises, never author one.
@@@ -/

def wfExample : { m : AList Nat Nat // (m.map Prod.fst).Nodup } :=
  ⟨[(1, 10), (2, 20), (3, 30)], by decide⟩

/-! @@@
> **Checkpoint — the representation invariant is decidable.** `Nodup` over a concrete list
> of `DecidableEq` keys is decidable — which is exactly why `by decide` can discharge the
> proof inside `wfExample`. **Predict** the Boolean below — do `wfExample`'s keys satisfy
> the invariant? — then check.
@@@ -/

#eval decide ((([(1, 10), (2, 20), (3, 30)] : AList Nat Nat).map Prod.fst).Nodup)   -- predict first

/-! @@@
## Exercises

Each exercise carries a banner — `[id] · competency · tier · level · target` — and,
where it asks you to build something, an **acceptance check**: paste it beneath your
definition in your own file and it must succeed.  `#guard` is silent on success and
errors on failure, so the compiler is your grader.  See `EXERCISE_CONVENTIONS.md` for
the schema.  Do every **core** exercise; **stretch** exercises go deeper and are
optional.

---

**[E11.1]** · *specification writing* · tier 1 · **core** · target `AList.size`

Add a `size` operation to the association-list dictionary and specify how it relates to
the other operations.  Define `AList.size (m : AList k v) : Nat`, then state — as `Prop`s
in your own words — the two laws *"the empty dict has size 0"* and *"`insert` grows size
by exactly one"* (`AList` never deduplicates, so the second holds literally, even for a
repeated key).  Confirm them on instances; the checks are the grader.  Effort: 1 line of
code; then say which check is the *boundary* case and which law each remaining check
witnesses.

```lean
#guard AList.size (AList.empty : AList Nat Nat) = 0
#guard AList.size (AList.insert 1 10 (AList.empty : AList Nat Nat)) = 1
#guard AList.size (AList.insert 1 99 (AList.insert 1 10 (AList.empty : AList Nat Nat))) = 2
#guard AList.size (AList.delete 1 (AList.insert 1 10 (AList.empty : AList Nat Nat))) = 0
```

---

**[E11.2]** · *decidability identification* · tier 1 · **stretch**

For each proposition about the dictionary, say **whether `decide` can close it and why**
(finite domain? decidable predicate? `DecidableEq` keys?) *before* checking — the
judgment is the point, not the tool-use:

(a) `AList.lookup 2 (AList.insert 2 20 (AList.insert 1 10 (AList.empty : AList Nat Nat))) = some 20`
(b) `∀ key ∈ ([1,2,3] : List Nat), AList.lookup key (AList.insert key 0 (AList.empty : AList Nat Nat)) = some 0`
(c) `∀ (m : AList Nat Nat) (key : Nat), AList.lookup key (AList.insert key 0 m) = some 0`

```lean
#guard AList.lookup 2 (AList.insert 2 20 (AList.insert 1 10 (AList.empty : AList Nat Nat))) = some 20
#guard decide (∀ key ∈ ([1, 2, 3] : List Nat),
    AList.lookup key (AList.insert key 0 (AList.empty : AList Nat Nat)) = some 0) = true
-- (c) has no check on purpose: say why decide cannot close a ∀ over ALL AList values,
--     and name the §11.2 law that settles it instead.
```

---

**[E11.3]** · *counterexample finding* · tier 1 · **core** · target `insertOrderCounterexample`

A student claims *"`insert` order never matters: inserting two pairs and then looking up
any key gives the same answer regardless of the order of the two inserts."*  It is
**wrong** whenever the two keys coincide (the shadowing from §11.3).  Find inputs where
swapping two inserts changes a lookup, and encode the witness so the check **succeeds**
(it confirms the two sides differ):

```lean
#guard AList.lookup 1 (AList.insert 1 200 (AList.insert 1 100 (AList.empty : AList Nat Nat)))
     ≠ AList.lookup 1 (AList.insert 1 100 (AList.insert 1 200 (AList.empty : AList Nat Nat)))
```

Then state, in one line, the *correct* condition under which insert order is irrelevant
(it is exactly the hypothesis of `lookup_insert_diff`).

---

**[E11.4]** · *type-directed derivation* · tier 2 · **core** · target `peek`

Derive `peek [Stack s] : s α → Option α` — the top element without removing it — from the
`Stack` interface alone.  Produce a **derivation trace** in the Week 2 §2.6 format (the
trace is the graded artifact), then the `def`.  *First-step hint:* the only operation that
inspects a stack is `pop : s α → Option (α × s α)`; apply it first, then turn
`Option (α × s α)` into `Option α` — which functor operation does that with a projection?
Effort: ~3 trace steps, 1 line of code.

```lean
#guard peek ([1, 2, 3] : List Nat) = some 1
#guard peek ([] : List Nat) = none
#guard peek (Stack.push 7 ([1, 2] : List Nat)) = some 7
```

---

**[E11.5]** · *type reading (free theorems)* · tier 2 · **stretch**

Read two abstract signatures without running anything.

(a) `Stack.pop : s α → Option (α × s α)`, polymorphic in the element type `α` and abstract
in the container `s`.  State two things **every** inhabitant must satisfy (can it
manufacture an `α` it was never given?  can a returned `α` be anything other than one
already in the stack?) and one thing the type **cannot** force (e.g. LIFO vs FIFO order —
why is that beyond the reach of the type?).

(b) `Dict.lookup : k → d k v → Option v`.  What does polymorphism in `v` forbid `lookup`
from doing to the values it returns, and why must every non-`none` result be a value that
was previously `insert`ed?  (Builds on §7.2.  No code to submit.)

---

**[E11.6]** · *specification reading* · tier 3 · **core**

§11.7 provides `wfExample : { m : AList Nat Nat // (m.map Prod.fst).Nodup }` — a
well-formed dictionary carrying a machine-checked proof of its representation invariant.
**Read** it (do not author any proof) and explain, in prose:

(a) what the invariant `(m.map Prod.fst).Nodup` asserts about the representation, and why a
dictionary needs it (relate it to *"a key maps to at most one value"* from §11.2);
(b) what the `by decide` inside `wfExample` actually verified, and why that check is
*decidable* here;
(c) the **abstraction function** — which partial function from keys to values does
`wfExample` denote?
(d) which `AList` operation from §11.3 can produce a value that *violates* the invariant,
and confirm the violation with the check below (a correct duplicate-key witness makes the
inequality-to-`false` check succeed):

```lean
#guard decide ((([(1, 10), (1, 20)] : List (Nat × Nat)).map Prod.fst).Nodup) = false
```

This is a reading task: the graded artifact is your four-part explanation, not a proof.
---

**[E11.7]** · *specification writing* · tier 1 · **stretch** · target `Queue`

Define a `Queue` type class in the style of §11.4's `Stack` — `empty`, `enqueue`,
`dequeue : q α → Option (α × q α)`, and `size` — together with a `LawfulQueue` extension
stating its laws.  The decisive law is **FIFO**: dequeuing returns the *oldest* element, not
the most recently enqueued.  State the laws; do not prove them.  Give the `List`-backed
instance and confirm the laws on instances:

```lean
#guard (Queue.dequeue (Queue.enqueue 2 (Queue.enqueue (1 : Nat) (Queue.empty : List Nat)))).map Prod.fst = some 1
#guard (Queue.dequeue (Queue.empty : List Nat)).isNone
#guard Queue.size (Queue.enqueue 2 (Queue.enqueue (1 : Nat) (Queue.empty : List Nat))) = 2
```

Compare with `LawfulStack` (§11.4): exactly one law changes.  Which one, and why does that
single change reverse the order of every observation?

---

**[E11.8]** · *type-directed derivation* · tier 2 · **stretch** · target `TwoListStack`

Give a second `Stack` implementation with a different representation:

```lean
structure TwoListStack (α : Type) where
  front : List α
  back  : List α
```

`push` conses onto `back`; `pop` takes from `front`, and when `front` is empty it first
rebalances by reversing `back` into it.  Produce a derivation trace for `pop` — the trace is
the graded artifact — then the `def`s, and write the `LawfulStack` law statements for this
representation (statements only).  *First-step hint:* `pop` eliminates `front` first
(`[]` vs `y :: ys`); only the `[]` branch touches `back`.  Effort: ~5 trace steps, ~8 lines.

```lean
#guard (TwoListStack.push 2 (TwoListStack.push (1 : Nat) TwoListStack.empty)).size = 2
#guard ((TwoListStack.push 2 (TwoListStack.push (1 : Nat) TwoListStack.empty)).pop).map Prod.fst = some 1
#guard (TwoListStack.pop (TwoListStack.empty : TwoListStack Nat)).isNone
```

---

**[E11.9]** · *specification writing* · tier 1 (+ tier-3 reading) · **core**

State the **representation-independence** theorem for `Stack`: *for any two `LawfulStack`
instances `S1` and `S2`, any program built only from `push`, `pop`, `size`, and `empty`
produces the same observable results in both.*  Write it as precisely as you can in Lean —
you must first decide what "program" and "observable result" are, as types, before the
statement can be written at all; that decision is the exercise.  Do not prove it.  Then,
using E11.8's `TwoListStack` alongside the `List` instance of §11.4, confirm the claim on one
concrete program by checking that both representations yield the same observation.

Say in two sentences which of the `LawfulStack` laws your statement actually depends on.
This is the exercise the unit points at: a client may rely on the laws, never on the
representation.

@@@ -/

end W11
