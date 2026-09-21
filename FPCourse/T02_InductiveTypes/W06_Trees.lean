-- FPCourse/T02_InductiveTypes/W06_Trees.lean
import Mathlib.Data.List.Sort
import Mathlib.Order.Basic

/-! @@@
# Trees and BST Invariants

## Binary trees

A binary tree over type `α` is either a leaf or a node carrying a value
and two subtrees.  Like lists, trees are defined inductively, and
functions on them are defined by structural recursion.

The key new idea this week: *invariants*.  A BST (binary search tree)
is not just any tree — it is a tree satisfying a *predicate* that
constrains the relationship between each node's value and the values in
its subtrees.  That predicate is a proposition, and preserving it is
a specification.
@@@ -/

namespace W06

/-! @@@
## 6.1  The BTree type
@@@ -/

inductive BTree (α : Type) where
  | leaf : BTree α
  | node : BTree α → α → BTree α → BTree α
deriving Repr

/-! @@@
## 6.2  Basic tree functions
@@@ -/

def BTree.size : BTree α → Nat
  | .leaf         => 0
  | .node l _ r   => l.size + 1 + r.size

def BTree.height : BTree α → Nat
  | .leaf         => 0
  | .node l _ r   => max l.height r.height + 1

def BTree.member [DecidableEq α] (x : α) : BTree α → Bool
  | .leaf         => false
  | .node l v r   => x == v || l.member x || r.member x

-- In-order traversal produces a list
def BTree.toList : BTree α → List α
  | .leaf         => []
  | .node l v r   => l.toList ++ [v] ++ r.toList

-- Specification of toList and size:
theorem toList_length_eq_size (t : BTree α) :
    t.toList.length = t.size := by
  induction t with
  | leaf => rfl
  | node l v r ihl ihr =>
    simp only [BTree.toList, BTree.size, List.length_append, List.length_cons,
               List.length_nil]
    omega

/-! @@@
> **Checkpoint — `toList` (in-order traversal).** `toList` flattens a tree
> left-value-right.  **Predict** the list below, then check.
@@@ -/

#eval (BTree.node (BTree.node BTree.leaf 3 BTree.leaf) 5 (BTree.node BTree.leaf 7 BTree.leaf)).toList   -- predict

/-! @@@
> **Checkpoint — `height`.** `height` returns the longest root-to-leaf path.
> **Predict** the value below from the tree's shape, then check.
@@@ -/

#eval (BTree.node (BTree.node BTree.leaf 3 BTree.leaf) 5 (BTree.node BTree.leaf 7 BTree.leaf)).height   -- predict

/-! @@@
> **Checkpoint — `member`.** `member` tests presence anywhere in the tree.
> **Predict** both Booleans, then check.
@@@ -/

#eval (BTree.node (BTree.node BTree.leaf 3 BTree.leaf) 5 (BTree.node BTree.leaf 7 BTree.leaf)).member 7   -- predict
#eval (BTree.node (BTree.node BTree.leaf 3 BTree.leaf) 5 (BTree.node BTree.leaf 7 BTree.leaf)).member 4   -- predict

/-! @@@
## 6.3  The BST predicate

A BST (for `BTree Nat`) is a tree where:
- Every value in the left subtree is strictly less than the root value.
- Every value in the right subtree is strictly greater than the root value.
- Both subtrees are themselves BSTs.

We express "every value in the subtree satisfies P" using an auxiliary
predicate `BTree.ForAll`.
@@@ -/

-- ForAll: every element of a tree satisfies a predicate
def BTree.ForAll (p : α → Prop) : BTree α → Prop
  | .leaf         => True
  | .node l v r   => p v ∧ l.ForAll p ∧ r.ForAll p

-- IsBST: the binary search tree invariant for Nat
inductive IsBST : BTree Nat → Prop where
  | leaf : IsBST .leaf
  | node : IsBST l → IsBST r
         → l.ForAll (· < v)
         → r.ForAll (v < ·)
         → IsBST (.node l v r)

-- We can check IsBST on concrete trees using decide,
-- once we make BTree.ForAll decidable:
instance decForAll (p : Nat → Prop) [DecidablePred p] :
    DecidablePred (BTree.ForAll p)
  | .leaf       => Decidable.isTrue trivial
  | .node l v r =>
    match decForAll p l, decForAll p r, inferInstanceAs (Decidable (p v)) with
    | Decidable.isTrue hl, Decidable.isTrue hr, Decidable.isTrue hv =>
      Decidable.isTrue ⟨hv, hl, hr⟩
    | Decidable.isFalse hl, _, _ =>
      Decidable.isFalse (fun ⟨_, h, _⟩ => hl h)
    | _, Decidable.isFalse hr, _ =>
      Decidable.isFalse (fun ⟨_, _, h⟩ => hr h)
    | _, _, Decidable.isFalse hv =>
      Decidable.isFalse (fun ⟨h, _, _⟩ => hv h)

/-! @@@
> **Checkpoint — `ForAll` is decidable.** `decForAll` makes `BTree.ForAll` decidable, so
> `decide` can settle it.  **Predict** the Boolean below, and say *why* it is decidable,
> before reading the result.
@@@ -/

#eval decide (BTree.ForAll (· < 5) (BTree.node BTree.leaf 3 BTree.leaf))   -- predict first

/-! @@@
## 6.4  BST insertion

Insert `x` into a BST, maintaining the invariant:
- If `x < v`, insert into the left subtree.
- If `v < x`, insert into the right subtree.
- If `x = v`, the element is already present.
@@@ -/

def bstInsert (x : Nat) : BTree Nat → BTree Nat
  | .leaf         => .node .leaf x .leaf
  | .node l v r   =>
    if x < v then .node (bstInsert x l) v r
    else if v < x then .node l v (bstInsert x r)
    else .node l v r   -- x = v: already present

/-! @@@
> **Checkpoint — `bstInsert` keeps order.** Inserting maintains the BST ordering.
> **Predict** the in-order `toList` after inserting `4`, then check that it stayed sorted.
@@@ -/

#eval (bstInsert 4 (BTree.node (BTree.node BTree.leaf 3 BTree.leaf) 5 BTree.leaf)).toList   -- predict

/-! @@@
## 6.5  Preservation of ForAll

A key lemma: if all elements of `t` satisfy `p`, and `p x` holds, then all
elements of `bstInsert x t` also satisfy `p`.

The provided proof is by structural recursion on `t`, mirroring the
structure of `bstInsert`.
@@@ -/

-- Provided term-mode proof of ForAll preservation.
theorem forAll_bstInsert (p : Nat → Prop) (x : Nat) (hx : p x) :
    ∀ t : BTree Nat, t.ForAll p → (bstInsert x t).ForAll p
  | .leaf,         _              => by simp [bstInsert, BTree.ForAll]; exact hx
  | .node l v r,  ⟨hv, hfl, hfr⟩ => by
    simp only [bstInsert]
    split_ifs with hlt hgt
    · exact ⟨hv, forAll_bstInsert p x hx l hfl, hfr⟩
    · exact ⟨hv, hfl, forAll_bstInsert p x hx r hfr⟩
    · exact ⟨hv, hfl, hfr⟩

/-! @@@
> **Checkpoint — insertion preserves a bound.** `forAll_bstInsert` says inserting an
> element that satisfies `p` keeps *every* element satisfying `p`.  **Predict** the
> Boolean (is every element still `< 10` after inserting `4`?), then check.
@@@ -/

#eval decide (BTree.ForAll (· < 10) (bstInsert 4 (BTree.node (BTree.node BTree.leaf 3 BTree.leaf) 5 BTree.leaf)))   -- predict

/-! @@@
## 6.6  Preservation of IsBST

If `t` is a BST and `x : Nat`, then `bstInsert x t` is also a BST.

The proof uses `forAll_bstInsert` twice per recursive case — once for the
left bound and once for the right — along with the structurally recursive
IsBST assumption.

@@@ -/

theorem bstInsert_isBST (x : Nat) :
    ∀ t : BTree Nat, IsBST t → IsBST (bstInsert x t)
  | .leaf,        _ => by
    simp [bstInsert]
    exact IsBST.node IsBST.leaf IsBST.leaf trivial trivial
  | .node l v r,  IsBST.node hl hr hfl hfr => by
    simp only [bstInsert]
    split_ifs with hlt hgt
    · exact IsBST.node (bstInsert_isBST x l hl) hr
        (forAll_bstInsert (· < v) x hlt l hfl) hfr
    · exact IsBST.node hl (bstInsert_isBST x r hr)
        hfl (forAll_bstInsert (v < ·) x hgt r hfr)
    · exact IsBST.node hl hr hfl hfr

/-! @@@
## 6.7  Mutual recursion: Rose trees

A *rose tree* has nodes with arbitrarily many children (stored as a list).
Defining rose trees requires mutual recursion between the tree type and
the forest (list of trees) type.
@@@ -/

mutual
  inductive RoseTree (α : Type) where
    | node : α → Forest α → RoseTree α

  inductive Forest (α : Type) where
    | nil  : Forest α
    | cons : RoseTree α → Forest α → Forest α
end

mutual
  def roseSize : RoseTree α → Nat
    | .node _ f => forestSize f + 1

  def forestSize : Forest α → Nat
    | .nil      => 0
    | .cons t f => roseSize t + forestSize f
end

/-! @@@
> **Checkpoint — mutual recursion (`roseSize`).** `roseSize` counts nodes by calling
> `forestSize` on its children.  **Predict** the count for the tree below (a root with
> two children), then check.
@@@ -/

#eval roseSize (RoseTree.node 1 (Forest.cons (RoseTree.node 2 Forest.nil) (Forest.cons (RoseTree.node 3 Forest.nil) Forest.nil)))   -- predict

/-! @@@
## Exercises

Banners read `[id] · competency · tier · level · target`; build exercises ship a
`#guard` **acceptance check** to paste beneath your definition (see
`EXERCISE_CONVENTIONS.md`).  Do every **core** exercise; **stretch** is optional.

---

**[E6.1]** · *inhabitation + specification writing* · tier 1 · **core** · target `BTree.map`

Define `BTree.map (f : α → β) : BTree α → BTree β` (apply `f` at every node, keep the
shape) and state its specification *"`map` preserves size"* as a `Prop`.  Confirm that
`map` preserves size and commutes with `toList`:

```lean
-- def BTree.map (f : α → β) : BTree α → BTree β
--   | .leaf => .leaf
--   | .node l v r => .node (l.map f) (f v) (r.map f)
#guard ((BTree.node (BTree.node BTree.leaf 3 BTree.leaf) 5 BTree.leaf).map (· * 10)).size = 2
#guard ((BTree.node (BTree.node BTree.leaf 3 BTree.leaf) 5 BTree.leaf).map (· * 10)).toList = [30, 50]
```

---

**[E6.2]** · *decidability identification* · tier 1 · **core**

§6.3 gives a `Decidable` instance for `BTree.ForAll` (`decForAll`) but **none** for
`IsBST`.  So: can `decide` close `IsBST t` *directly*?  If not, name the instance that
is missing, and confirm the *ingredient* propositions `decide` **can** settle (these
compile; `decide (IsBST …)` would not):

```lean
#guard decide (BTree.ForAll (· < 5) (BTree.node BTree.leaf 3 BTree.leaf)) = true
#guard decide (BTree.ForAll (5 < ·) (BTree.node BTree.leaf 7 BTree.leaf)) = true
```

One line: what would you have to provide to make `decide (IsBST t)` typecheck?

---

**[E6.3]** · *counterexample finding* · tier 1 · **core**

A student claims *"`(bstInsert x t).size = t.size + 1` for all `x`, `t`."*  It is
**wrong**.  Find `x`, `t` witnessing the mismatch (hint: what if `x` is already in
`t`?) and encode the witness so the check **succeeds**:

```lean
#guard (bstInsert 5 (BTree.node BTree.leaf 5 BTree.leaf)).size
         ≠ (BTree.node BTree.leaf 5 BTree.leaf).size + 1
```

State the *correct* relationship between `(bstInsert x t).size` and `t.size` in words.

---

**[E6.4]** · *type-directed derivation* · tier 2 · **core** · target `BTree.mirror`

Derive `BTree.mirror : BTree α → BTree α` that swaps every node's left and right
subtrees.  Give a **derivation trace** (Week 2 §2.6 format; the trace is graded), then the `def`.
*First-step hint:* match the input's constructor (`.leaf` vs `.node l v r`) — ⊕E — then
rebuild, recursing on both subtrees.  Effort: ~3 trace steps, 3 lines.

```lean
#guard (BTree.node (BTree.node BTree.leaf 1 BTree.leaf) 2 BTree.leaf).mirror.toList = [2, 1]
#guard (BTree.node (BTree.node BTree.leaf 1 BTree.leaf) 2 BTree.leaf).mirror.mirror.toList
         = (BTree.node (BTree.node BTree.leaf 1 BTree.leaf) 2 BTree.leaf).toList
```

---

**[E6.5]** · *inhabitation (exploiting an invariant)* · tier 2 · **stretch** · target `bstSearch`

Define `bstSearch (x : Nat) : BTree Nat → Bool` that uses the BST ordering to visit
**one** subtree per node (O(height), not O(size)): compare `x` with `v` and recurse
left or right accordingly.  (The `IsBST` proof is not needed for the computation — the
ordering is what you exploit.)  Effort: one `match` + `if`/`else if`; ~5 lines.

```lean
#guard bstSearch 7 (BTree.node (BTree.node BTree.leaf 3 BTree.leaf) 5 (BTree.node BTree.leaf 7 BTree.leaf)) = true
#guard bstSearch 6 (BTree.node (BTree.node BTree.leaf 3 BTree.leaf) 5 (BTree.node BTree.leaf 7 BTree.leaf)) = false
```

---

**[E6.6]** · *inhabitation + specification writing (mutual recursion)* · tier 1 · **stretch** · target `roseToList`

Define `roseToList : RoseTree α → List α` and its mutual helper `forestToList : Forest
α → List α`, collecting every value.  State the spec `(roseToList t).length = roseSize
t`, analogous to `toList_length_eq_size`, and confirm on an instance.  Effort: a
`mutual` block, ~6 lines.

```lean
#guard (roseToList (RoseTree.node 1
          (Forest.cons (RoseTree.node 2 Forest.nil)
            (Forest.cons (RoseTree.node 3 Forest.nil) Forest.nil)))).length = 3
```
@@@ -/

end W06
