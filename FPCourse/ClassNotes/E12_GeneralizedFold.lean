/- @@@
# Foldable: Generalizing Fold Beyond `List`

Last class we fixed *one* half of `fold`'s type signature,
`(α → α → α) → α → List α → α`. A bare `op`/`id` pair isn't
enough structure to guarantee `fold` means anything -- `op`
has to be associative, and `id` has to be a genuine identity
for it -- so we bundled the two together with proofs into a
`Monoid`, and wrote a `mfold [Monoid α] : List α → α` that
can't be handed a broken pair the way the original could.

Today we fix the *other* half: `List`. Nothing about folding
is actually about lists. You can fold a `Tree Nat` down to its
sum the same way you fold a `List Nat`; you can fold an
`Option Nat` (treating `none` as "nothing to add"). Right now,
doing either means writing a brand-new `treeFold`/`optionFold`
by hand, each one re-deriving the exact same shape `mfold`
already has. We'll name that shape -- `Foldable` -- so writing
it once, per container, is enough.
@@@ -/

namespace GeneralizedFold

/- @@@
## Recap: `Monoid`, Bundled and Proved

Same class as last time, restated so this file stands on its
own. See `E11_abstractAlgebra.lean` if any of this is unfamiliar --
`op`/`id` and the two laws that make folding with them safe.
@@@ -/

class Monoid (α : Type) where
  op      : α → α → α
  id      : α
  assoc   : ∀ a b c, op (op a b) c = op a (op b c)
  idLeft  : ∀ a, op id a = a
  idRight : ∀ a, op a id = a

instance : Monoid Nat where
  op      := (· + ·)
  id      := 0
  assoc   := Nat.add_assoc
  idLeft  := Nat.zero_add
  idRight := Nat.add_zero

instance : Monoid String where
  op      := (· ++ ·)
  id      := ""
  assoc   := fun _ _ _ => String.append_assoc
  idLeft  := fun _ => String.empty_append
  idRight := fun _ => String.append_empty

/-- Last class's `mfold`, word for word: fold a `List α` with whatever
`Monoid α` typeclass resolution finds. -/
def mfold {α : Type} [Monoid α] : List α → α
| List.nil      => Monoid.id
| List.cons h t => Monoid.op h (mfold t)

#eval mfold (α := Nat) [2, 3, 4]   -- 9

/- @@@
## The Same Problem, One Level Up

Here's a binary tree of our own, nothing fancy -- a `leaf`, or
a `node` carrying a left subtree, a value, and a right subtree.
@@@ -/

inductive Tree (α : Type) where
| leaf
| node (l : Tree α) (v : α) (r : Tree α)

def sampleTree : Tree Nat :=
  Tree.node
    (Tree.node Tree.leaf 1 Tree.leaf)
    2
    (Tree.node Tree.leaf 3 Tree.leaf)

/- @@@
Suppose you want the sum of every value in a `Tree Nat` -- the
tree's version of `mfold`'s job. Nothing from `mfold` is reusable
for this: its argument type is pinned to `List α`, and a `Tree α`
isn't a `List α`. So you write it again, by hand, from scratch.
@@@ -/

def treeSum : Tree Nat → Nat
| Tree.leaf => 0
| Tree.node l v r => treeSum l + v + treeSum r

#eval treeSum sampleTree   -- 6

/- @@@
Look at `treeSum` next to `mfold` (or last class's hand-rolled
`sumNat`, for that matter): same shape, same "combine the
pieces with `+`, bottom out at `0`" idea, different container.
Multiply the three of them by every container type you'll ever
want to fold, and every element-monoid you'll ever want to fold
*with*, and you get a wall of near-identical functions that
differ only in which container they pattern-match on. That's
exactly the smell `Monoid` itself was invented to fix for `op`
and `id` -- except now it's the *container*, `List` vs. `Tree`
vs. whatever comes next, that needs abstracting over.
@@@ -/

/- @@@
## Aside: `Option`

One of the containers below will be `Option`, so a quick look at
it first. `Option α` means "maybe an `α`, maybe nothing" -- exactly
the shape you need when a function has no sensible answer for some
inputs:

```lean
inductive Option (α : Type) where
| none
| some (a : α)
```

`Nat.zero` has no predecessor -- there's nothing one less than
zero -- so a safe `pred` hands back `none` there instead of lying
and calling it zero again:
@@@ -/

def pred : Nat → Option Nat
| Nat.zero   => none
| Nat.succ n => some n

#eval pred 0   -- none
#eval pred 5   -- some 4

/- @@@
Same idea for `List.head?` (already in Lean): an empty list has no
first element, so it answers `none` instead of crashing.
@@@ -/

#eval ([] : List Nat).head?        -- none
#eval ([1, 2, 3] : List Nat).head? -- some 1

/- @@@
## `Foldable`: A Typeclass Over Containers, Not Values

Every `Monoid` we've written is parameterized by a *concrete
type*: `Monoid Nat` is about the type `Nat`, full stop; `Monoid
String` is about the type `String`. Both `Nat` and `String` have
kind `Type` -- they are themselves types, so something can have
type `Nat` or type `String`.

`List`, `Tree`, and `Option`, on their own, are not concrete types
at all -- there's no value `x : List`, the way there's a value `x :
Nat`. Each one is a function *from* a type *to* a type: hand `List`
the type `Nat` and you get back the type `List Nat`; hand it
`String` and you get `List String`. Same for `Tree` and `Option`.
That makes `List`, `Tree`, and `Option` values of the kind `Type →
Type` -- one level up from `Nat` and `String`'s kind, `Type`:
@@@ -/

#check (Nat : Type)
#check (List : Type → Type)
#check (Tree : Type → Type)
#check (Option : Type → Type)

/- @@@
`Foldable`'s parameter `F` lives at that same level: not `F :=
Nat`, a `Type`, but `F := List` or `F := Tree` or `F := Option`,
each a `Type → Type`. That's the whole difference from `Monoid`:
`Monoid` asks "what concrete type is this about?"; `Foldable` asks
"what type-building container is this about?"

The one method, `foldr`, is exactly `List.foldr`'s signature
(and exactly `reduce`'s, from before we ever introduced
`Monoid`) with `List` replaced by the class's own type
parameter `F`: given a combining step `α → β → β` and a base
case `β`, turn an `F α` into a `β`.
@@@ -/

class Foldable (F : Type → Type) where
  foldr {α β : Type} : (α → β → β) → β → F α → β

/- @@@
`List`'s instance doesn't even need new code -- Lean's own
`List.foldr` already has exactly the right shape.
@@@ -/

instance : Foldable List where
  foldr := List.foldr

/- @@@
`Option`'s is the shortest possible `Foldable`: a `none` has no
elements to fold over, so it just returns the base case; a
`some a` has exactly one, so it combines `a` with the base case
and stops.
@@@ -/

instance : Foldable Option where
  foldr f z
  | none => z
  | some a => f a z

/- @@@
And `Tree`'s is `treeSum`'s recursion, generalized: fold the
left subtree, combine the value, fold the right subtree --
except now `f`/`z` are parameters instead of `+`/`0` baked in.
It's written as a plain recursive `def` first, `treeFoldr`,
rather than directly inside the `instance`: the recursive calls
need to call *themselves*, and while an ordinary `def` can
always do that, an `instance`'s own method can't yet call
*itself* by typeclass search -- the instance isn't registered
until the whole declaration finishes elaborating. `instance :
Foldable Tree where foldr := treeFoldr` just points the class
at the already-recursive function.
@@@ -/

def treeFoldr {α β : Type} (f : α → β → β) (z : β) : Tree α → β
| Tree.leaf => z
| Tree.node l v r => treeFoldr f (f v (treeFoldr f z r)) l

instance : Foldable Tree where
  foldr := treeFoldr

#eval Foldable.foldr (· + ·) 0 [1, 2, 3]        -- 6
#eval Foldable.foldr (· + ·) 0 (some 5)         -- 5
#eval Foldable.foldr (· + ·) 0 (none : Option Nat) -- 0
#eval Foldable.foldr (· + ·) 0 sampleTree       -- 6

/- @@@
## What You Get For Free

`Foldable.foldr` alone is already enough to define a handful of
useful operations *once*, generically over `F`, instead of once
per container:

- `toList`: every element, in the order `foldr` visits them,
  collected into a plain `List` -- handy when you want to fall
  back on everything `List` already has, for any container you
  can `Foldable.foldr` over.
- `size`: how many elements, by combining each one with "add
  one to the count" instead of doing anything with its value.
- `fold`: last class's `mfold`, except it now works on *any*
  `Foldable`, because `Monoid.op`/`Monoid.id` are exactly the
  `(α → β → β)`/`β` that `foldr` wants once you set `β := α`.
@@@ -/

def toList {F : Type → Type} [Foldable F] {α : Type} (xs : F α) : List α :=
  Foldable.foldr List.cons [] xs

def size {F : Type → Type} [Foldable F] {α : Type} (xs : F α) : Nat :=
  Foldable.foldr (fun _ n => n + 1) 0 xs

def fold {F : Type → Type} [Foldable F] {α : Type} [Monoid α] (xs : F α) : α :=
  Foldable.foldr Monoid.op Monoid.id xs

#eval toList sampleTree            -- [1, 2, 3]
#eval toList (some "hi")           -- ["hi"]
#eval toList (none : Option Nat)   -- []

#eval size sampleTree              -- 3
#eval size [1, 2, 3, 4]            -- 4
#eval size (none : Option Nat)     -- 0

#eval fold (α := Nat) sampleTree           -- 6, via Monoid Nat
#eval fold (α := Nat) [2, 3, 4]            -- 9, agrees with mfold
#eval fold (α := String) (some "only one") -- "only one"

/- @@@
`fold` on a `List` and `mfold` compute the same answer on every
input -- `Foldable List`'s `foldr` just *is* `List.foldr`, and
`mfold`'s recursion is `List.foldr Monoid.op Monoid.id` unrolled
by hand. `mfold` wasn't wrong; it was `fold` with `F` hardwired
to `List` before `Foldable` existed to say so.
@@@ -/

/- @@@
## A Second Example: `LawfulMap`

`Foldable` followed one recipe: a typeclass over a *container*
`F : Type → Type`; a method whose own *element types* (`α`/`β`)
are separate parameters, not fixed by `F`; and, same as `Monoid`,
laws bundled in as proof fields so only well-behaved instances
compile. `map` fits the same recipe.

The two laws say what "map" has to mean for *any* container, not
just `List`: `mapId` says mapping the identity function changes
nothing -- same shape, nothing dropped or duplicated. `mapComp`
says mapping with `g` and then `h` matches mapping with their
composite in one pass -- each element is transformed on its own,
in place, independent of the other elements and independent of
whether you do it in one step or two.
@@@ -/

class LawfulMap (F : Type → Type) where
  map     : {α β : Type} → (α → β) → F α → F β
  mapId   : ∀ {α : Type} (xs : F α), map id xs = xs
  mapComp : ∀ {α β γ : Type} (g : α → β) (h : β → γ) (xs : F α),
    map (h ∘ g) xs = map h (map g xs)

/- @@@
`List`'s instance is `List.map` itself, with the two laws proved
by induction on the list.
@@@ -/

instance : LawfulMap List where
  map     := List.map
  mapId   := by intro α xs; induction xs <;> simp_all
  mapComp := by intro α β γ g h xs; induction xs <;> simp_all

/- @@@
`Option`'s instance leaves `none` alone and maps under `some` --
both laws check by cases, no induction needed since there's no
recursive structure to induct on.
@@@ -/

instance : LawfulMap Option where
  map     := Option.map
  mapId   := by intro α xs; cases xs <;> rfl
  mapComp := by intro α β γ g h xs; cases xs <;> rfl

/- @@@
`Tree`'s instance is `treeMap`, structured exactly like `treeFoldr`
above: recurse left, transform the value, recurse right. Same
self-recursion rule applies -- it's a plain `def` first, not
written directly inside the `instance`. The two laws then follow
by induction on the tree, exactly as they did for `List`.
@@@ -/

def treeMap {α β : Type} (f : α → β) : Tree α → Tree β
| Tree.leaf => Tree.leaf
| Tree.node l v r => Tree.node (treeMap f l) (f v) (treeMap f r)

instance : LawfulMap Tree where
  map     := treeMap
  mapId   := by intro α xs; induction xs <;> simp_all [treeMap]
  mapComp := by intro α β γ g h xs; induction xs <;> simp_all [treeMap]

#eval LawfulMap.map (· + 1) [1, 2, 3]            -- [2, 3, 4]
#eval LawfulMap.map (· + 1) (some 5)             -- some 6
#eval LawfulMap.map (· + 1) (none : Option Nat)  -- none
#eval LawfulMap.map (· + 1) sampleTree            -- Tree with 2, 3, 4

/- @@@
And exactly like `Foldable.foldr` bought `toList`/`size`/`fold`
for free, `LawfulMap.map` alone is enough to write one generic
function that works over any container at all -- no `F`-specific
code, just the method the laws are attached to.
@@@ -/

def increment {F : Type → Type} [LawfulMap F] (xs : F Nat) : F Nat :=
  LawfulMap.map (· + 1) xs

#eval increment [1, 2, 3]            -- [2, 3, 4]
#eval increment (some 5)             -- some 6
#eval increment (none : Option Nat)  -- none
#eval increment sampleTree            -- Tree with 2, 3, 4

/- @@@
## EXERCISES

1. Give `Array` a `Foldable` instance (Lean's `Array.foldr` has
   the right shape already, same as `List`'s did). Confirm
   `size`/`toList`/`fold` all work on an `Array Nat` with no
   changes to those three definitions.

2. Define `sum {F : Type → Type} [Foldable F] (xs : F Nat) : Nat`
   directly from `Foldable.foldr` (no `Monoid` involved), and
   confirm it agrees with `fold (α := Nat)` on every example
   above -- `Monoid Nat` already means `+`/`0`, so the two
   should compute the same answer. Then build a `Monoid Nat`
   *value* using `*`/`1` (same `natMulMonoid` idea as last
   class's exercises -- it can't be a second `instance` for the
   same reason), and define `product` by calling
   `Foldable.foldr` with that value's `op`/`id` directly,
   since `fold` itself can only ever find the one registered
   `Monoid Nat` instance.

3. Define `any`/`all : {F : Type → Type} → [Foldable F] → (α →
   Bool) → F α → Bool` directly from `Foldable.foldr` (no
   `Monoid` needed -- `Bool` with `||`/`false` and `&&`/`true`
   are both monoids, but you can also just write the recursion
   by hand with `foldr` as the primitive). Check `any`/`all`
   against `sampleTree` and a `List Nat`.

4. `Tree`'s `foldr` above visits left-subtree, value,
   right-subtree -- "in-order." Define a *second* `Tree`
   container, `PreTree`, identical to `Tree` except its
   `Foldable` instance visits value-left-right instead
   ("pre-order"), and confirm `toList` on the same shape of
   tree gives a different list depending on which one you used.
   (You cannot give `Tree` itself a second `Foldable` instance
   for the same reason `Nat` couldn't wear two `Monoid`s --
   typeclass resolution needs one canonical choice per type.)

5. Lean's own `for x in xs do ...` loop syntax is backed by a
   typeclass with the same flavor as `Foldable`, `ForIn`, except
   it abstracts over *how to iterate with side effects* rather
   than *how to combine into one value*. Look up `ForIn` and
   write a one-paragraph comparison: what does `Foldable.foldr`
   buy you that `ForIn`'s `forIn` doesn't, and vice versa?
@@@ -/

/- @@@
## ANSWERS

### Exercise 1: `Array` as `Foldable`

The pattern is now clear: for any container with a `foldr`
operation that matches `(α → β → β) → β → F α → β`, we just
point the `Foldable` instance at that existing function.
`Array` is no exception -- Lean already ships with `Array.foldr`,
which has exactly the right shape. This is the easiest instance
to write because we're literally just delegating to something
that already exists.
@@@ -/

instance : Foldable Array where
  foldr := Array.foldr

#eval size (#[1, 2, 3, 4] : Array Nat)    -- 4
#eval toList (#[5, 6] : Array Nat)        -- [5, 6]
#eval fold (#[2, 3, 4] : Array Nat)       -- 9

/- @@@
Notice that `size`, `toList`, and `fold` work unchanged. That's
the whole point of `Foldable` -- once the instance exists, every
generic function built on top of `foldr` instantly works for
this new container, no re-implementation needed.

### Exercise 2: `sum` and `product`

We can define `sum` directly from `Foldable.foldr` without
reaching for `Monoid` at all. All we need is to pass `+` as the
combining step and `0` as the base case -- the same choice that
the `Monoid Nat` instance makes for `op` and `id`.
@@@ -/

def sum {F : Type → Type} [Foldable F] (xs : F Nat) : Nat :=
  Foldable.foldr (· + ·) 0 xs

#eval sum sampleTree           -- 6
#eval sum [2, 3, 4]            -- 9
#eval sum (some 5)             -- 5
#eval sum (none : Option Nat)  -- 0

/- @@@
Check: `fold (α := Nat)` on the same inputs also computes `6`,
`9`, `5`, and `0` respectively. They agree because they're using
the same combining strategy -- one is written out explicitly
with `(· + ·)` and `0`, the other looks them up via the
`Monoid Nat` typeclass instance, but they're the same numbers.

Now, for products: `Monoid Nat` is fixed to `+` and `0`, so
we can't make it also mean `*` and `1` via a second instance
(typeclass resolution needs one answer per type). Instead,
we'll build a `Monoid Nat` *value*, and pass its `op`/`id`
fields directly to `Foldable.foldr`.
@@@ -/

@[instance_reducible]
def natMulMonoid : Monoid Nat where
  op      := (· * ·)
  id      := 1
  assoc   := Nat.mul_assoc
  idLeft  := Nat.one_mul
  idRight := Nat.mul_one

def product {F : Type → Type} [Foldable F] (xs : F Nat) : Nat :=
  Foldable.foldr natMulMonoid.op natMulMonoid.id xs

#eval product sampleTree           -- 6 (1 * 2 * 3)
#eval product [2, 3, 4]            -- 24
#eval product (some 5)             -- 5
#eval product (none : Option Nat)  -- 1

/- @@@
The key insight: `Monoid` is just a bundle of data (`op`, `id`,
and proofs). When you can't register it as an instance, you
just pass it as an explicit value and unpack the fields you
need with dot notation.

### Exercise 3: `any` and `all`

These operations ask a question about the elements rather than
combining them into a single result. The "base case" is whether
we've found what we're looking for yet, and the "combining step"
checks one element and asks: "does this make our overall answer
true or false?"

For `any`, we're looking for *at least one* element that satisfies
the predicate. Start from `false` (we haven't found a match yet),
and short-circuit to `true` as soon as we encounter an element
where `p x` is true. Logically, combining is OR: `(p x) || accumulator`.

For `all`, we're checking that *every* element satisfies the
predicate. Start from `true` (no violations yet), and flip to
`false` if we find even one element where `p x` is false.
Logically, combining is AND: `(p x) && accumulator`.
@@@ -/

def any {F : Type → Type} [Foldable F] {α : Type} (p : α → Bool) (xs : F α) : Bool :=
  Foldable.foldr (fun x acc => p x || acc) false xs

def all {F : Type → Type} [Foldable F] {α : Type} (p : α → Bool) (xs : F α) : Bool :=
  Foldable.foldr (fun x acc => p x && acc) true xs

#eval any (· > 2) sampleTree              -- true (3 > 2)
#eval any (· > 5) sampleTree              -- false (none exceed 5)
#eval any (· > 2) [1, 2, 3, 4]            -- true (3, 4 exceed 2)

#eval all (· > 0) sampleTree              -- true (all are positive)
#eval all (· > 2) sampleTree              -- false (1 and 2 are not > 2)
#eval all (· > 0) [1, 2, 3, 4]            -- true (all are positive)

/- @@@
Notice: `any` and `all` work the same on `Tree`, `List`, and
`Option` -- all thanks to `Foldable`. The predicate is generic
(we could pass any `α → Bool` function), the container is generic,
and the logic is container-agnostic. This is abstraction paying
off: one definition, infinite reuse.

### Exercise 4: Pre-order Traversal with `PreTree`

The `Tree` instance above uses in-order traversal: left subtree,
then the value, then the right subtree. But folding isn't married
to any particular order -- the recursive structure is the same,
only the arrangement changes.

`PreTree` is structurally identical to `Tree` (same constructors,
same shape). The only difference is its `Foldable` instance: when
you reach a `node`, visit the value *first*, then the left subtree,
then the right subtree. Because a type can only have one canonical
`Foldable` instance, and we want to show that *different orders
are possible*, we need a separate type.
@@@ -/

inductive PreTree (α : Type) where
| leaf
| node (v : α) (l : PreTree α) (r : PreTree α)

/- @@@
Notice we rearranged the fields in the `node` constructor:
`v : α` comes before the subtrees, matching the pre-order
traversal (visit value first). This isn't strictly necessary
for the instance to work, but it makes the structure self-documenting.

For pre-order folding, the key insight is: we want the combining
function to see elements in pre-order (value first, then left,
then right). In `foldr` terms, that means:
  `f v (foldr-left-subtree (foldr-right-subtree z))`

This threads the value through as the first element, then folds
the left subtree into that result, then folds the right subtree
into the left's result.
@@@ -/

def preTreeFoldr {α β : Type} (f : α → β → β) (z : β) : PreTree α → β
| PreTree.leaf => z
| PreTree.node v l r => f v (preTreeFoldr f (preTreeFoldr f z r) l)

instance : Foldable PreTree where
  foldr := preTreeFoldr

-- Same tree shape, but as a PreTree:
def samplePreTree : PreTree Nat :=
  PreTree.node
    2
    (PreTree.node 1 PreTree.leaf PreTree.leaf)
    (PreTree.node 3 PreTree.leaf PreTree.leaf)

#eval toList sampleTree       -- [1, 2, 3]  (in-order)
#eval toList samplePreTree    -- [2, 1, 3]  (pre-order)

/- @@@
Pre-order visits the value before its subtrees, so `2` comes
first, then `1` from the left, then `3` from the right.
In-order visits left subtree, then value, then right subtree,
giving us the sorted order: `1`, `2`, `3`. One tree structure,
two different instances, two different traversal orders. The
whole point of `Foldable` is that we don't have to rewrite
`toList` -- it works off `foldr` alone, and `foldr`'s implementation
*is* the traversal order.

### Exercise 5: `Foldable.foldr` vs. `ForIn`

`Foldable` and `ForIn` are solving related but distinct problems.
`Foldable.foldr` takes a container and a pure combining function
(no side effects allowed), and uses the function to thread values
through a computation that produces one final result. `ForIn` is
designed for imperative-style `for x in xs do ...` loops: it
threads side effects (printing, modifying mutable state, throwing
exceptions) through the iteration, and the goal is often *not* to
produce a final value but just to perform those effects in order.

For example, with `Foldable`, you combine values into one result:
@@@ -/

#eval fold sampleTree  -- one number: 6

/- @@@
With `ForIn`, you perform side effects for each element (on a `List`,
which has a `ForIn` instance):
@@@ -/

def printList (xs : List Nat) : IO Unit := do
  for x in xs do
    IO.println s!"Element: {x}"

#eval printList [1, 2, 3]
-- Prints:
-- Element: 1
-- Element: 2
-- Element: 3

/- @@@
`foldr` gives you compositional abstraction -- you can nest folds,
combine fold results, reason about what one fold computes -- while
`forIn` is built for sequential iteration with side effects, where
that kind of composition doesn't make as much sense. In other
words: `Foldable` is for *functional* consumption of containers,
`ForIn` is for *imperative* iteration over them. You could
implement `ForIn` using `Foldable` (fold over each element,
performing the effect), but `forIn` is often backed by different
recursion that's optimized for side effects, while `foldr` is
optimized for pure functional composition.
@@@ -/

end GeneralizedFold
