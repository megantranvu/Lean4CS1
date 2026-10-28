```lean
-- Only needed for the library's real `Monoid`/`AddMonoid` near the end
-- of this file (`Zero`/`One`/`Add`/`Mul`/`List.sum`/`List.prod` are
-- core Lean and need no import at all); everything above that is
-- deliberately import-free, built entirely from scratch.
import Mathlib.Algebra.Group.Nat.Defs
```

# Map, Fold, and the Algebra That Makes Fold Safe

You've already written several functions that take a
*sequence* of things and boil it down to *one* thing: sum
a list of numbers, multiply a list of numbers, concatenate
a list of strings, find the biggest number in a list. Each
of these is the same shape: repeatedly apply some two-
argument *combining step* to pairs of elements until only
one value is left.

You might picture "multiply together a list of numbers" as
writing `*` between every adjacent pair and evaluating the
result: `2 * 3 * 4`. But that picture quietly breaks down
at the edges. What do you write down for a list with one
element, `[5]`? There's no `*` to write at all -- yet the
answer had better be `5`. And for the *empty* list, `[]`?
There's nothing to multiply, and yet a total function must
still return *some* `Nat`.

The fix is to stop thinking "put the operator between the
elements" and start thinking "start from a base value, and
fold each element into it, one at a time." That's the idea
behind `fold` (sometimes called `reduce`), and it's today's
main event. Along the way we'll meet `map`, its usual
partner, and we'll discover that `fold` is a lot pickier
about its arguments than its type signature lets on --
which is exactly what motivates today's first peek into the
realm of abstract algebra: at the *monoid*.

There are endless tutorials on how to understand different
abstract algebra objects: just check online for tutorials
that try to answer the qusetion, *what's a monad*? Rather
than asking what one of these things is, instead ask what
new super-power does it give you. A monoid, in particular,
let's you lift a *binary* operator, taking two arguments,
to an *n-ary* operator, e.g., to add any number of values,
not just two. The super-power that a monoids gives you is
thus to turn binary operator correctly into an n-ary one.
```lean
namespace AbstractAlgebra
```

## Folding Over Lists By Hand

Let's write the "multiply everything" function directly,
before abstracting anything. A `List α` is built from
exactly two constructors: `List.nil` (the empty list,
usually written `[]`) and `List.cons h t` (usually written
`h :: t`), where `h : α` is the element at the front of the
list and `t : List α` is *the rest of the list*. A total
function on `List α` must say what to do for *both* shapes,
just as the recursors from last class demanded.
```lean
def productNat : List Nat → Nat
| List.nil       => 1
| List.cons h t  => h * productNat t

#eval productNat [2, 3, 4]   -- 24
#eval productNat [5]         -- 5
#eval productNat []          -- 1
```

Look closely at that `List.nil` case: `1`. Why `1`, and not,
say, `0`, or `17`? There's actually only one answer that
makes `productNat` compute the *product* and not some other
function. Walk it through: `productNat [2,3,4]` unfolds to
`2 * (3 * (4 * productNat []))`. Whatever `productNat []`
is, call it `b`, the whole expression is `2 * 3 * 4 * b`.
For that to equal the actual product `24`, you need `b = 1`.
Multiplying by `1` is the only thing you can do to a number
that is guaranteed to *leave it alone* -- and "leave it
alone" is exactly what you want the empty tail of the list
to contribute. We'll come back to this observation; it's
the seed of everything else today.

Here's the same shape again, for addition.
```lean
def sumNat : List Nat → Nat
| List.nil      => 0
| List.cons h t => h + sumNat t

#eval sumNat [2, 3, 4]   -- 9
#eval sumNat []          -- 0
```

## Abstracting the Step: `reduce`

`productNat` and `sumNat` are the *same* function, up to
two choices: which two-argument operator to use (`*` or
`+`), and which value to return for `[]` (`1` or `0`). Let's
lift both choices to parameters.
```lean
def reduce {α : Type} (op : α → α → α) (id : α) : List α → α
| List.nil      => id
| List.cons h t => op h (reduce op id t)

#eval reduce (· * ·) 1 [2, 3, 4]   -- 24, same as productNat
#eval reduce (· + ·) 0 [2, 3, 4]   -- 9,  same as sumNat
#eval reduce String.append "" ["ab", "cd", "ef"]   -- "abcdef"
```

This `reduce` is, in fact, Lean's own `List.foldr`
(`fold`, *from the right*, because the recursion bottoms
out at the right end of the list and builds back up). You
rarely need to write it yourself -- it's in the library --
but you really do want to understand exactly how it works.
```lean
#eval List.foldr (· * ·) 1 [2, 3, 4]   -- 24, (· * ·) is Nat.mul
```

## Well-Typed, But Wrong

`reduce`'s signature, `(α → α → α) → α → List α → α`, is
happy to accept *any* function of the right shape and *any*
value of type `α`. Lean's type checker has no complaints
about the following call.
```lean
#eval reduce (· * ·) 0 [2, 3, 4]   -- ???
```

That evaluates to `0` -- and so does `reduce (· * ·) 0` on
*every* list, except possibly ones you'd expect to have a
zero in them anyway. The bug is easy to see once you look
for it: `op h (reduce op id t)` with `op := (· * ·)` means
every single step multiplies by whatever came before, and
`h * 0 = 0` no matter what `h` is. Once the accumulator is
`0`, it never leaves `0` -- you can never "get off the
ground." The call type-checks perfectly. It is also simply
wrong, in the sense that it does not compute the product of
the list. Well-typed code can still be wrong: the type
system checked that the *pieces fit together*, not that the
*combination means what you wanted*.

What went wrong, precisely? We need `id` to be a value that
`op` can combine with *anything* and get that *same thing*
back -- otherwise folding it in at the base case corrupts
the answer. That property has a name.

**`id` is an identity element for `op`** when, for every `a`,
```
op id a = a   and   op a id = a
```
Check it: is `0` an identity element for `(· * ·)`? We'd
need `0 * a = a` for every `a` -- false already at `a := 1`.
Is `1`? `1 * a = a` and `a * 1 = a` both hold, for every
`Nat`. That's why `1` is the right base case for products,
and `0` is the right base case for sums (`0 + a = a`,
`a + 0 = a`), and `""` is the right base case for string
concatenation.
```lean
def isIdentityFor {α : Type}  (op : α → α → α) (id : α) : Prop :=
  ∀ a, op id a = a ∧ op a id = a

example : isIdentityFor (α := Nat) (· * ·) 1 :=
  fun a => ⟨Nat.one_mul a, Nat.mul_one a⟩   -- ignore proof for now

-- 0 fails -- this is a real, provable fact about Nat, not a style complaint
example : ¬ isIdentityFor (α := Nat) (· * ·) 0 :=
  fun h => absurd (h 1).1 (by decide)       -- ignore proof for now
```

## Associativity: Does Grouping Matter?

Getting `id` right isn't the whole story. `reduce`/`foldr`
groups its combining steps from the *right*:
`op h1 (op h2 (op h3 id))`. Lean's own `List.foldl` groups
from the *left* instead: `op (op (op id h1) h2) h3`. If
`op` doesn't care how its arguments get grouped, these
agree. If it does, they can give genuinely different
answers -- and neither is more "correct" than the other,
which is itself a sign something is off.

**`op` is associative** when, for every `a b c`,
```
op (op a b) c = op a (op b c)
```
Grouping (associativity, a semantic fact about the function)
is a different thing from the *parsing convention* for an
operator's notation. Lean declares `+`, `*`, and `-` as
`infixl` (left-associative *parsing*: `a - b - c` always
*parses* as `(a - b) - c`), and `^` as `infixr`. That choice
only decides what an unparenthesized expression *means
syntactically* -- it says nothing about whether the
*function* is mathematically associative. `+` happens to be
both left-parsed *and* associative, so parenthesization never
matters for it. `-` is also left-parsed, but it is *not*
associative, so which grouping `fold` uses matters a great
deal, as we're about to see. (An operator could also be
declared plain `infix`, with *no* associativity, forcing you
to parenthesize repeated uses by hand -- Lean's own way of
refusing to guess when grouping isn't free to pick.)

Subtraction on `Int` is the cleanest counterexample.
```lean
#eval (1 - 2) - 3   -- -4
#eval 1 - (2 - 3)   -- 2

example : ¬ (∀ a b c : Int, (a - b) - c = a - (b - c)) :=
  fun h => absurd (h 1 2 3) (by decide)
```

Now watch `foldr` and `foldl` diverge on exactly this `op`.
```lean
#eval List.foldr (· - · : Int → Int → Int) 0 [1, 2, 3]   -- 1 - (2 - (3 - 0)) =  2
#eval List.foldl (· - · : Int → Int → Int) 0 [1, 2, 3]   -- ((0 - 1) - 2) - 3 = -6
```

Two "obviously reasonable" ways of reducing the *same* list
with the *same* operator land on `2` and `-6`. Neither is a
bug in `foldr` or `foldl` -- each is doing exactly what it
promises, folding in one particular order. The bug, if there
is one, is in *choosing `-` as a fold operator* for a task
where the order shouldn't matter. (Worth noticing, too:
`0` isn't even a two-sided identity for `-`. `a - 0 = a`
holds, but `0 - a = a` does not -- so this `op`/`id` pair
fails *both* of today's properties at once.)

Exponentiation on `Nat` shows the same non-associativity
without needing negative numbers at all -- just by
parenthesizing one expression two ways.
```lean
#eval (2 ^ 3) ^ 2   -- 64
#eval 2 ^ (3 ^ 2)   -- 512
```

## What `reduce` Actually Needs

Put the two sections together. For `reduce op id` to mean
"the" well-defined combination of a list's elements --
agreeing with `foldl`, agreeing with however you parenthesize
it, and leaving an empty or singleton list sensibly alone --
`op` and `id` jointly need:

1. `op` is **associative**: grouping never changes the answer.
2. `id` is an **identity element for `op`**: folding it in at
   the edge never corrupts the answer.

Neither property is visible in the *type*
`(α → α → α) → α → List α → α`. Both are facts about the
*particular* `op` and `id` you hand in, and nothing stops
you from handing in a well-typed pair that fails them, as
`(· * ·)`/`0` and `(· - ·)`/`0` just showed. A bare function
and a bare value are simply *not enough structure* to carry
the guarantee a fold needs.

The fix is to stop passing `op` and `id` separately, and
instead bundle them *together with proofs that they satisfy
exactly these two properties*. A carrier type, an operator,
an identity element for that operator, where the operator is
associative -- that bundle is called a **monoid**.
```lean
class Monoid (α : Type u) where
  op      : α → α → α
  id      : α
  assoc   : ∀ a b c, op (op a b) c = op a (op b c)
  idLeft  : ∀ a, op id a = a
  idRight : ∀ a, op a id = a
```

## Three Familiar Monoids

You already know these three, even if you've never called
them "monoids" before. For each, the identity element is the
value that "does nothing," and associativity is the fact
that you can insert parentheses anywhere in a chain of the
operator without changing the answer.

- **The additive monoid of `Nat`**: carrier `Nat`, operator
  `+`, identity `0`. Associativity is "regrouping a sum
  doesn't change the total" -- obvious once you picture
  stacking up the same tally marks in a different order.
  `0 + a = a = a + 0`: adding nothing leaves `a` alone.

- **The multiplicative monoid of `Nat`**: carrier `Nat`,
  operator `*`, identity `1`. Same regrouping argument, one
  level up: `(a * b) * c` and `a * (b * c)` both count the
  same rectangular grid of unit squares. `1 * a = a = a * 1`:
  multiplying by nothing-extra leaves `a` alone.

- **The concatenation (or "free") monoid of `String`**:
  carrier `String`, operator `++`, identity `""`. Gluing
  three strings end-to-end gives the same character sequence
  whichever pair you glue first -- that's associativity.
  Gluing on the empty string adds no characters, so it's the
  identity.

A fourth, for the curious: Boolean conjunction, carrier
`Bool`, operator `&&`, identity `true`. Grouping `p && q`
doesn't change whether *all* of them end up true, and
`true && p = p = p && true`. (`||` with `false` is its
mirror image -- see the exercises.)
## Instances: Giving `Nat` and `String` Their Monoid Structure

A monoid is data (an `op`, an `id`) *plus proof obligations*
(`assoc`, `idLeft`, `idRight`). Writing the instance forces
you to actually discharge those obligations -- which is
exactly the assurance the `(· * ·)`/`0` disaster was missing.
The proofs below are just the standard library facts about
`Nat` and `String` that we already leaned on above.
```lean
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
```

Try to build the *multiplicative* monoid for `Nat` the same
way and you'll hit a wall worth noticing: Lean already picked
`Monoid Nat` to mean the additive one, so a second
`instance : Monoid Nat where ...` doesn't *fail to compile* --
it compiles and then leaves instance search to pick one of
the two arbitrarily, which defeats the whole point of a
typeclass. A single type can only wear *one* `Monoid`
instance "by default" this way. (Mathlib's actual fix is to
wrap the carrier in a marker type, `Multiplicative Nat`, so
the *type itself* records which monoid is meant -- out of
scope for today, but good to know the real solution exists.)
This is also why bundling `op` and `id` as explicit
*structure fields* earlier, in `Monoid`, rather than only as
an `instance`, still matters: you can build as many *distinct*
`Monoid Nat` *values* as you like (one for `+`, one for `*`),
you just can't make Lean pick between them for you via `[Monoid α]`
without more machinery.
```lean
set_option warn.classDefReducibility false in
def natMulMonoid : Monoid Nat where
  op      := (· * ·)
  id      := 1
  assoc   := Nat.mul_assoc
  idLeft  := Nat.one_mul
  idRight := Nat.mul_one
```

## `map`: The Other Half of Map-Reduce

`reduce`/`fold` combines a `List α` down to one `α`. Its
usual partner, `map`, goes the other way across a list,
transforming *every* element with the same function without
changing the list's shape or length.
```lean
def map (f : α → β) : List α → List β
| List.nil      => List.nil
| List.cons h t => List.cons (f h) (map f t)

#eval map (· * 2) [1, 2, 3]          -- [2, 4, 6]
#eval map String.length ["ab", "", "xyz"]   -- [2, 0, 3]
```

## A Correct-by-Construction `fold`

Now write `reduce` once more, but this time take a `Monoid α`
*instance* instead of a bare `op`/`id` pair. There is no way
to call this version with an `op`/`id` combination that
fails associativity or the identity laws, because producing
a `Monoid α` value at all requires having already proved
those laws hold.
```lean
def mfold {α : Type} [Monoid α] : List α → α
| List.nil      => Monoid.id
| List.cons h t => Monoid.op h (mfold t)

#eval mfold [2, 3, 4]              -- 9  (uses the Monoid Nat instance: +, 0)
#eval mfold ["ab", "cd", "ef"]  -- "abcdef"
```

And here's `map` and `mfold` working together -- the
classic "map, then reduce" pattern -- tying `String` and
`Nat` together through the one `Monoid Nat` instance in
scope: map every string in the list to its length, then fold
the resulting `List Nat` under addition.
```lean
def totalLength (strs : List String) : Nat :=
  mfold (map String.length strs)

#eval totalLength ["abc", "de", "f"]   -- 6
```

## The Real Library Doesn't Have This Problem

Everything just above -- `natMulMonoid` stuck as a plain `def`, the
aside about `Multiplicative Nat` -- was working around a limitation
of *this lesson's* `Monoid`, not a limitation of monoids as such.
Lean's actual library gives multiplication and addition two different
typeclass *names*, `Monoid` and `AddMonoid`, so `Nat` simply has
*both* instances at once, each found automatically, no workaround
needed.

One wrinkle: inside this `namespace`, the bare name `Monoid` still
means *ours* (`AbstractAlgebra.Monoid`, defined above), so reaching
the library's real one below needs its full name, `_root_.Monoid`.
`AddMonoid` isn't shadowed by anything we defined, so it needs no
prefix.
```lean
-- _root. picks the definition in the root, not this nested, namespace

def foldMonoid {α : Type} [_root_.Monoid α] (xs : List α) : α :=
  xs.foldr (· * ·) 1

def foldAddMonoid {α : Type} [AddMonoid α] (xs : List α) : α :=
  xs.foldr (· + ·) 0

#eval foldMonoid   [2, 3, 4]   -- 24, via the library's Monoid Nat    ( *, 1 )
#eval foldAddMonoid [2, 3, 4]   -- 9,  via the library's AddMonoid Nat ( +, 0 )
```

Same list, two different folds, both resolved by typeclass search
with zero ambiguity -- `[_root_.Monoid Nat]` and `[AddMonoid Nat]` are
two different searches, so nothing has to arbitrate between them. And
this exact pattern is common enough that the library already ships it
under friendlier names than `foldMonoid`/`foldAddMonoid`:
```lean
#eval ([2, 3, 4] : List Nat).prod   -- 24
#eval ([2, 3, 4] : List Nat).sum    -- 9
```

## EXERCISES

1. Prove `isIdentityFor (α := Nat) (· + ·) 0`, mirroring the
   `(· * ·) 1` proof above.

2. Give `Bool` a `Monoid` instance using `&&` and `true`.
   (`Bool.and_assoc`, `Bool.true_and`, and `Bool.and_true`,
   or your own short proofs by `decide`/case split, should do
   it.) Then give `||`/`false` the same treatment as a second,
   separate `Monoid Bool` *value* (following the
   `natMulMonoid` pattern, not a second `instance`, for the
   reason discussed above).

3. `natMulMonoid` above is a value, not an `instance`, so
   `mfold` can't find it automatically. Write a version of
   `mfold` that takes a `Monoid α` as an explicit *argument*
   rather than an instance-implicit one, and use it together
   with `natMulMonoid` to compute a product -- confirm it
   agrees with `productNat` from the very first section.

4. Find a three-element counterexample showing `Nat.div`
   (`/`) is not associative, the same way we did for `Int`
   subtraction. (Careful: `Nat` division truncates, so pick
   numbers where the truncation itself is doing the work.)

5. `List.append` (`++`) is itself associative with identity
   `[]`, for *any* `α` -- not just `String`. State and prove
   `Monoid (List α)`'s three laws using `List.append_assoc`,
   `List.nil_append`, and `List.append_nil`, generalizing the
   `String` instance above.
```lean
end AbstractAlgebra
```


<div class="issue-box">📝 <a href="https://github.com/kevinsullivan/Lean4CS1/issues/new">Report an issue</a> with this section</div>

