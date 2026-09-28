/- @@@
# 6. Grow

The fourth builder, and the one that makes the kit complete rather than
merely tidy.

Everything you have built so far is of fixed size. A `Point` has two
fields. A `Light` has three cases. A `Status` carries a code and a
reason. You can look at the type and know, in advance, the shape of every
value it has.

Real data is not like that. A shopping list has as many items as it has.
A folder contains folders. A sentence is words, and there is no longest
sentence. You cannot enumerate the cases, because there are unboundedly
many.

The move is startling the first time and obvious afterwards: **let the
type mention itself**.
@@@ -/

namespace C06

/- @@@
## 6.1 Counting numbers, from nothing

Start with the smallest possible example. What is a natural number? Two
answers, and the second one is the trick:

- it is zero, or
- it is one more than some natural number.

That is a complete definition, and notice that the second case refers to
the thing being defined. Written down:
@@@ -/

inductive Counter where
  | zero
  | succ (previous : Counter)
deriving Repr

/- @@@
Two constructors, one of which carries a `Counter`. From those two rules
every counting number is reachable, and only counting numbers are:
@@@ -/

def zero  : Counter := .zero
def one   : Counter := .succ .zero
def two   : Counter := .succ (.succ .zero)
def three : Counter := .succ (.succ (.succ .zero))

#eval three

/- @@@
Count the values. Chapter 2 gave us an arithmetic, so apply it: a
`Counter` is one case carrying nothing, plus one case carrying a
`Counter`. If `c` is the number of `Counter`s, then `c = 1 + c`. No
finite number satisfies that — and that is exactly the point. The
self-reference is what buys us unboundedly many values from two lines of
definition.

## 6.2 Recursion: the function follows the type

Now write a function over `Counter`. There are two cases in the type, so
there are two cases in the function, and the second one is allowed to
call the function being defined:
@@@ -/

def toNat : Counter → Nat
  | .zero      => 0
  | .succ prev => toNat prev + 1

#eval toNat three
#eval toNat (.succ three)

/- @@@
Follow `toNat three` by hand, because this is the mechanism and it is
worth seeing once:

```
toNat (succ (succ (succ zero)))
  = toNat (succ (succ zero)) + 1
  = (toNat (succ zero) + 1) + 1
  = ((toNat zero + 1) + 1) + 1
  = ((0 + 1) + 1) + 1
  = 3
```

Each step peels one `succ` and hands the smaller value back to `toNat`.
The peeling must stop, because you cannot peel forever from a finite
value — eventually you hit `.zero`, the case with no recursive call, and
the whole thing unwinds.

This shape is the template for every recursive function you will ever
write:

> **One branch per case. The non-recursive cases give an answer
> outright. The recursive cases call the function on a strictly smaller
> piece and build the answer from what comes back.**

Addition follows it too. Adding zero to `m` is `m`; adding one-more-than-`n`
to `m` is one more than `n + m`:
@@@ -/

def add : Counter → Counter → Counter
  | .zero,      m => m
  | .succ prev, m => .succ (add prev m)

#eval toNat (add two three)
#eval toNat (add three three)

/- @@@
> **Checkpoint — recursion unwinds.** `toNat (add one two)` builds a
> `Counter` and then counts it. **Predict** the number, then check.
@@@ -/

#eval toNat (add one two)   -- predict first

/- @@@
## 6.3 The real `Nat`

Lean's built-in `Nat` is defined exactly as above — `zero` and `succ` —
with fast arithmetic underneath for the sizes real programs use. What you
get in exchange for the built-in version is nicer patterns: write `0` for
the base case and `n + 1` for the successor case.
@@@ -/

def factorial : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 0
#eval factorial 5
#eval factorial 20

def sumTo : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + sumTo n

#eval sumTo 10       -- 55
#eval sumTo 100      -- 5050

/- @@@
In the `n + 1` branch, `n` is the number one smaller — already bound and
ready to recurse on. The pattern *is* the peeling.

> **Checkpoint — the base case does the stopping.** `factorial 0` is `1`
> by the first branch. **Predict** `factorial 4`, and say how many times
> the second branch fires before the first one does.
@@@ -/

#eval factorial 4   -- predict first

/- @@@
## 6.4 Lean insists that recursion stops

A recursive definition that does not get smaller is not a program, it is
a hang. Lean will not accept one. Uncomment either of these to see it
refuse:
@@@ -/

-- def spin (n : Nat) : Nat := spin n
-- def worse (n : Nat) : Nat := worse (n + 1)

/- @@@
The error says it cannot show the definition terminates, and it is right
to complain: `spin 3` would call `spin 3` forever.

What Lean checks is **structural recursion** — that every recursive call
is on a piece strictly *inside* the argument it was given. `factorial`
passes, because `n` is structurally smaller than `n + 1`. `spin` fails,
because `n` is not smaller than `n`.

This is a real constraint and it is on your side. Every function you
manage to define is a function that finishes. The category of bug where
a program stops responding and you cannot see why simply does not arise
from this kind of definition.

(Recursion that shrinks in some less obvious way — halving a number,
consuming a queue — can still be written, by telling Lean what is
decreasing. That is beyond this book; structural recursion covers a
great deal, and it covers everything here.)

## 6.5 Lists

A list is the same idea, with cargo. What is a list of numbers?

- it is empty, or
- it is one number followed by a list of numbers.
@@@ -/

inductive NatList where
  | empty
  | cons (head : Nat) (tail : NatList)
deriving Repr

def myList : NatList := .cons 3 (.cons 1 (.cons 4 .empty))

#eval myList

/- @@@
Functions over it follow the template — one case for `empty`, one for
`cons`, recursing on the tail:
@@@ -/

def length : NatList → Nat
  | .empty       => 0
  | .cons _ rest => 1 + length rest

def sum : NatList → Nat
  | .empty       => 0
  | .cons n rest => n + sum rest

def largest : NatList → Nat
  | .empty       => 0
  | .cons n rest => max n (largest rest)

#eval length myList
#eval sum myList
#eval largest myList

/- @@@
Three functions, one shape. `length` ignores the head and counts.
`sum` adds it. `largest` compares. The recursion is identical in all
three, which should make you suspicious that it could be written once —
and in Chapter 7 it is, and it is called `fold`.

Lean's built-in `List` is this type, with better notation: `[]` for
empty, `::` for cons, and `[3, 1, 4]` as shorthand for the whole thing.
@@@ -/

def realList : List Nat := [3, 1, 4]

#eval realList
#eval 3 :: [1, 4]              -- the same list
#eval realList.length
#eval [1, 2] ++ [3, 4]         -- append

/- @@@
And you can pattern-match it the same way, with `[]` and `x :: rest`:
@@@ -/

def sumList : List Nat → Nat
  | []           => 0
  | x :: rest    => x + sumList rest

def countEvens : List Nat → Nat
  | []        => 0
  | x :: rest => (if x % 2 == 0 then 1 else 0) + countEvens rest

#eval sumList [1, 2, 3, 4, 5]
#eval countEvens [1, 2, 3, 4, 5, 6]

/- @@@
> **Checkpoint — matching a list.** `sumList` adds the head to the sum
> of the tail, and `[]` contributes `0`. **Predict** `sumList [10, 20]`
> and `countEvens [2, 4, 5]`, then check.
@@@ -/

#eval sumList [10, 20]        -- predict first
#eval countEvens [2, 4, 5]    -- predict first

/- @@@
Two more, because they show recursion building structure rather than just
consuming it:
@@@ -/

def append : List Nat → List Nat → List Nat
  | [],        ys => ys
  | x :: rest, ys => x :: append rest ys

def reverse : List Nat → List Nat
  | []        => []
  | x :: rest => reverse rest ++ [x]

#eval append [1, 2] [3, 4]
#eval reverse [1, 2, 3, 4]

/- @@@
## 6.6 Trees

Lists recurse once per case. Nothing stops a type from recursing twice,
and that is where the shape stops being a line and becomes interesting.

A binary tree of numbers:

- is a leaf, carrying nothing, or
- is a node carrying a left tree, a number, and a right tree.
@@@ -/

inductive Tree where
  | leaf
  | node (left : Tree) (value : Nat) (right : Tree)
deriving Repr

def tiny : Tree := .node .leaf 5 .leaf

def sample : Tree :=
  .node
    (.node .leaf 1 (.node .leaf 3 .leaf))
    4
    (.node .leaf 7 .leaf)

#eval tiny

/- @@@
Drawn, `sample` is:

```
        4
       / \
      1   7
       \
        3
```

Every function over it makes *two* recursive calls, one per subtree, and
combines the results:
@@@ -/

def size : Tree → Nat
  | .leaf         => 0
  | .node l _ r   => size l + 1 + size r

def depth : Tree → Nat
  | .leaf         => 0
  | .node l _ r   => 1 + max (depth l) (depth r)

def total : Tree → Nat
  | .leaf         => 0
  | .node l v r   => total l + v + total r

def contains (target : Nat) : Tree → Bool
  | .leaf       => false
  | .node l v r => v == target || contains target l || contains target r

#eval size sample
#eval depth sample
#eval total sample
#eval contains 3 sample
#eval contains 99 sample

/- @@@
Flattening a tree into a list, left to right, is the one that convinces
people that recursion is worth learning. Three lines, and it handles
every tree there is:
@@@ -/

def toList : Tree → List Nat
  | .leaf       => []
  | .node l v r => toList l ++ [v] ++ toList r

#eval toList sample       -- [1, 3, 4, 7]

/- @@@
Building structure works the same way. Mirroring a tree is swapping the
subtrees, recursively:
@@@ -/

def mirror : Tree → Tree
  | .leaf       => .leaf
  | .node l v r => .node (mirror r) v (mirror l)

#eval toList (mirror sample)      -- [7, 4, 3, 1]
#eval toList (mirror (mirror sample))

/- @@@
> **Checkpoint — two recursive calls.** `size` counts nodes and `depth`
> counts levels. **Predict** `size tiny` and `depth tiny`, then check,
> and say why they differ.
@@@ -/

#eval size tiny    -- predict first
#eval depth tiny   -- predict first

/- @@@
Try writing `toList` with a loop and an index and see how far you get.
The recursive version is short because it matches the shape of the data
exactly: the definition of `Tree` has two cases, so `toList` has two
cases, and there is nowhere for a mistake to hide.

## 6.7 What you have

| Idea | Shape |
|---|---|
| a type that mentions itself | one or more constructors carrying the type |
| the base case | a constructor with no recursive part; the function answers outright |
| the recursive case | a constructor carrying the type; the function calls itself on it |
| termination | every call is on a structurally smaller piece, and Lean checks it |
| one recursive field | a chain: `Counter`, `List` |
| two recursive fields | a tree: branching, and `depth` less than `size` |

The habit to take away: **write the type first, then let it dictate the
function.** Count the constructors — that is how many branches you need.
Look at which constructors carry the type — that is where the recursive
calls go. Recursive functions stop being a puzzle and become
transcription.

## Exercises

**[6.1]** Define `double : Counter → Counter` over §6.1's `Counter`
without converting to `Nat`. Two cases; the recursive one adds two
`succ`s.

```lean
#guard toNat (double three) = 6
#guard toNat (double zero) = 0
```

**[6.2]** Define `power : Nat → Nat → Nat` so that `power b e` is `b` to
the `e`, recursing on the exponent. What is the base case, and what does
it have to return so that `power 2 0` is right?

```lean
#guard power 2 0 = 1
#guard power 2 10 = 1024
#guard power 5 3 = 125
```

**[6.3]** Define `countDown : Nat → List Nat` so that `countDown 3` is
`[3, 2, 1]`. Then `countUp : Nat → List Nat` giving `[1, 2, 3]` — one of
these is a one-line change from the other, and noticing which is the
exercise.

```lean
#guard countDown 3 = [3, 2, 1]
#guard countDown 0 = []
#guard countUp 3 = [1, 2, 3]
```

**[6.4]** Define `member : Nat → List Nat → Bool`, true when the number
appears. Then say how many elements it examines in the worst case, and
in the best.

```lean
#guard member 3 [1, 2, 3] = true
#guard member 9 [1, 2, 3] = false
#guard member 1 [] = false
```

**[6.5]** Define `leaves : Tree → Nat`, counting the `.leaf`s rather
than the nodes. Check it on `sample` and `tiny`, then state the
relationship between `leaves t` and `size t` for every tree — and
confirm it on both.

```lean
#guard leaves tiny = 2
#guard leaves sample = 5
```

**[6.6]** `mirror (mirror t)` gave back the original in §6.6. Check that
on two more trees of your own. Then explain, in two sentences and no
code, why it must hold for every tree: what does `mirror` do at a leaf,
and what does it do at a node?

**[6.7]** A classmate writes:

```lean
-- def sumDown (n : Nat) : Nat := n + sumDown (n - 1)
```

and cannot see why Lean rejects it. Say precisely which requirement
from §6.4 it fails, and what goes wrong at `n = 0`. Then fix it by
matching on `0` and `n + 1`.

```lean
#guard sumDown 4 = 10
#guard sumDown 0 = 0
```
@@@ -/

end C06
