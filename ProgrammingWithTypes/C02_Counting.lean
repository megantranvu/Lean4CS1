/- @@@
# 2. Counting

This is the chapter that makes the rest of the book short.

The claim is this. The only thing you fundamentally need to know about a
type is **how many values it has**. Every builder in the kit has an
arithmetic — an exact rule for how it changes that count. Once you can
count, you can look at a type you have designed and a situation you are
modelling and check that the two have the same number of cases. When
they do, your program has nowhere to go wrong. When they do not, you can
say precisely which way it will fail.

Programmers who work this way write fewer bugs. Not because they are
more careful, but because they have arranged for whole classes of bug to
be unwritable.
@@@ -/

namespace C02

/- @@@
## 2.1 Counting the atoms

We chose the three atoms by their counts, so this part is immediate.

| Atom | Values | Count |
|---|---|---|
| `Empty` | — | **0** |
| `Unit` | `()` | **1** |
| `Bool` | `true`, `false` | **2** |

Here is `Bool`, exhaustively. Not a sample — the whole type:
@@@ -/

def allBools : List Bool := [true, false]

#eval allBools
#eval allBools.length      -- 2

/- @@@
That is a complete inventory of a type, which is a strange and useful
thing to be able to write down.

## 2.2 `×` multiplies

`α × β` is the type of pairs: an `α` **and** a `β`, carried together.
Write one with a comma in parentheses.
@@@ -/

#check (true, false)
#eval (true, false)
#eval (3, "hi")

/- @@@
How many pairs of `Bool` with `Bool` are there? Pick either value for
the first slot; for each of those, pick either for the second. Two
choices times two choices.
@@@ -/

def allBoolPairs : List (Bool × Bool) :=
  [(true, true), (true, false), (false, true), (false, false)]

#eval allBoolPairs
#eval allBoolPairs.length      -- 4

/- @@@
Four, and the list above is all of them — try to name a fifth.

The general rule: if `α` has `m` values and `β` has `n` values, then
`α × β` has **`m × n`** values. This is why it is called a *product*.

It scales the way multiplication scales, which is worth feeling in your
hands. A `Bool × Bool × Bool` has 8 values. A record of six `Bool`
fields has 64. A record holding a `Nat` and a `String` has more values
than there are atoms in the observable universe, several times over. A
product of large types is enormous, and every one of those values is a
state your program might be in.

> **Checkpoint — products multiply.** `Bool` has 2 values and `Unit`
> has 1. **Predict** the number of values of `Bool × Unit`, then say
> what that means about how much `Bool × Unit` tells you that plain
> `Bool` does not.

## 2.3 `⊕` adds

`α ⊕ β` is the type of *either*: an `α` **or** a `β`, never both, and
you can always tell which one you have. Build one by tagging it, with
`Sum.inl` for the left type or `Sum.inr` for the right.
@@@ -/

#check (Sum.inl true : Bool ⊕ Bool)
#eval (Sum.inl true : Bool ⊕ Bool)
#eval (Sum.inr false : Bool ⊕ Bool)
#eval (Sum.inr "oops" : Nat ⊕ String)

/- @@@
How many values in `Bool ⊕ Bool`? Every value is *either* a tagged
`Bool` from the left (two of those) *or* a tagged `Bool` from the right
(two more). Two plus two.
@@@ -/

def allBoolEithers : List (Bool ⊕ Bool) :=
  [Sum.inl true, Sum.inl false, Sum.inr true, Sum.inr false]

#eval allBoolEithers
#eval allBoolEithers.length      -- 4

/- @@@
The general rule: if `α` has `m` values and `β` has `n` values, then
`α ⊕ β` has **`m + n`** values. Hence *sum*.

Now look carefully at what just happened. `Bool × Bool` has four values
and `Bool ⊕ Bool` has four values, and they are *not the same four*. In
the product, every value carries two booleans. In the sum, every value
carries exactly one boolean plus the knowledge of which side it came
from. Same count, completely different content.

> **Checkpoint — sums add.** **Predict** the number of values of each
> of `Bool ⊕ Unit`, `Unit ⊕ Unit`, and `Bool ⊕ Empty`. For the last
> one, say where the missing values went.

`Bool ⊕ Empty` has `2 + 0 = 2` values — adding a type with no values
adds nothing, exactly as adding zero adds nothing. There is no value you
could put in the right slot, so `Sum.inr` is a constructor you can never
use. `Empty` is the zero of this arithmetic, and that is what it is for.

## 2.4 `→` raises to a power

`α → β` is the type of functions from `α` to `β`. Every value of this
type is a complete rule that answers *for every* `α` with some `β`.

So counting them means counting rules. How many different functions
`Bool → Bool` are there? A function has to answer for `true` and answer
for `false`, and it may answer anything for each. Two choices for the
first answer, two for the second: four functions, and here they all are.
@@@ -/

def alwaysTrue  : Bool → Bool := fun _ => true
def alwaysFalse : Bool → Bool := fun _ => false
def keepIt      : Bool → Bool := fun b => b
def flipIt      : Bool → Bool := fun b => !b

-- Each row is one function's complete behavior: its answer on
-- `true`, then its answer on `false`.
#eval (alwaysTrue  true, alwaysTrue  false)   -- (true,  true)
#eval (alwaysFalse true, alwaysFalse false)   -- (false, false)
#eval (keepIt      true, keepIt      false)   -- (true,  false)
#eval (flipIt      true, flipIt      false)   -- (false, true)

/- @@@
Four rows, four possible pairs of answers, four functions. There is no
fifth function `Bool → Bool` — any one you write must agree with one of
these four everywhere, and is therefore the same function.

The general rule: if `α` has `m` values and `β` has `n` values, then
`α → β` has **`n` to the power `m`** values. One choice of answer, from
`n` options, for each of the `m` possible inputs.

This rule explains three facts that otherwise have to be memorized.

**`α → Unit` has exactly one value.** `1` to any power is `1`. There is
only one thing a function can do if its answer carries no information:
return `()` and be done. So a function returning `Unit` is never
interesting for its *value* — only for what it did along the way.
@@@ -/

def toUnit : Nat → Unit := fun _ => ()

#eval toUnit 5
#eval toUnit 99999    -- the same value; there was never another option

/- @@@
**`Empty → α` has exactly one value too.** Any `n` to the power `0` is
`1`. A function from `Empty` must say what to do for every value of
`Empty`, and there are none, so there is nothing to say. Lean writes
that empty case analysis as `nomatch`:
@@@ -/

def fromEmpty : Empty → Nat := fun e => nomatch e

/- @@@
You cannot call it, because you cannot produce an argument. It exists
and is useless, which is precisely what "one value, carrying no
information" predicts.

**`Bool → Nat` is infinite.** `Nat` has unboundedly many values and
`Bool` has two, so there are as many such functions as there are pairs
of naturals. Most types you build will be infinite this way. Counting
still guides you even when the count is not a number you can write
down — what matters is the *comparison* between your type and your
situation.

> **Checkpoint — functions are exponents.** **Predict** the number of
> values of `Bool → Bool → Bool`. (Read it as `Bool → (Bool → Bool)`,
> and use the count of `Bool → Bool` you already have.)

## 2.5 The arithmetic, assembled

| Kit entry | Written | Count, if `α` has `m` and `β` has `n` |
|---|---|---|
| nothing | `Empty` | `0` |
| one thing | `Unit` | `1` |
| two things | `Bool` | `2` |
| both | `α × β` | `m × n` |
| either | `α ⊕ β` | `m + n` |
| transform | `α → β` | `n` to the power `m` |

The algebra you learned in school, running over types. And it obeys the
laws you would expect, which is a genuine practical convenience rather
than a curiosity:

| Law | Reading |
|---|---|
| `α × Unit` has `m × 1 = m` values | pairing with a no-information value adds nothing |
| `α ⊕ Empty` has `m + 0 = m` values | an alternative you can never build is not an alternative |
| `α × Empty` has `m × 0 = 0` values | *requiring* the impossible makes the whole thing impossible |
| `Unit → α` has `m` to the power `1` values | a function needing no real input is just a value |

Read the third row again, because it is the one that surprises people.
A pair is only as buildable as its hardest component: demand something
unobtainable alongside your data and you have described a type nobody
can ever construct.

## 2.6 Designing by counting

Now the payoff. Here is the method, and it is the working habit this
whole book exists to install.

> **Count the cases in the world. Count the values in your type. Make
> them match.**

Both directions of mismatch hurt, and they hurt differently.

**Too few values: things you cannot say.** Suppose you model a traffic
light with a `Bool`. Two values; three lights. You are now stuck, and
the usual escape is a lie — "`true` means go, `false` means stop, and
we will handle yellow with a separate flag" — which is the beginning of
a long and unhappy story.

**Too many values: things you can say that are nonsense.** This is the
more common and more expensive mistake, because nothing complains. Model
a traffic light with a `String` and you can write `"green"`, but you can
also write `"purple"`, `"GREEN"`, `"gren"`, and `""`. The type permits
billions of values; the world has three. Every extra value is a state
your program can reach and has no sensible behavior for.

Here is the canonical version of that error, the one you will meet in
real code. We are fetching something over a network, and it is either
still in flight, or it arrived, or it failed.
@@@ -/

-- The mistake: three independent flags and fields.
structure BadStatus where
  isLoading : Bool
  content   : String
  errorMsg  : String

/- @@@
Count it. `2 × |String| × |String|`, which is astronomically many — but
the shape of the problem is visible even if we shrink the strings down
to "present or absent", which is `Bool` for counting purposes:
`2 × 2 × 2 = 8`.

Eight states. The world has three. Let us name the five extra:

| `isLoading` | content | error | Meaning |
|---|---|---|---|
| `true` | absent | absent | loading — **legal** |
| `false` | present | absent | succeeded — **legal** |
| `false` | absent | present | failed — **legal** |
| `true` | present | absent | loading, but we already have the answer? |
| `true` | absent | present | loading, but it already failed? |
| `true` | present | present | all three at once |
| `false` | present | present | succeeded *and* failed |
| `false` | absent | absent | finished, with no result and no error |

Five nonsense states. Nobody intends to write them, and they get written
anyway — by a function that sets one field and forgets another, by a
merge of two code paths, by a refactor eighteen months from now. And
every reader of this type has to *guess* which combinations are real,
because the type does not say.

Now count the alternative. Three cases, so build a sum:
@@@ -/

-- 1 for "loading", plus the successes, plus the failures.
def Status : Type := Unit ⊕ String ⊕ String

def loading : Status := Sum.inl ()
def succeeded (content : String) : Status := Sum.inr (Sum.inl content)
def failed (msg : String) : Status := Sum.inr (Sum.inr msg)

#eval loading
#eval succeeded "the data"
#eval failed "connection refused"

/- @@@
`1 + |String| + |String|`. Every value is exactly one of the three real
cases, carrying exactly the data that case has and nothing else. There
is no combination to get wrong, because there are no combinations. The
nonsense states did not get *handled* — they became unwritable.

This is the single most valuable habit in the book: when your data has
alternatives, reach for a **sum**, not a product of flags.

Two honest caveats. First, `Unit ⊕ String ⊕ String` is unreadable, and
nobody should ship it; Chapter 4 shows how to give the three cases real
names while keeping the count identical. Second, matching counts does
not make a program correct — it makes a program *incapable* of a
specific family of mistakes. That is a smaller claim than "correct" and
a much larger one than it sounds.

## 2.7 The checklist

When you sit down to model something, in any language:

1. **List the cases.** What genuinely different situations exist? Write
   them on paper, in words, before you write any code.
2. **Count them.** Exactly how many? If the answer is "three", that is
   your target.
3. **For each case, list what it carries.** The loading case carries
   nothing. The success case carries content. The failure carries a
   message. Different cases carry different things, and that is normal.
4. **Build it.** Alternatives become a **sum**. Data carried together
   becomes a **product**. Something of unbounded size means the type
   will mention **itself** (Chapter 6).
5. **Recount.** Does your type have values the world does not? Name one
   and see whether it is nonsense. If it is, the type is wrong — not the
   code that will later have to cope with it.

Steps 1 through 3 involve no programming at all. That is the point:
nearly all of the thinking in this kind of design happens before you
touch the keyboard, and it is the part that determines whether the code
will be easy or awful.

## Exercises

**[2.1]** Give the number of values of each type, and show the
arithmetic:

(a) `Bool × Bool × Bool`  (b) `Unit ⊕ Unit ⊕ Unit`
(c) `Bool → Unit`  (d) `Unit → Bool`  (e) `Empty × Bool`
(f) `(Bool × Bool) → Bool`

For (f) the answer is larger than most people guess; the exponent rule
is doing the work.

**[2.2]** Write out *every* value of `Unit ⊕ Bool` as a Lean list, the
way §2.3 did for `Bool ⊕ Bool`. Your list's length must equal the count
you predicted.

```lean
#guard allOfThem.length = 3
```

**[2.3]** How many functions `Bool → Unit` are there? Write them all
out. When you have finished, explain why you could not have been asked
to write out every function `Unit → Bool` in a different number of
lines.

**[2.4]** A deck of ordinary playing cards has 52 cards: 13 ranks in
each of 4 suits. Which builder gives you `52` from `13` and `4`, and
why is it that one and not the other? Then: a card is a rank and a suit,
but a card *drawn from a deck* may also be "no card, the deck was
empty". Give the count of that second type in terms of `52`, and say
which builder you used.

**[2.5]** Here is a real design error. A calendar event is modelled as:

```lean
structure Event where
  allDay    : Bool
  startTime : Nat   -- minutes past midnight; meaningless when allDay
  endTime   : Nat   -- likewise
```

Name three values of this type that cannot correspond to any real
event. Then describe — in words, no code needed — a type with exactly
the right number of cases. (Two cases; one of them carries nothing but
the fact that it is all day.)

**[2.6]** Take something you actually know about — a chess move, a
library book's status, a coffee order, a bus timetable entry. Run the
§2.7 checklist on it in prose. List the cases, count them, say what
each carries, and say which builder you would reach for. No code. If
your answer to step 5 is "my type has too many values", write down one
of the nonsense ones; that is the exercise working.
@@@ -/

end C02
