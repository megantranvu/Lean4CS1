/- @@@
# 5. Transform

The third builder. `α → β` is the type of functions from `α` to `β`, and
it is the one entry in the kit that is also the thing you spend all day
writing.

You have been using functions since Chapter 1. This chapter is about the
part that usually goes untaught: a function is a **value**, of a type
like any other, and it can be stored, passed, returned, and built out of
other functions. That single fact is what makes Chapter 7's `map`,
`filter`, and `fold` possible, and it is the difference between writing
the same loop forty times and writing it once.
@@@ -/

namespace C05

/- @@@
## 5.1 Two ways to write one down

The direct way is `fun`, which builds a function value out of nothing:
@@@ -/

def double : Nat → Nat := fun n => n * 2
def negate : Bool → Bool := fun b => !b

#eval double 21
#eval negate true

/- @@@
Read `fun n => n * 2` as "given an `n`, produce `n * 2`". The name `n`
is local to the function and means nothing outside it.

The convenient way puts the arguments to the left of the colon, naming
them as part of the definition:
@@@ -/

def triple (n : Nat) : Nat := n * 3
def shout (s : String) : String := s.toUpper ++ "!"

#eval triple 14
#eval shout "hello"

/- @@@
These two forms mean exactly the same thing. `triple` *is* a value of
type `Nat → Nat`, and you can see that with `#check`:
@@@ -/

#check double
#check triple

/- @@@
Applying a function is juxtaposition — the function, a space, the
argument. No parentheses required, and parentheses mean grouping rather
than "this is a call":
@@@ -/

#eval double 5            -- 10
#eval double (5 + 1)      -- 12: the argument is 6
#eval double 5 + 1        -- 11: application binds tighter than `+`

/- @@@
> **Checkpoint — application binds tightest.** `double 5 + 1` groups as
> `(double 5) + 1`. **Predict** `triple 2 + triple 3`, then check.
@@@ -/

#eval triple 2 + triple 3   -- predict first

/- @@@
## 5.2 Several arguments, one at a time

A function of two arguments is written the way you would expect:
@@@ -/

def add (a b : Nat) : Nat := a + b

#eval add 3 4

/- @@@
But look at its type:
@@@ -/

#check add        -- Nat → Nat → Nat

/- @@@
`Nat → Nat → Nat`, and `→` groups to the right, so that is
`Nat → (Nat → Nat)`: a function that takes one `Nat` and returns *a
function from `Nat` to `Nat`*. There are no two-argument functions in
this language. There are one-argument functions that return functions.

That sounds like pedantry until you use it. Supply one argument and you
get a perfectly good function back, which you can name and reuse:
@@@ -/

def addTen : Nat → Nat := add 10

#eval addTen 5          -- 15
#eval add 10 5          -- 15, the same thing
#eval (add 10) 5        -- 15, spelled out

/- @@@
Giving a function some of its arguments is called **partial
application**, and it is how you build a specific tool out of a general
one without writing any new code:
@@@ -/

def repeatStr (sep : String) (s : String) : String := s ++ sep ++ s

def dashed : String → String := repeatStr "-"
def spaced : String → String := repeatStr " "

#eval dashed "ab"
#eval spaced "ab"

/- @@@
> **Checkpoint — partial application.** `repeatStr` takes a separator
> and then a string. **Predict** `dashed "x"` and `repeatStr "+" "y"`,
> then check.
@@@ -/

#eval dashed "x"          -- predict first
#eval repeatStr "+" "y"   -- predict first

/- @@@
## 5.3 Functions as ordinary values

A function value can go anywhere a value can go. Into a pair:
@@@ -/

def twoOps : (Nat → Nat) × (Nat → Nat) := (double, triple)

#eval twoOps.1 10
#eval twoOps.2 10

/- @@@
Into a list — which is a list whose elements happen to be functions:
@@@ -/

def ops : List (Nat → Nat) := [double, triple, addTen]

#eval ops.length
#eval ops.map (fun f => f 6)     -- apply each one to 6

/- @@@
That last line is worth a second look. `ops.map` applies something to
every element of a list; the something is itself a function that takes
a function `f` and applies it to `6`. Functions holding functions and
handing them around is not an advanced technique — it is just what
"functions are values" means, spelled out.

## 5.4 Functions that take functions

A function whose *argument* is a function is called higher-order. Here is
the smallest useful one: do this twice.
@@@ -/

def twice (f : Nat → Nat) (n : Nat) : Nat := f (f n)

#eval twice double 5     -- 20: double 5 is 10, double 10 is 20
#eval twice triple 1     -- 9
#eval twice addTen 0     -- 20

/- @@@
`twice` knows nothing about doubling. It knows how to repeat a step, and
which step is your business. That separation — the general plan here,
the specific operation supplied by the caller — is the whole idea of
higher-order functions, and Chapter 7 shows that `map`, `filter`, and
`fold` are the three shapes of it you will use every day.

> **Checkpoint — higher order.** `twice f n` is `f (f n)`. **Predict**
> `twice (fun n => n + 3) 1`, then check.
@@@ -/

#eval twice (fun n => n + 3) 1   -- predict first

/- @@@
A function can also *return* a function it builds on the spot. This one
manufactures adders:
@@@ -/

def adder (k : Nat) : Nat → Nat := fun n => n + k

def inc : Nat → Nat := adder 1
def addHundred : Nat → Nat := adder 100

#eval inc 41
#eval addHundred 41
#eval (adder 7) 35

/- @@@
## 5.5 Composition

Doing one thing and then another is so common it has an operator. `f ∘ g`
is the function that applies `g` first, then `f`.
@@@ -/

def tripleThenDouble : Nat → Nat := double ∘ triple
def doubleThenTriple : Nat → Nat := triple ∘ double

#eval tripleThenDouble 5     -- triple to 15, double to 30
#eval doubleThenTriple 5     -- double to 10, triple to 30

/- @@@
Both give `30` here, because multiplication does not care about order.
Pick operations that do care, and composition stops being symmetric:
@@@ -/

def addOne : Nat → Nat := fun n => n + 1

#eval (double ∘ addOne) 5    -- add first: 6, then double: 12
#eval (addOne ∘ double) 5    -- double first: 10, then add: 11

/- @@@
The right-to-left order reads backwards at first and matches the way you
say it in mathematics. If you would rather read left to right, `|>` pipes
a value forwards through a function:
@@@ -/

#eval 5 |> addOne |> double     -- 12
#eval 5 |> double |> addOne     -- 11

/- @@@
> **Checkpoint — order matters.** **Predict** `(triple ∘ addOne) 3` and
> `(addOne ∘ triple) 3`, then check. Say in one line which operator
> applied first in each.
@@@ -/

#eval (triple ∘ addOne) 3   -- predict first
#eval (addOne ∘ triple) 3   -- predict first

/- @@@
## 5.6 Shorthand you will see everywhere

Writing `fun n => n * 2` gets tiresome. `·` is a hole: put it where the
argument goes, wrap the expression in parentheses, and Lean builds the
function for you.
@@@ -/

#eval (· * 2) 21              -- same as (fun n => n * 2) 21
#eval [1, 2, 3].map (· * 10)
#eval [1, 2, 3, 4].filter (· % 2 == 0)
#eval (· ++ "!") "hi"

/- @@@
Each `·` is one argument, left to right, so `(· - ·)` is a function of
two:
@@@ -/

#eval (· - ·) 10 3
#eval (· ++ ·) "a" "b"

/- @@@
Use it for something short and obvious. When the body gets long enough
that a reader has to hunt for the holes, go back to `fun` and a name.

## 5.7 Defining a function by cases

You have seen this in Chapter 4, and it is worth naming as a third way
to write a function: instead of a body, give a case for each shape the
argument can have.
@@@ -/

def label : Bool → String
  | true  => "yes"
  | false => "no"

def sign : Int → String
  | 0 => "zero"
  | n => if n > 0 then "positive" else "negative"

#eval label true
#eval sign 0
#eval sign (-4)
#eval sign 9

/- @@@
This is the same `match` from Chapter 4, with the `match l with` line
left implicit. Use whichever reads better: a case-per-line definition
when the function is really a table, and `fun` or named arguments when
there is one uniform thing to compute.

## 5.8 What you have

| Idea | Written | Note |
|---|---|---|
| a function value | `fun n => …` | a value of type `α → β` |
| a named function | `def f (n : α) : β := …` | the same thing, with a name |
| application | `f x` | binds tighter than any operator |
| partial application | `f x` where `f` wants more | returns a function |
| higher order | `(α → β) → γ` | takes a function as an argument |
| returning a function | `γ → (α → β)` | builds one and hands it back |
| composition | `f ∘ g` | `g` first, then `f` |
| piping | `x |> f |> g` | the same, read left to right |
| shorthand | `(· * 2)` | one `·` per argument |

And the count, from §2.4: `α → β` has `|β|` to the power `|α|` values.
A function type is usually the largest type in sight, which is another
way of saying that "what should this function do?" is usually the
hardest question in the room.

## Exercises

**[5.1]** Define `applyTwice` for `String → String` (the same shape as
`twice`, different type), then use it with `(· ++ "!")`.

```lean
#guard applyTwice (· ++ "!") "hi" = "hi!!"
#guard applyTwice (fun s => s ++ s) "ab" = "abababab"
```

**[5.2]** Define `compose3 : (γ → δ) → (β → γ) → (α → β) → α → δ`
applying the three functions right to left. Then check that it agrees
with two uses of `∘`.

```lean
#guard compose3 (· + 1) (· * 2) (· + 3) 0 = 7
```

**[5.3]** Define `multiplier : Nat → Nat → Nat` such that
`multiplier 3` is a function multiplying by three. Then define
`triple' := multiplier 3` and `tenTimes := multiplier 10` with no new
`fun`.

```lean
#guard triple' 7 = 21
#guard tenTimes 7 = 70
```

**[5.4]** `#check` each of `twice`, `adder`, and `(· * 2)`. For each,
say how many arguments it takes before it stops being a function, and
what you get if you supply one fewer.

**[5.5]** Predict, then check, each of `(double ∘ double) 3`,
`(twice double) 3`, and `double (double 3)`. All three give the same
answer. Say what that tells you about the relationship between `twice`
and `∘`.

**[5.6]** Someone writes `def apply (f : Nat → Nat) : Nat := f 0` and
complains that it "only ever tests zero". Rewrite it as
`applyAt : (Nat → Nat) → Nat → Nat` so the caller chooses the input,
then show that the original is a partial application of yours.

```lean
#guard applyAt double 21 = 42
#guard applyAt (· + 1) 0 = 1
```

**[5.7]** How many functions are there of type `Bool → Bool → Bool`?
You counted this in [2.4]; now write down the one that is `&&`, the one
that is `||`, and one that ignores its first argument entirely. Then say
how many of the total ignore their first argument, and why.
@@@ -/

end C05
