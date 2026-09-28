/- @@@
# 1. Values and Types

Programming is writing down expressions and letting the machine work
out what they mean. That is nearly the whole story; the rest of this
book is about *which* expressions are worth writing down.

Two commands run this chapter. `#eval` takes an expression and computes
it. `#check` takes an expression and tells you its *type* without
computing anything.
@@@ -/

namespace C01

/- @@@
## 1.1 Expressions and evaluation

An expression is any piece of text with a value. `2 + 3` is an
expression. So is `2`. So is `"hello" ++ ", world"`.

`#eval` reduces an expression, one step at a time, until no step is
left. The thing it cannot reduce any further is the *value*.
@@@ -/

#eval 2 + 3                    -- 5
#eval 2 + 3 * 4                -- 14, not 20: `*` binds tighter than `+`
#eval (2 + 3) * 4              -- 20
#eval "hello" ++ ", world"     -- "hello, world"
#eval "hello".length           -- 5

/- @@@
The machine has exactly one job: rewrite until it cannot. `2 + 3 * 4`
becomes `2 + 12` becomes `14`. Nothing is happening that you could not
do on paper — the machine is only faster and never bored.

> **Checkpoint — precedence.** `*` is applied before `+`, and
> parentheses override that. **Predict** the two values below, and say
> which rule makes them differ, before you look.
@@@ -/

#eval 10 - 2 * 3     -- predict first
#eval (10 - 2) * 3   -- predict first

/- @@@
## 1.2 Every expression has a type

A **type** is a name for a collection of values. `Nat` is the type of
the counting numbers `0, 1, 2, 3, …`. `String` is the type of text.
Every expression in Lean has exactly one type, and Lean works it out
before running anything.

`#check` shows it. Read `e : T` as "`e` is of type `T`".
@@@ -/

#check 42            -- Nat
#check "hello"       -- String
#check true          -- Bool
#check 'x'           -- Char
#check (-7 : Int)    -- Int
#check (1.5 : Float) -- Float

/- @@@
You can also *demand* a type, with a colon. This is how you say what
you mean when a literal could belong to several types:
@@@ -/

#check (42 : Nat)
#check (42 : Int)
#check (42 : Float)

/- @@@
And when the demand is impossible, Lean refuses before your program
ever runs. Uncomment the next line to watch it happen — the error
message is worth reading in full.
@@@ -/

-- #check ("hello" : Nat)

/- @@@
This is the central service a type system performs. A whole category of
mistake — adding a number to a name, asking for the length of a
temperature — is not caught *late*, by a user, in production. It is
caught *now*, by you, while you are still holding the problem in your
head.

## 1.3 Naming things with `def`

`def` binds a name to a value, once and for all. Names in this language
do not change their value afterwards; there is no assignment to undo,
which removes an entire genre of bug.
@@@ -/

def answer : Nat := 42
def greeting : String := "hello"
def tau : Float := 6.28318

#eval answer
#eval answer * 2
#eval greeting ++ ", " ++ greeting

/- @@@
Write the type after the name (`: Nat`) whenever you can. Lean can
usually infer it, but the annotation is a claim you are making, and
having the machine check your claims is the point.

`let` does the same job *inside* an expression, for a name you only
need locally:
@@@ -/

def circleArea : Float :=
  let r := 3.0
  let pi := 3.14159
  pi * r * r

#eval circleArea

/- @@@
> **Checkpoint — `def` and `let`.** `answer` is `42`, and `circleArea`
> multiplies `3.14159` by `3.0` twice. **Predict** the value below —
> roughly is fine — then check.
@@@ -/

#eval circleArea + 1.0   -- predict first

/- @@@
## 1.4 The stock atoms

Some types come with the language. You will use these constantly, so
here they are with their essential operations. Nothing here is deep;
skim it and come back when you need it.

**`Nat`** — whole numbers from zero up, with no upper limit. There is
no largest `Nat`; the machine grows them as needed.
@@@ -/

#eval 7 + 5
#eval 7 * 5
#eval 7 / 2      -- 3: whole-number division rounds toward zero
#eval 7 % 2      -- 1: the remainder
#eval 3 - 10     -- 0, and not what you expected

/- @@@
That last one deserves a word. `Nat` has no negative values, so
subtraction that would go below zero stops at zero instead. This is not
a bug, it is a consequence of the type: `3 - 10` must be a `Nat`, and
`-7` is not one. If you want negatives, ask for `Int`.
@@@ -/

#eval (3 - 10 : Int)   -- -7

/- @@@
> **Checkpoint — truncated subtraction.** On `Nat`, a subtraction that
> would go negative yields `0`. **Predict** both lines below, and note
> that the *types* are what make them differ.
@@@ -/

#eval (5 - 8 : Nat)   -- predict first
#eval (5 - 8 : Int)   -- predict first

/- @@@
**`String`** — text. Join with `++`, and ask about it with the
functions hanging off the dot.
@@@ -/

#eval "lean" ++ " " ++ "4"
#eval "lean".length
#eval "lean".toUpper
#eval "lean".append "!"
#eval "l,e,a,n".splitOn ","

/- @@@
**`Bool`** — the type with exactly two values, `true` and `false`. This
is the type of every question the machine can answer yes or no.
@@@ -/

#eval true
#eval !true              -- false: `!` flips a Bool
#eval true && false      -- false: `&&` is "both"
#eval true || false      -- true:  `||` is "at least one"

-- Comparisons produce Bools
#eval 3 == 3             -- true
#eval 3 != 4             -- true
#eval 3 < 4              -- true
#eval "a" == "b"         -- false

/- @@@
> **Checkpoint — `Bool` operators.** `&&` needs both sides true, `||`
> needs one, and `!` flips. **Predict** the value of the expression
> below, then check.
@@@ -/

#eval (4 == 4 && 2 < 1) || !(3 > 5)   -- predict first

/- @@@
`Bool` is also how you choose between two expressions, with
`if … then … else`. Note that both branches must have the *same* type —
an `if` is an expression with one value, so it must have one type.
@@@ -/

def describe (n : Nat) : String :=
  if n == 0 then "zero"
  else if n < 10 then "small"
  else "big"

#eval describe 0
#eval describe 7
#eval describe 1000

/- @@@
## 1.5 The two atoms you have never met

Now the two that make this book's kit work, and that most languages
either hide or get wrong.

**`Unit`** — the type with exactly **one** value. That value is written
`()`.
@@@ -/

#check ()
#eval ()

/- @@@
What use is a type with one value? Consider: if I hand you a value of
type `Unit`, how much have I told you? Nothing at all — you already
knew which value it would be. `Unit` is the type that carries *no
information*.

That is exactly what you want as the result of something done purely
for its effect. A function that prints to the screen has nothing to
return, but in a language where every expression has a value, it must
return *something*. It returns the one value that says nothing.
@@@ -/

def shout (s : String) : IO Unit := IO.println (s ++ "!")

#eval shout "hello"

/- @@@
**`Empty`** — the type with **no** values at all.
@@@ -/

#check Empty

/- @@@
There is no `#eval` to show you, and that is the entire point: you
cannot write down a value of type `Empty`, because there is not one to
write. A value of `Empty` will never arrive, so any code that would
receive one will never run.

This sounds useless and is not. A type with no values is how you say
"this cannot happen" in a way the machine can check — and it is where
the arithmetic of the next chapter gets its zero. Set it aside for now;
you will want it in Chapter 2 and again in Chapter 4.

## 1.6 What you have

| Type | Values | Used for |
|---|---|---|
| `Empty` | none | a case that cannot occur |
| `Unit` | `()` only | a result carrying no information |
| `Bool` | `true`, `false` | a yes-or-no answer, a choice of two |
| `Nat` | `0, 1, 2, …` | counting, sizes, indices |
| `Int` | `…, -1, 0, 1, …` | quantities that can go below zero |
| `Float` | approximate reals | measurement, geometry, graphics |
| `Char` | `'a'`, `'Z'`, … | one character |
| `String` | `"text"` | text |

Three of these — `Empty`, `Unit`, `Bool` — are the atoms of the kit,
because they have zero, one, and two values. The rest are conveniences
the language supplies so you do not have to build arithmetic yourself.

Notice what is *missing*: there is no type here for a point, a
customer, a playing card, a shopping cart, a move in a game. The stock
types will never cover your actual problem. The next five chapters are
about building the type your problem needs.

## Exercises

**[1.1]** Predict, then check, each of: `17 % 5`, `17 / 5`,
`(17 / 5) * 5 + (17 % 5)`. Then say in one sentence why the third
result is what it is, in terms of the first two.

```lean
#guard 17 % 5 = 2
#guard 17 / 5 = 3
#guard (17 / 5) * 5 + (17 % 5) = 17
```

**[1.2]** Define `isTeen : Nat → Bool`, true exactly when its argument
is between `13` and `19` inclusive. Use `&&`.

```lean
#guard isTeen 13 = true
#guard isTeen 19 = true
#guard isTeen 12 = false
#guard isTeen 20 = false
```

**[1.3]** Define `initials : String → String → String` so that
`initials "Ada" "Lovelace"` is `"A.L."`. The pieces you need are
`String.get!` … but try `"Ada".take 1` first, and `++`.

```lean
#guard initials "Ada" "Lovelace" = "A.L."
#guard initials "Grace" "Hopper" = "G.H."
```

**[1.4]** A classmate writes `def half (n : Nat) : Nat := n / 2` and
claims `half n * 2` gives back `n`. Find a value of `n` that shows the
claim is wrong, and encode it as the inequality that must hold:

```lean
#guard half 7 * 2 ≠ 7
```

Then state in one line the condition on `n` under which the claim
*does* hold.

**[1.5]** `#check` each of `Nat.succ`, `String.append`, and
`Bool.not`. Write in plain English what each type tells you: how many
arguments the function takes, of what types, and what it gives back.
You have not been shown what these functions *do* — say how much you
can work out from the type alone.

**[1.6]** Uncomment and run each of the following in your own file.
For each, write down the error in your own words before moving on.
This is a reading exercise; the errors are the material.

```lean
-- #eval "3" + 4
-- #eval if 3 then "yes" else "no"
-- #eval (3.5 : Nat)
-- def bad : Nat := "hello"
```
@@@ -/

end C01
