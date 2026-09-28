/- @@@
# Programming with Types

*A short course in programming, built from three atoms and five builders.*

This is a small, self-contained book. It teaches you to program. It
assumes you have never written a line of code, and it stops when you
have written a working interpreter for a little language of your own.

It is short because it is built around a kit rather than a feature
list. Most first courses in programming hand you a language and then
walk its manual: here are the loops, here are the arrays, here are the
classes, here are the exceptions. You end up knowing many things and
not knowing what any of them are *for*.

This book does the opposite. It gives you a very small number of ways
to describe data, and it insists that they are enough. Everything else
you will ever build — a list, a calendar, a bank ledger, a game board,
the syntax tree of a programming language — is those few moves applied
again and again.

## The kit

Three **atoms**. Types that are handed to you, not built from anything.
We distinguish them by the only thing that matters about a type: *how
many different values it has.*

| Atom | Written | How many values |
|---|---|---|
| nothing | `Empty` | 0 |
| one thing | `Unit` | 1 |
| a choice of two | `Bool` | 2 |

Five **builders**. Each takes types you already have and gives you back
a new one. This is where the leverage is.

| Builder | Written | What it means |
|---|---|---|
| **both** | `α × β` | carry an `α` *and* a `β`, together |
| **either** | `α ⊕ β` | carry an `α` *or* a `β`, and know which |
| **transform** | `α → β` | turn any `α` into a `β` |
| **grow** | a type that mentions itself | data of unlimited size |
| **abstract** | a type that takes a type | one design, every element type |

That is the whole kit. Eight entries. You will spend the rest of this
book learning to read a situation and reach for the right one.

## Why a kit, and not a feature list

Because the kit comes with an arithmetic, and the arithmetic tells you
when your design is right.

`Bool` has two values. `Bool × Bool` has four — two choices of the
first paired with two of the second. `Bool ⊕ Bool` has two *plus* two,
so four as well, but they are four *different* values, and the
difference matters enormously in practice. `Bool → Bool` has four too,
and for a third reason.

Once you can count the values of a type, you can ask the question that
separates a careful programmer from a hopeful one:

> Does my type have exactly as many values as the situation has cases?

Too few, and there are real situations you cannot write down. Too many,
and your program contains states that are nonsense — and every one of
those is a bug waiting for a user to find it. Chapter 2 makes this
precise, and it is the one idea in this book worth memorizing.

## The language

We write in **Lean 4**. Do not read anything into that choice yet. It
is a practical programming language with an unusually honest type
system, which is exactly what a book organized around types needs. It
also runs your code the moment you type it, which is how we will learn.

You need Lean installed to follow along. The main book's
[Setting Up Your Machine](../setup.md) does that; come back here when
`#eval 2 + 2` prints `4`.

Everything in these chapters is real, compiled code. Each chapter is a
single Lean file: you can open it, edit it, break it, and see what
happens. That is not a bonus feature of this book, it is the method.

## How to read a chapter

Three habits, and they are the whole study technique:

1. **Predict before you look.** Every chapter has boxed
   **Checkpoints** — a short expression and a request to say what it
   evaluates to *before* reading the answer. A wrong prediction is the
   single most useful event in learning to program, so make real ones.
2. **Type it yourself.** Reading code teaches you much less than
   typing it. Keep a scratch file open.
3. **Break it on purpose.** Change a `+` to a `-`, delete a case from
   a `match`, pass an argument of the wrong type. The error messages
   are a tutor, and they are patient.

Exercises close each chapter. Most ship a block of `#guard` checks:
paste them under your own definition and they must pass. `#guard` is
silent when it succeeds and reports an error when it fails, so the
compiler grades your work and you never have to wonder.

## The road

| | Chapter | What you get |
|---|---|---|
| 1 | [Values and Types](./C01_Values.md) | expressions, evaluation, the three atoms |
| 2 | [Counting](./C02_Counting.md) | the arithmetic of types; designing by counting |
| 3 | [Both](./C03_Both.md) | products, tuples, records |
| 4 | [Either](./C04_Either.md) | sums, variants, `match`, missing values |
| 5 | [Transform](./C05_Functions.md) | functions as values, and functions of functions |
| 6 | [Grow](./C06_Recursion.md) | self-referential data and recursion over it |
| 7 | [Abstract](./C07_Polymorphism.md) | type parameters; `map`, `filter`, `fold` |
| 8 | [Shared Behavior](./C08_Interfaces.md) | type classes: one name, many types |
| 9 | [A Program](./C09_Program.md) | a small language, interpreted, end to end |

Chapter 9 is the point of the other eight. It is a complete program:
data, errors, evaluation, printing, tests, and a `main` you can run.
When it works, you will have used every entry in the kit, and you will
have written a program that most self-taught programmers would not
attempt in their first year.

Start with [Chapter 1](./C01_Values.md).
@@@ -/
