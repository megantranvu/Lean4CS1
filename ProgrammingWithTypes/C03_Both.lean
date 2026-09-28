/- @@@
# 3. Both

The first builder. You have data that belongs together — a width *and* a
height, a name *and* a price *and* a quantity — and you want one value
that carries all of it.

This chapter is the easy one. Products are the part of type design that
every language gets more or less right, and you have probably met them
already as records, structs, or objects-without-the-behavior. We do them
properly here because the *next* builder is the one people get wrong,
and the contrast is instructive.
@@@ -/

namespace C03

/- @@@
## 3.1 Pairs

`α × β` is the type of pairs. Build one with a comma, take it apart with
`.1` and `.2`.
@@@ -/

def origin : Nat × Nat := (0, 0)
def labelled : Nat × String := (7, "seven")

#eval origin
#eval labelled
#eval labelled.1      -- 7
#eval labelled.2      -- "seven"

/- @@@
The two components need not have the same type, and usually do not. That
is the whole reason pairs are more useful than lists for this job: a
pair's components are allowed to be different kinds of thing, and the
type records which is which.

A function can take a pair apart and put a different one together:
@@@ -/

def swap (p : Nat × String) : String × Nat := (p.2, p.1)

#eval swap (7, "seven")

/- @@@
A function can also *return* a pair, which is how you return two things
at once without inventing a name for the combination:
@@@ -/

def divMod (a b : Nat) : Nat × Nat := (a / b, a % b)

#eval divMod 17 5      -- (3, 2)

/- @@@
> **Checkpoint — projections.** `divMod 17 5` is `(3, 2)`. **Predict**
> the two values below before checking, and say which one is the
> remainder.
@@@ -/

#eval (divMod 17 5).1   -- predict first
#eval (divMod 17 5).2   -- predict first

/- @@@
Pairs nest, and `×` groups to the right: `Nat × String × Bool` means
`Nat × (String × Bool)`. So the second component of a triple is itself a
pair, and you reach into it with `.2.1` and `.2.2`.
@@@ -/

def row : Nat × String × Bool := (1, "ada", true)

#eval row.1        -- 1
#eval row.2        -- ("ada", true)
#eval row.2.1      -- "ada"
#eval row.2.2      -- true

/- @@@
The count is what §2.2 said it would be: a pair's values are every
combination of its components' values. `Nat × String × Bool` has
`|Nat| × |String| × 2` of them.

> **Checkpoint — nesting.** `row.2` is a pair. **Predict** what
> `row.2.2` is and what its *type* is, then check.

## 3.2 Positions do not scale

Now watch this get uncomfortable.
@@@ -/

def employee : String × String × Nat × Nat × Bool :=
  ("Ada", "Lovelace", 36, 1815, true)

#eval employee.2.2.1      -- which field is this?

/- @@@
That expression is correct and nobody can read it. `36` and `1815` are
both `Nat`, so the type does not stop you from swapping them; `.2.2.1`
and `.2.2.2.1` differ by one character and mean entirely different
things; and adding a field in the middle silently changes the meaning of
every access after it.

The problem is not the product. Grouping five things together is exactly
right. The problem is identifying the parts by *position*.

## 3.3 Structures give the parts names

A `structure` is a product whose components have names. Same arithmetic,
vastly better ergonomics.
@@@ -/

structure Employee where
  first    : String
  last     : String
  age      : Nat
  hireYear : Nat
  active   : Bool
deriving Repr

/- @@@
Read that as: a value of type `Employee` is a `String` **and** a
`String` **and** a `Nat` **and** a `Nat` **and** a `Bool`. The count is
the product of the five. Nothing has changed arithmetically; we have
only attached labels.

`deriving Repr` asks Lean to write the code that displays an `Employee`,
so `#eval` has something to print. You will want it on nearly every
structure you define.

Build one by naming the fields. Order does not matter, and leaving one
out is an error rather than a silent default:
@@@ -/

def ada : Employee :=
  { first := "Ada", last := "Lovelace", age := 36, hireYear := 1815, active := true }

#eval ada
#eval ada.age
#eval ada.first ++ " " ++ ada.last

/- @@@
`ada.age` instead of `ada.2.2.1`. The field name is the documentation,
the type checker catches a misspelling, and inserting a new field breaks
nothing.

There is also a positional form, `Employee.mk`, and an anonymous
bracket form `⟨…⟩` that works wherever Lean already knows the type. Both
are handy in short definitions and both give up the benefit we just
bought, so prefer the named form for anything a person will read.
@@@ -/

def grace : Employee := Employee.mk "Grace" "Hopper" 45 1943 true
def alan  : Employee := ⟨"Alan", "Turing", 41, 1936, false⟩

#eval grace.last
#eval alan.hireYear

/- @@@
## 3.4 Changing one field

Values do not change. When you want "the same employee, but retired",
you build a new value that copies the old one and overrides what
differs. That is `with`:
@@@ -/

def retiredAda : Employee := { ada with active := false }

#eval retiredAda
#eval ada.active          -- still true: the original is untouched

/- @@@
This is a genuine feature and not a limitation. `ada` means the same
thing everywhere in the program, forever, so no function you call can
quietly alter it behind your back. If you want a changed version, you
say so, and you get a value with a different name.

The natural way to express an update is therefore a *function* from the
old value to the new one:
@@@ -/

def retire (e : Employee) : Employee := { e with active := false }
def birthday (e : Employee) : Employee := { e with age := e.age + 1 }

#eval retire grace
#eval (birthday ada).age     -- 37
#eval ada.age                -- 36

/- @@@
> **Checkpoint — `with` copies.** `birthday ada` produces a new
> `Employee`. **Predict** both values above, and say why the second is
> not `37`.

## 3.5 Structures made of structures

Fields can have any type, including other structures. This is how real
models are built: small pieces, composed.
@@@ -/

structure Point where
  x : Float
  y : Float
deriving Repr

structure Rect where
  corner : Point
  width  : Float
  height : Float
deriving Repr

def unitSquare : Rect := { corner := { x := 0.0, y := 0.0 }, width := 1.0, height := 1.0 }

#eval unitSquare
#eval unitSquare.corner.x
#eval unitSquare.width * unitSquare.height

/- @@@
Functions over these read the way the geometry does:
@@@ -/

def area (r : Rect) : Float := r.width * r.height

def centre (r : Rect) : Point :=
  { x := r.corner.x + r.width / 2.0,
    y := r.corner.y + r.height / 2.0 }

def move (r : Rect) (dx dy : Float) : Rect :=
  { r with corner := { x := r.corner.x + dx, y := r.corner.y + dy } }

#eval area unitSquare
#eval centre unitSquare
#eval move unitSquare 10.0 5.0
#eval area (move unitSquare 10.0 5.0)    -- moving does not resize

/- @@@
> **Checkpoint — composition.** `centre unitSquare` uses the corner at
> the origin and a width and height of `1.0`. **Predict** both of its
> fields, then check.

## 3.6 Comparing and testing

`deriving` can supply more than display. `BEq` gives you `==`, and
`DecidableEq` gives you `=` inside a `#guard`, both by comparing fields
one at a time.
@@@ -/

structure Card where
  rank : Nat
  name : String
deriving Repr, BEq, DecidableEq

#eval ({ rank := 1, name := "ace" } : Card) == { rank := 1, name := "ace" }
#eval ({ rank := 1, name := "ace" } : Card) == { rank := 2, name := "two" }

-- `#guard` is silent when it holds and errors when it does not,
-- which makes it a test the compiler runs for you.
#guard ({ rank := 1, name := "ace" } : Card) = { rank := 1, name := "ace" }
#guard area unitSquare == 1.0
#guard (divMod 17 5) = (3, 2)

/- @@@
Get in the habit now. Every function you write, follow it with a
`#guard` or two covering an ordinary case and an awkward one. They cost
a line, they run on every build, and they are the difference between
code you believe and code you hope about.

## 3.7 Tuple or structure?

Use a **pair or triple** when the combination is anonymous and
immediate: a function returning two results, a key next to its value, a
coordinate you are about to take apart on the next line.

Use a **structure** when the combination is a *thing in your problem* —
when it has a name people say out loud, when it has more than three
parts, when two parts share a type and could be confused, or when it
will appear in more than one function's type.

In doubt, use a structure. The cost is five words and you buy back every
future reader's attention, including your own.

## Exercises

**[3.1]** Define `structure Book` with fields `title : String`,
`author : String`, and `pages : Nat`, deriving `Repr` and `DecidableEq`.
Then define `longer : Book → Book → Book` returning whichever has more
pages, preferring the first on a tie.

```lean
#guard (longer ⟨"A", "x", 100⟩ ⟨"B", "y", 300⟩).title = "B"
#guard (longer ⟨"A", "x", 300⟩ ⟨"B", "y", 100⟩).title = "A"
#guard (longer ⟨"A", "x", 200⟩ ⟨"B", "y", 200⟩).title = "A"
```

**[3.2]** Define `minMax : Nat → Nat → Nat × Nat` returning the smaller
then the larger of its two arguments.

```lean
#guard minMax 3 8 = (3, 8)
#guard minMax 8 3 = (3, 8)
#guard minMax 5 5 = (5, 5)
```

**[3.3]** Using `Point` and `Rect` from §3.5, define
`scale : Rect → Float → Rect` that multiplies width and height by a
factor, leaving the corner alone. Then check that scaling by `2.0`
multiplies the area by `4.0`, and say in one line why.

```lean
#guard area (scale unitSquare 2.0) == 4.0
#guard (scale unitSquare 3.0).corner.x == 0.0
```

**[3.4]** How many values does `Book` from [3.1] have, in terms of the
counts of `String` and `Nat`? Now suppose you add a field
`inPrint : Bool`. By what factor does the count grow? Does adding a
field ever *reduce* the number of values a structure has?

**[3.5]** Here is a structure that is the wrong shape:

```lean
structure Measurement where
  celsius    : Float
  fahrenheit : Float
```

Every value carries two numbers, but a real measurement is one
temperature. Name a value of this type that is nonsense, then describe
the two honest designs: one that stores a single number, and one that
stores a number together with which scale it is in. Which builder does
the second one need for the scale, and is it in your kit yet?

**[3.6]** Rewrite the `employee` tuple from §3.2 as a structure, then
look back at `employee.2.2.1` and write down what it was. Were you
right on the first try? Keep the answer in mind the next time a tuple of
five things looks convenient.
@@@ -/

end C03
