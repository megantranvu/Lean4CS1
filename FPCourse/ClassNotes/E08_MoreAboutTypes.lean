/- @@@
# More About Types
@@@ -/

/- @@@
## No Branching on Types

The definition below is an error, because you can't
branch on values of variables of type Type. That's
the rule. The logic would break down were that
allowed, so it's just not.
If you want it you have to simulate it using values
of ordinary types then interpreted as representing as
ordinary data the types of the values they label. You
can pattern match on ordinary data.

On its own this code does not compile. The core reason
is as just stated. You can't write a function that takes
a type, such as Nat or Bool, then branch depending on
which you got. The proximate technical reason for the
build error is that the pattern matching doesn't even
represent Nat or String (left of =>) as the names of
types. Now when a fresh variable such as Nat in this
specific context is used to pattern match an argument
(here the incoming type) it matches any such value.
Thus function will then return "Nat" for everything.
And the error is given because there's nothing left
for the second case to handle--a presumed mistake. So
it says the String case is redundant, as any argument
value would already have been handled by the preceding
case. Hover over Nat or String to the left of the =>s.
You should see Lean knows their types. But now change
Nat to something silly, maybe Hip. Ah hah. The Nat to
the left of => doesn't refer to the ℕ (Nat) type, it
is just an identifier to be bound to the argument. No
matching on inhabitants of Type will work.
@@@ -/

/- @@@
### Why this file still compiles: `#guard_msgs`

The definition below *is* an error -- that is the
whole point of it. But a file that errors would
break `lake build` for the entire course library, so
rather than leave the error loose, we capture it
with Lean's `#guard_msgs` command.

`#guard_msgs in` applies to the one command that
follows it. It runs that command, collects every
message the command produces -- errors, warnings,
and `#eval` output alike -- and compares them
against the text of the docstring `/-- ... -/`
written just above. On a match the messages are
*consumed*: Lean reports nothing and the build
succeeds. On a mismatch `#guard_msgs` itself errors
and prints a diff of expected against actual.

So the error is not silenced, it is *asserted*. The
message we expect is pinned in the source. If a
future Lean reworded it, or if matching on `Type`
ever became legal, the build would fail right here
and say so. Try it: change a word inside the
docstring and rebuild.

Capturing the error does not discard the definition
-- `branchOnType` is still added to the environment,
which is why the three `#eval`s below still run.
Watch what they print: "Nat" every time, exactly as
the reasoning above predicts.
@@@ -/

/--
error: Redundant alternative: Any expression matching
  String
will match one of the preceding alternatives
-/
#guard_msgs in
def branchOnType : Type → String :=
  fun t =>
    match t with
    | Nat => "Nat"
    | String => "String"

#eval branchOnType Nat
#eval branchOnType Bool
#eval branchOnType String

/- @@@
## Types are Values Too

A superpower you get by programming in such languages
is that *types are values,* too. You can make a list
of Type values as easily as a list of Nat values. You
can store them in data structures. Whatever.

The one limitation, not further explained here, is
that you cannot pattern match on, distinguish, or
thus branch values in any type universe (Type u).
(i.e., distinguish, or thus branch on) values of
type Type (Type 0) or higher.

With types as values, you can have lists of them
and much more. Here's a list of types.
@@@ -/

def myBestTypes := [Nat, Bool, String, Bool, Nat, Bool, String]

#eval myBestTypes.length
#check myBestTypes


/- @@@
So what about more. Yes. Store a type as a value
in a data structure. Have that type value inhabit
Prop, so now you're storing a proposition (a type)
as in a data structure. And now here lies the true
gold: you can have a second field holding a value
with its type given by *value* of the first field.

We start with a structure type, typedContainer,
with two "data members" (typed fields). The first
field takes as its value a type in any "universe."
The type of value held in the second is then given
by the *value* of the first field (a type, maybe
even one in Prop, thus a logical proposition.)

Here's an example of a container that you first
specialize by giving a type, and into which you
can then inject any value as long as its of the
type you just specified. Try that in Java.
@@@ -/

structure typedContainer where
-- we'll let Lean use mk as the default single constructor name
(α : Type u)  -- the value of this field is just some type
(a : α)       -- the value of this field is of *that* type!

example := typedContainer.mk Nat 3
example := typedContainer.mk String "Hi!"
-- predict the error then uncomment the code to check yourself
-- example := typedContainer.mk Nat true
#eval (typedContainer.mk Nat 3).a
#eval (typedContainer.mk String "H!").a

/- @@@
Now you learn the magic trick. Propositions are just types
of a certain kind, their values, if any, are their proofs,
so we can do with propositions and proofs of them what we
just did with ordinary data types and values (Nat and 3).
@@@ -/

structure provedTheorem where
(P : Prop)
(p : P)

example := provedTheorem.mk (3 = 3) rfl

example := provedTheorem.mk ("Hi" = "Hi") rfl

example :=
  provedTheorem.mk  -- arg #1: proposition
    (
      let n := 5
      let m := 2
      n + m < 10
    )
  (by decide)       -- arg #2: arithm dec. proc.

def x := 7
def y := 9

-- The conjecture is valid but it's the wrong proof
-- example := provedTheorem.mk (3 = 3) (Eq.refl 4)
-- uncomment that!

-- False proposition precludes larger construction
-- example := provedTheorem.mk (0 = 1) _
-- uncomment the previous line to see the issue

/- @@@
Here's a last example: the type of ordered pairs of
natural numbers where the second is the square of the
first.
@@@ -/

structure SquarePair where
(fst : Nat)
(snd : Nat)
(invariant : snd = fst * fst)

example := SquarePair.mk 1 1 rfl
example := SquarePair.mk 5 25 rfl
--example := SquarePair.mk 5 50 rfl

/- @@@
This is an important example. It shows how you
can not only formally state but also have the
Lean kernel enforce *invariants* over the state
components of otherwise unconstrained types.

Dependent typing is indispensable here. The
*type* of *invariant* depends on the *values*
of both *fst* and *snd*. The proposition (type)
that (3,9) is good is a different proposition
than the one asserting (3,16). Be sure to see
what breaks to cause an error report.

So, voila, a first example proof-carry code in
the form of a data type definition, restricting
the combinations of values that will typecheck
as satisfying the invariants of a structure.
@@@ -/

/- @@@
The same idea works to guard function applications
to ensure their *preconditions* are verified. The
trick is to expres the precondition as a proposition
about the values of the ordinary arguments and then
to require a proof of it as an addition argument to
the function. If you can't construct such a proof,
you can't call the function with those arguments!
Here's a function that takes two Nat arguments but
only if the second is the first one squared. (It's
a sill example but illustrates the point.)
@@@ -/

def squareChecker (n m : Nat) (_h : n*n = m) : Unit :=
  Unit.unit

-- A static square checking function.
-- Purpose is typechecking not return value.
-- So return type is set to Unit (void in C).
#eval squareChecker 1 1 rfl
#eval squareChecker 2 4 rfl
#eval squareChecker 3 9 rfl

-- uncomment: type error blocks application
--#eval squareChecker 3 10 rfl
