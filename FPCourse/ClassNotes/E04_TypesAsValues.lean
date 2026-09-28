/- @@@
# Types are Values Too
@@@ -/

/- @@@
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
