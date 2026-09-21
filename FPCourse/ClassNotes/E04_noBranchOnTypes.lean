/- @@@
# No Branching on Types
@@@ -/

/- @@@
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
## Why this file still compiles: `#guard_msgs`

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

@@@-/
