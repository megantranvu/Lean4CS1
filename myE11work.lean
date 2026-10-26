import Mathlib.Algebra.Group.Nat.Defs
namespace AbstractAlgebra

/- @@@
## EXERCISES

1. Prove `isIdentityFor (α := Nat) (· + ·) 0`, mirroring the
   `(· * ·) 1` proof above.

-/

example : isIdentityFor (α := Nat) (· + ·) 0 :=
  fun a => ⟨Nat.zero_add a, Nat.add_zero a⟩

/-

2. Give `Bool` a `Monoid` instance using `&&` and `true`.
   (`Bool.and_assoc`, `Bool.true_and`, and `Bool.and_true`,
   or your own short proofs by `decide`/case split, should do
   it.) Then give `||`/`false` the same treatment as a second,
   separate `Monoid Bool` *value* (following the
   `natMulMonoid` pattern, not a second `instance`, for the
   reason discussed above).

  -/

set_option warn.classDefReducibility false in
def BoolAndMonoid : Monoid Bool where
  op      := (· && ·)
  id      := true
  assoc   := Bool.and_assoc
  idLeft  := Bool.true_and
  idRight := Bool.and_true

set_option warn.classDefReducibility false in
  def BoolOrMonoid : Monoid Bool where
    op      := (· || ·)
    id      := false
    assoc   := Bool.or_assoc
    idLeft  := Bool.false_or
    idRight := Bool.or_false

  /-

3. `natMulMonoid` above is a value, not an `instance`, so
   `mfold` can't find it automatically. Write a version of
   `mfold` that takes a `Monoid α` as an explicit *argument*
   rather than an instance-implicit one, and use it together
   with `natMulMonoid` to compute a product -- confirm it
   agrees with `productNat` from the very first section.

-/

def mfoldExplicit {α : Type} (M : Monoid α) : List α → α -- explicitly pass Monoid arg
  | List.nil      => M.id
  | List.cons h t => M.op h (mfoldExplicit M t)

#eval mfoldExplicit natMulMonoid [2, 3, 4]

/-

4. Find a three-element counterexample showing `Nat.div`
   (`/`) is not associative, the same way we did for `Int`
   subtraction. (Careful: `Nat` division truncates, so pick
   numbers where the truncation itself is doing the work.)

-/

#eval (10 / 5) / 2
#eval 10 / (5 / 2)

/-

5. `List.append` (`++`) is itself associative with identity
   `[]`, for *any* `α` -- not just `String`. State and prove
   `Monoid (List α)`'s three laws using `List.append_assoc`,
   `List.nil_append`, and `List.append_nil`, generalizing the
   `String` instance above.
@@@ -/

set_option warn.classDefReducibility false in
def listAppendMonoid (α : Type) : Monoid (List α) where
  op      := (· ++ ·)
  id      := []
  assoc   := List.append_assoc
  idLeft  := List.nil_append
  idRight := List.append_nil

end AbstractAlgebra
