-- CHAPTER 0

-- (a) 2 < 3 ∧ 3 < 4 (b) 2 < 3 ∨ 3 < 2 (c) ¬ (2 = 3) (d) ¬ (2 < 3 ∧ 3 < 2)
-- All the claims can be decided because they concrete numbers and basic comparison operators.
-- (a) uses conjunction, (b) uses disjunction, (c) uses equality and negation, and (d) uses conjunction and negation.
#guard decide (2 < 3 ∧ 3 < 4) = true
#guard decide (2 < 3 ∨ 3 < 2) = true
#guard decide (¬ (2 = 3)) = true
#guard decide (¬ (2 < 3 ∧ 3 < 2)) = true



-- I don't know how to make a trace.
def twice {α : Type} (f : α → α) (x : α) : α :=
  f (f x)
#guard twice (· * 2) 3 = 12
#guard twice (fun b => !b) false = false
#guard twice (· + 1) 0 = 2



def mapOption {α β : Type} (f : α → β) : Option α → Option β
  | none => none
  | some x => some (f x)
#guard mapOption (· * 2) (some 5) = some 10
#guard mapOption (· * 2) (none : Option Nat) = none
#guard mapOption (fun b => !b) (some true) = some false
-- This uses the Function and Sum constructors.



#guard (3 - 10) + 10 ≠ 3
-- Side condition, (a - b) + b = a does hold when a >= b



--CHAPTER 1

#check Nat.add --returns sum of two natural numbers
#check Nat.mul -- returns product of two natural numbers
#check String.append --returns concatenation of two strings
-- All these functions are curried and take 2 arguments
#check ∀ α, α → α → α
-- it can return either input argument, but it can't make up a new value of type alpha.


def myStrNat : String × Nat := ("lean", 4)
def MyStrNatSpec : Prop := myStrNat.1 = "lean" ∧ myStrNat.2 > 0
#guard myStrNat.1 = "lean"
#guard myStrNat.2 = 4
#guard decide (myStrNat.1 = "lean" ∧ myStrNat.2 > 0) = true

-- (a) 17 * 23 = 391 (b) 100 < 200 ∧ 200 < 300 (c) ¬ (5 * 5 = 26) (d) (1.0 : Float) = 1.0
-- a, b, and c can be decided because they are concrete numbers and basic comparison operators.
-- d cannot be decided because Float equality is not decidable (floating points often involve rounding errors).
#guard decide (100 < 200 ∧ 200 < 300) = true
#guard decide (¬ (5 * 5 = 26)) = true
-- (d) has no check on purpose: say why `decide` cannot close Float equality.
--     (Hint: what would DecidableEq Float have to certify about NaN?  §1.2, revisited Week 7.)

#guard 3 - 5 + 5 ≠ 3
-- Side condition, (a - b) + b = a does hold when a >= b
