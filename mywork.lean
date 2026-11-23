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



-- next for 9/21


def swap_menu : Sum Chicken Fish → Sum Fish Chicken :=
  fun menu =>
    match menu with
    | Sum.inl c => Sum.inr c  -- Given c : Chicken, put it on the right side using Sum.inr
    | Sum.inr f => Sum.inl f  -- Given f : Fish, put it on the left side using Sum.inl

/- @@@
#2: PROVE: that someone who ordered "Fish, and either
Rice or Potato" should be satisfied to be served
"Rice or Potato, and Fish. Clearly, it's true: you
just have to turn the plate a little! To prove it
it would do to show there's a function that applied
to a whole *meal, "Fish, and either Rice or Potato"
derives and returns a meal, "either Rice or Potato,
and Fish."
@@@-/


/- @@@
That's just commutativity of × again. We proved it by
running the whole proof strategy again for this special
case of the general principle; but we don't have to, as
we have a general "theorem" (swap function) for that.

The reason we prefer to prove generalized theorems or
write general-purpose functions is because we can then
*apply* them where needed without having to reproduce
the whole derivation from scratch. It's makes math work!
@@@ -/

def swap : ∀ (α : Type u) (β : Type v), α × β → β × α := fun _ _ (a, b) => (b, a)

def swap_meal : Fish × (Rice ⊕ Potato) → (Rice ⊕ Potato) × Fish
  | meal => swap Fish (Rice ⊕ Potato) meal

/- @@@
#3: Prove. Here's an example suggesting that × distributes
over ⊕ just as numerical multiplication distributes over
addition: x * (y + z) = x * y + x * z. Show that the
same principle holds for × and ⊕, first in a specific
example, then in general.
@@@ -/

example :
  Fish × (Rice ⊕ Potato) → Fish × Rice ⊕ Fish × Potato
  | (f, rop) => match rop with
    | Sum.inl r => Sum.inl (f, r) -- fish and rice
    | Sum.inr p => Sum.inr (f, p) -- fish and potato

-- #4 Prove the other direction too.
example :
  (Fish × Rice) ⊕ (Fish × Potato) → Fish × (Rice ⊕ Potato)
  | meal => match meal with
    | Sum.inl (f, r) => (f, Sum.inl r) -- fish and rice
    | Sum.inr (f, p) => (f, Sum.inr p) -- fish and potato

/- @@@
### The Curry-Howard Twin of ⊕ is ∨

Just as *And* (∧) is the Curry-Howard twin of *×*,
so *Or* (∨) is the twin of ⊕. Go back and study the
inductive definition of *Sum* (⊕) then compare with
it's logical counterpart, `Or` (∨), copied below.

```lean
inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b
```

Infix notation for the type, *Or P Q*, is *P ∨ Q*.
@@@ -/


-- #5: PROVE: `Or` (∨) is commutative *in general*

example {P Q : Prop} : P ∨ Q → Q ∨ P
| _ => sorry  -- replace with your code

-- #6: Prove ∧ distributes over or in the usual way
example {P Q R : Prop } : P ∧ (Q ∨ R) → P ∧ Q ∨ P ∧ R
| _ => sorry  -- replace this line with your code

-- #7: Prove that ∨ is associative. It's left associative
-- so note that P ∨ Q ∨ R is read as (P ∨ Q) ∨ R.
example {P Q R : Prop } :  P ∨ Q ∨ R → (P ∨ Q) ∨ R
| _ => sorry  -- replace this line with your code
