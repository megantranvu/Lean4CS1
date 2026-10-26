--8/26

--https://live.lean-lang.org/
-- Specifications
#check Empty
#check Unit
#check Bool
#check Nat
#check Int
#check String
#check String → Bool

-- Implementations (of the specs)
#check false
#check (fun _s : String => true)
#reduce (fun _s : String => true) "Hello"



--8/31

/-
https://kevinsullivan.github.io/Lean4CS1/SoftwareLogic/index.html
Lean is a functional programming lang
Specs / types are propositions (ex: Int, 7=7)
Implementations are proofs of the spec / type (ex: 6, a proof that 7 equals 7)
Some specs have no implementations (ex: 6=7 has no existing proof)
Decision procedure – a procedure to decide a problem in a finite number of steps (ex: integer equality is decidable, but floating-point equality is not)

There's like 2 readings to do before Wed class
Get Lean env ready for Wed
Kevin Sullivan hotline: 4344097123

Extra stuff:
Cedar for policy writing?
Ocamel? Pascal? Other functional langs?
What's wrong with git's mental model
The Design of Everyday Things by Don Norman is a good book to read
-/



--9/2

/-
Important commands: Restart File button if code isn't compiling right
Total function – function is defined for all elements in domain, every possible input has an output
Empty type has no possible values (is an uninhabited type), so no function can map to Empty
Type tag on union? For expressing XOR/Sum/Variant type?

Bool -> Empty is invalid (inhabited type to uninhabited type)
Empty -> Empty is valid

Read 2 more papers for next time. Man
-/



--9/7

/-
Lean supports Dependent Type Theory – type definition can depend on another value, ex: Vector Nat 5 type depends on value 5
Prof went through chaps and noted where he may have confused us. Yay!

All types can be considered Prop or Type???
Prop (Sort 0) - for logical stuff
Type (Type 0) (Sort 1) - for computational stuff
Type 1 (Sort 2) - for meta stuff, like an object that has Type 0 fields???
All things have a type, ex: Type of 5 is Nat, Type of Nat is Type 0

Russell's paradox – does the set of all sets contain itself
Java void is like a Unit type (only has one possible value)
The type Unit has one possible implementation (Unit.unit)
example : Unit := Unit.unit

A Prop needs just one proof to be true
The prop True has one possible proof (True.intro)
True := True.intro

Logic has introduction and elimination rules
Introduction – use Type constructors to make values
Elimination – do case analysis to decide what to do with the value
-/

namespace hidden

inductive Bool : Type where
| false : Bool   --two constructors
| true : Bool

def b2s (b : Bool) : String :=   --function that turns bool to string
match b with   --do case analysis
| Bool.true => "It's true"
| Bool.false => "It's false"

inductive Nat : Type where
| Zero : Nat
| Succ (n : Nat)

end hidden



--9/9

/-
How to integrate LLM into VSCode?
Parametric polymorphism – function can take any type as input, ex: List A, Vector A
Overloaded operation - operation has multiple defs depending on input, ex: + operator
A SUM B is a proof of A OR B
A PROD B is a proof of A AND B
-/

#check Nat.add -- this is a function where input is Nat, output is function (Nat → Nat)
-- right associative, like Nat → (Nat → Nat)
#check Nat.add 3 -- this is a function where input is Nat, output is Nat
-- I can name the function from above...
def add3 := Nat.add 3
#check add3 -- waiting for 1 more Nat input
#check add3 7
-- curried function - takes one input at a time, returns a function that takes the next input

def f' (b1 b2 b3 : Bool) : Bool := true -- takes 3 bools and returns true
#check f'
#check f' true -- waiting for 2 more bools
#check f' true false -- waiting for 1 more bool
#check f' true false true


def id' (a : Sort u) : a → a := fun n => n -- takes any Type a, returns an identity function
-- Sort u is like Sort 0, Sort 1, etc, where u is a universe level
#check id' Nat -- returns a function that takes a Nat and returns a Nat
#eval id' Nat 7 -- explicitly state type of 7
#eval id' _ 7 -- Lean infers type of 7 is Nat

def id'' {a : Sort u} (n : a) : a := n -- implicit argument in curly braces, Lean infers type of n is a
#eval id'' 7 -- Lean infers type of 7 is Nat
#eval @id'' Nat 7 -- explicitly state type with @ if you want

-- parametric polymorphism vs ad-hoc polymorphism



-- 9/14 + weekend video

def a : Bool := Bool.true
def b : Bool := Bool.false
def ab : Bool × Bool := (a, b) -- need special /x

def ab_return_a : (Bool × Bool) → Bool
:= fun ab => ab.1 -- returns first element of tuple

theorem disjunction_flip : A ∨ B → B ∨ A := -- disjunction is commutative
fun pq =>
match pq with
| Or.inl p => Or.inr p -- given a proof p for A, construct a disjunction with p on the right
| Or.inr q => Or.inl q -- given a proof q for B, construct a disjunction with q on the left

def swap {A B} : (A × B) → (B × A) := fun ab => (ab.2, ab.1) -- swap elements of a tuple
-- curly braces around implicit arguments
-- (A x B) is an explicit argument, Lean infers type of A and B
#eval swap (7, "Hello")

def swap' {a : Type u} {b : Type v} : (a × b) → (b × a) := fun ab => (ab.2, ab.1) -- swap elements of a tuple
#eval swap' (7, "Hello")

-- involutive function – applying function twice returns original input
#check (swap (swap (7, "Hello")) = (7, "Hello"))

theorem swap_comm : swap ( swap (x, y) ) = (x, y) := rfl -- rfl is same as Eq.refl, reflexivity of equality

-- keyword 'inductive' - defines a type
-- keyword 'structure' - defines a type with one constructor, mk
-- honestly what's the diff between inductive and structure

-- Prod.make = And.intro, introduction rules
-- funny angled brackets to make tuple of proofs /< />



-- 9/16
-- Wth are we doing? shallow embedding of predicate lang constructs as Lean types

inductive Variable where
| X : Variable
| Y : Variable

inductive PropLogic where
| t
| f
| and (p q : PropLogic) : PropLogic
| or (p q : PropLogic) : PropLogic
| not (p : PropLogic) : PropLogic
| variable (v : Variable) : PropLogic

open PropLogic

def X := PropLogic.variable Variable.X
def Y := PropLogic.variable Variable.Y


def eval : PropLogic → (Variable → Bool) → Bool
| t, _ => true
| .f, _ => false
| .and p q, i => eval p i && eval q i
| .or p q, i => eval p i || eval q i
| .not p, i => !(eval p i)
| .variable v, i => i v

def i1 : Variable → Bool
| .X => true
| .Y => true

def e1 := f
def e2:= t
def e3:= PropLogic.and e1 e2
#eval eval e3 i1 -- basically ignoring i1

def e4 := PropLogic.and X Y
#eval eval e4 i1 -- using vals from i1

-- 9/21
-- shallow vs deep embedding
-- shallow - predicate logic
-- deep - propositional logic

def e2e : Empty → Empty
| e => e

theorem f2f : False → False
| f1 => f1


inductive MyEmpty : Type -- no constructors
def me2e : MyEmpty → Empty
| me => nomatch me -- no cases to match, proving that MyEmpty is uninhabited


inductive MyFalse : Prop where -- no constructors
theorem mf2f : MyFalse → False
| mf => nomatch mf -- no cases to match, proving that MyFalse is uninhabited


def neg (a : Prop) : Prop := a → False -- a negation function

example : neg MyFalse
| mf => nomatch mf -- no cases to match, proving that MyFalse is uninhabited

example : ¬ MyFalse
| mf => nomatch mf -- no cases to match, proving that MyFalse is uninhabited


inductive KevinIsFromCville : Prop where
| driversLicense

example : KevinIsFromCville := KevinIsFromCville.driversLicense

inductive JorgIsFromToronto : Prop where
| driversLicense
| utilityBill
| healthCard

example : KevinIsFromCville ∧ JorgIsFromToronto :=
And.intro
    KevinIsFromCville.driversLicense
    JorgIsFromToronto.healthCard


-- prove deMorgan's laws in Lean
-- apparently not all of deMorgan's laws are valid in Lean tho?


-- 9/28

-- classical logic: P ∨ ¬P is always true (law of excluded middle)
-- constructive logic: P ∨ ¬P is not generally valid, we have to have proof

-- proof by negation, derive proof of ¬P by assuming P and deriving False
-- proof by contradiction, derive proof of P by assuming ¬P and deriving False (basically deriving ¬¬P)

-- classical logic: ¬¬P → P (double-negation elimination)
-- constructive logic: ¬¬P → P is not generally valid
-- so proof by contradiction doesn't work in constructive logic



-- 9/30

example {P : Prop} : ¬(P ∧ ¬P) :=
fun h => -- assume we have proof of P ∧ ¬P
  let p : P := h.left
  let np : ¬P := h.right
  np p

-- different way to prove same thing...
example {P : Prop} : ¬(P ∧ ¬P) :=
fun (pnp : P ∧ ¬P) =>
pnp.right pnp.left -- applying ¬P to P to get False

-- sorry: key word used to indicate placeholder in proof

-- a predicate is like a proposition with placeholders...
-- it's like a property

inductive Dog : Type where
| Iris : Dog
| Fido : Dog
| Sargent : Dog

inductive Friendly : Dog → Prop where -- Friendly is a predicate on Dogs
| irisFriendly : Friendly Iris -- Friendly applied to Iris returns proof
| fidoFriendly : Friendly Fido

inductive Furry : Dog → Prop where -- Furry is a predicate on Dogs
| irisFurry : Furry Iris -- Furry applied to Iris returns proof
| sargentFurry : Furry Sargent

example : Friendly Iris ∧ Furry Iris :=
And.intro Friendly.irisFriendly Furry.irisFurry

-- predicate is a function that takes some object and returns a Prop
def Suitable (d : Dog) : Prop := -- d is in global scope
Friendly d ∧ Furry d

def Suitable' : Dog → Prop :=
fun d => Friendly d ∧ Furry d -- d is in the scope of the function

example : Suitable Iris :=
And.intro Friendly.irisFriendly Furry.irisFurry

#check Friendly

-- to prove ∀, we need a function

example : ∀ d : Dog, Friendly d := -- Friendly d is a Prop
fun d => -- assume we get some dog
  match d with
  | Dog.Iris => Friendly.irisFriendly -- the proof is a value of Friendly d
  | Dog.Fido => Friendly.fidoFriendly
  | Dog.Sargent => sorry

example : ¬(∀ d : Dog, Friendly d) :=
fun allDogsFriendly => -- assume we have a function allDogsFriendly
let sf := allDogsFriendly Dog.Sargent -- apply function to Sargent to get proof of Friendly Sargent
nomatch sf -- but there is no proof of Friendly Sargent

-- to prove ∃, we need a witness and a proof

example : ∃ (d : Dog), Friendly d :=
  ⟨Dog.Iris, Friendly.irisFriendly⟩ -- make witness/proof pair using angled brackets

example : ∃ (d : Dog), Friendly d := -- basically the same as above, but using
Exists.intro Dog.Iris Friendly.irisFriendly -- intro rule for Exists
-- this is a dependent pair
-- type of proof (Friendly Iris) depends on witness (Iris)



-- 10/7
-- review: predicate is a function that takes some object and returns a Prop

def simpf : Prop :=
  (∃ d, Suitable d) → (∃ d, Friendly d)

example : simpf :=
fun h => -- assume we have proof of (∃ d, Suitable d)
  let ⟨d, sd⟩ := h -- extract witness and proof from existential
  ⟨d, _⟩ -- construct proof of ∃ d, Friendly d
-- is this even possible


-- 10/12

-- normal vs strong induction:
-- normal induction: to prove ∀ n, P n, we assume P n and prove P (n+1)
-- we only have direct previous case
-- strong induction: to prove ∀ n, P n, we assume ∀ m < n, P m and prove P n
-- we have all previous cases

#check Empty.rec
-- we can use Empty.rec to prove any proposition from an empty type
-- every type has induction principle
#check PUnit.rec
#check Bool.rec

-- how do we know we can recurse over the nat numbers:
#check Nat.rec
-- given base case and step case
-- we can always prove any proposition about natural numbers
-- using motive function to get answer

-- try to understand exists elim ig


-- 10/14

-- function to sum up all natural numbers from 0 to n
def sumUp: Nat → Nat
| 0 => 0
| n + 1 => (n + 1) + sumUp n
-- can also write n + 1 as Nat.succ n, but n + 1 is more readable duh
-- n => n + sumUp (n-1) does not work, it doesn't know if the function is terminating

-- factorial function
def fac : Nat → Nat
| 0 => 1
| n + 1 => (n + 1) * fac n

#eval fac 3

#check Nat.rec
-- this is the recursor

namespace Arith

inductive ArithExpr where
| lit (n : Nat) : ArithExpr
| plus (a b : ArithExpr) : ArithExpr

open ArithExpr

-- these are expressions
def a1 : ArithExpr := lit 1
def a7 : ArithExpr := lit 7
def a1plus7 : ArithExpr := plus a1 a7

def arithEval : ArithExpr → Nat
| lit n => n
| plus a b => arithEval a + arithEval b

#eval arithEval a1plus7

-- another way
def p1 : ArithExpr := plus (lit 1) (lit 7)
#eval arithEval p1

end Arith
