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
