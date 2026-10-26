-- 10/26

inductive myOption (α : Type) where
| none : myOption α
| some (a : α) : myOption α

def dec : Nat → myOption Nat
| 0 => myOption.none
| (n' + 1) => myOption.some n'



inductive myList (α : Type) where
| nil : myList α
| cons (a : α) (l : myList α) : myList α -- cons means "constructor"

def head : myList α → myOption α
| myList.nil => myOption.none
| myList.cons h t => myOption.some h

def myFold
{α : Type}
(f : α → α → α)
(id : α) : List α → α
| [] => id -- [] is another way to say List.nil
| h::t => f h (myFold f id t) -- h::t is another way to say List.cons h t

#eval myFold Nat.add 0 []
#eval myFold Nat.add 0 [1, 2, 3]

def myFold'
{α : Type}
(f : α → α → α)
(f_assoc : ∀ a b c : α, f (f a b) c = f a (f b c)) -- now with proof of associativity
(id : α)
(f_id : ∀ a : α, f a id = a ∧ f id a = a) -- and proof of identity
: List α → α
| [] => id -- [] is another way to say List.nil
| h::t => f h (myFold' f f_assoc id f_id t) -- h::t is another way to say List.cons h t

def myMap {α β : Type} (f : α → β) : List α → List β
| [] => []
| h::t => f h :: myMap f t
