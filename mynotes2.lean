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

#eval myMap (fun n => n*n) [1, 2, 3]



-- 10/28
-- 2nd highest bid, auction theory

-- Option, List, and Tree are containers, they are type to type builders
-- ex: when List gets type Nat, it makes type List Nat
#check List

-- look at how size fun works in E12 notes
-- and read the rest of the chapter



-- 11/2

-- moving on to E13

-- a Group is a monoid with an inverse function
-- groups are symmetry preserving transformations?
-- simple group: can't be broken down into smaller groups
-- torsor: originless plane where points live, can move between points with vectors
-- torsor over a group?
