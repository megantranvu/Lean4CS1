# Side notes from in class 10/26/26
```lean
-- remember parameterized List type
inductive MyList (α : Type) : Type where
| nil
| cons (h : α) (t : MyList α)

-- head, a partial function, using Option α
def head {α : Type} : MyList α → Option α
| MyList.nil => none
| MyList.cons h t => some h

-- using list notation
def head' {α : Type} : List α → Option α
| [] => none
| h::t => some h

-- it can work
def myfold {α : Type} (f : α → α → α) (id : α) : List α → α
| [] => id
| h::t => f h (myfold f id t)

-- see ... un, oops
#eval myfold Nat.add 0 []
#eval myfold Nat.add 0 [1]
#eval myfold Nat.add 0 [5,4,3,2,1]

-- now right, but type's too wide
#eval myfold Nat.mul 1 []
#eval myfold Nat.mul 1 [7]
#eval myfold Nat.mul 1 [5,4,3,2,1]

-- formalize laws operation correctness requires
-- require proofs of them with the other arguments
def myfold2
  {α : Type}
  (f : α → α → α)
  (f_assoc: ∀ (a b c : α), f (f a b) c = f a (f b c))
  (id : α)
  (fid : ∀ a, f id a = a ∧ f a id = a)
  : List α → α
| [] => id
| h::t => f h (myfold f id t)

-- an easily broken higher order *map* function
def myMap {α β: Type} (f : α → β)  :  List α → List β
| [] => []
| h::t => (f h)::(myMap f t)

-- satisfaction of what laws does *map* operation require
#eval myMap (fun n => n*n) [1,2,3,4,5]

-- constraints include overall output having same shape as
-- input, and every element in the input list appears as
-- transformd by *f* in the corresponding output positions
-- Now we can just cut to the chase.

-- HERE (-> moved into E12_GeneralizedFold.lean, toward the end)
```


<div class="issue-box">📝 <a href="https://github.com/kevinsullivan/Lean4CS1/issues/new">Report an issue</a> with this section</div>

