# Side notes from in class 10/26/26
```lean
inductive MyList (α : Type) : Type where
| nil
| cons (h : α) (t : MyList α)


def head {α : Type} : MyList α → Option α
| MyList.nil => none
| MyList.cons h t => some h

def head' {α : Type} : List α → Option α
| [] => none
| h::t => some h

def myfold {α : Type} (f : α → α → α) (id : α) : List α → α
| [] => id
| h::t => f h (myfold f id t)

#eval myfold Nat.add 0 []
#eval myfold Nat.add 0 [1]
#eval myfold Nat.add 0 [5,4,3,2,1]

#eval myfold Nat.mul 1 []
#eval myfold Nat.mul 1 [1]
#eval myfold Nat.mul 1 [5,4,3,2,1]


def myfold2
  {α : Type}
  (f : α → α → α)
  (f_assoc: ∀ (a b c : α), f (f a b) c = f a (f b c))
  (id : α)
  (fid : ∀ a, f id a = a ∧ f a id = a)
  : List α → α
| [] => id
| h::t => f h (myfold f id t)

def myMap {α β: Type} (f : α → β)  :  List α → List β
| [] => []
| h::t => (f h)::(myMap f t)

#eval myMap (fun n => n*n) [1,2,3,4,5]
```


<div class="issue-box">📝 <a href="https://github.com/kevinsullivan/Lean4CS1/issues/new">Report an issue</a> with this section</div>

