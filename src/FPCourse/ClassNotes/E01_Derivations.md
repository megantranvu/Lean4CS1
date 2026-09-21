# Inference Rules and Derivations
## Introduction Rules
The term introduction rule refers to the means for
constructing, or introducing into the discourse, a
value of a given type, or a proof of a proposition.
Here are examples of construction/introduction
rules in very simple programming examples.
The introduction rules for Nat, as for any inductive
type, are simply given by its constructors.

``` inductive Nat : Type where
| zero            : Nat
| succ (n : Nat)  : Nat
```
```lean
-- The informal derivations are in th comments

def n : Nat := Nat.zero     -- Nat.intro_zero
def b : Bool := Bool.true   -- Bool.intro_true

def nb : Nat × Bool :=      -- × means Prod Nat Bool
  Prod.mk n b               -- Prod.intro

def nb' : Nat × Bool :=      -- × means Prod Nat Bool
  (                          -- Prod.mk Prod intro
    Nat.zero,                -- Nat.intro_zero
    Bool.false               -- Bool intro false
  )
```

## Elimination Rules
Every single type has its own elimination rules,
but they all serve the same purpose: to enable one
to define total functions from values of any type.
The elimination rules for a product type are just
the two projection functions, for pulling the first
and second values out of a given ordered pair value
of such a type.
```lean
-- Given a Nat-Bool pair, return the Nat component
def NB2Nat : (Nat × Bool) → Nat :=
  fun (p : Nat × Bool)  =>   -- → introduction
   Prod.fst p
```

To understand why this is true one must understand the
product type, *Prod*, itself. Remember you can use check
then right click and Go To Definition to see definitions
in Lean.

```lean
structure Prod (α : Type u) (β : Type v) where
  mk ::  (fst : α) (snd : β)
```
*Prod* has × as infix notation. Its single introduction
rule is  *Prod.mk* with notation *⟨_, _⟩*. Its two elimination
rules are projection of the first and second elements of any
pair by the functions *Prod.fst* and *Prod.snd* applied to it.
## Prod (×) is commutative.

This informal statement is intended to assert that if
you have *any* pair of types, call them α and β, there
is a total function, call it *swap*, that converts *any*
ordered pair, *p = (a, b)* of type *α × β* into a pair,
*(b, a)* of type *(β × α)*.
Moreover, there is an essential correctness condition
for any implementation of such a function: namely that
for any (a : α), (b : β), *swap (swap (a, b)) = (a, b)*.
In other words, `swap` applied twice is the *identity*
function for product

To gain deeper intuition it certainly helps to start
with simple concrete examples. So let's assume for now
that *α = Nat* and *β = Bool* and we'll just hardwire
these choices in our first examples.

### Special Case
To begin, let's prove, by simply programming, that
there is way, from *any* pair *(n, b) : Nat × Bool*
to derive a pair, *(b, n)* of type *Bool × Nat*. A
derivation of this form is just a *total function* of
type *(Nat × Bool) → (Bool × Nat)*.
```lean
-- specification
def swap_nat_bool : (Nat × Bool) → (Bool × Nat)
-- implementation
:= fun nb =>               -- → introduction
    let n := nb.1         -- × elimination left/1
    let b := nb.2         -- × elimination right/2
    (b, n)
```

Here's a more concise way to write it. To the left
of the `=>` we destructure the argument (just as in
javascript and other such languages). As usual this
operation binds names to subparts of the argument. On
the right, we assemble them (intro) in the result.
```lean
-- Specification
def swap_nat_bool' : (Nat × Bool) → (Bool × Nat)
:= fun (n, b) => (b, n)

#eval swap_nat_bool (3, true)
```

### Generalized Definition of Swap

The notion of swapping the elements of any ordered
pair is entirely sensible *in general*. It applies
not only to Nat-Bool pairs but to pairs of values of
any type.

We can express this in English by saying, if *α* and
*β* are any types, with *(a, b)*, any pair of values
of the product type, *α × β*, then there is a way from
that value to derive the pair *(b, a) :(β × α).* Let's
call it *swap*.

What we're going to show then, is that if *α* and *β*
are any types, then from any value of type *α × β* one
can derive a value of type *β × α*. In logical notation
we could write this: *∀ {α β : Type}, α × β → β × α*.
Let's get to that in a few steps.
### A Verbose Definition
```lean
def swap'''''' :
  ∀                 -- forall ..., for any ..., for every ...
    (α : Type u)    -- for any type α
    (β : Type v),   -- for any type β
    α × β → β × α   -- from any α-β pair, derive a β-α
-- Implementation
:= fun _ _ (a, b) => (b, a)
```

### Implicit Arguments
```lean
def swap''''' :
  ∀                 -- forall ..., for any ..., for every ...
    {α : Type u}    -- for any type α
    {β : Type v},   -- for any type β
    α × β → β × α   -- from any α-β pair, derive a β-α
-- Now we omit explicit α and β arguments; they're inferred
:= fun (a, b) => (b, a)

#eval swap'''''' Nat Bool (0, false)
#eval swap''''' (0, false)
```

What we just saw is the use of a logical  *∀* expression
used to express the type of a function. The *∀* introduces
named formal arguments. The comma separates them from the
return type, here *α × β → β × α*. Finally, after the *:=*
is the implementation, or proof, of the function type which
we can also read as a logical proposition! A proof of a *∀*
proposition is always just a function. Assuming you're given
*any* values of the argument types, a proof must show you
can derive *some* value/proof of the return type.
### Arguments of a Type Flock Together

Code is clearer when arguments of the same type are declared
together.
```lean
def swap'''' {α β : Type u} : α × β → β × α := fun (a, b) => (b, a)
```

### Arguments Bound Early

Arguments can be bound to names early by declarting then
to the left of the colon. Such arguments are no longer
subject to pattern matching using *match*.
```lean
-- pattern matching on *α × β* argument
def swap''' {α β : Type u} : α × β → β × α
| (a, b) => (b, a)

-- early binding of *α × β* argument
def swap'' {α β : Type u} (p: α × β) : β × α :=
match p with | (a, b) => (b, a)

-- early binding of *α × β* argument
def swap' {α β : Type u} (p: α × β) : β × α := (p.2, p.1)
```

### Type Inference
Finally, Lean can infer the function type from its implementation.
We can shorten the function definition by eliding its definition
accordingly.
```lean
def swap {α β : Type u} (p: α × β) := (p.2, p.1)
```

### Function / ∀ Elimination
The elimination rule for any function type, of proof of a
*∀* proposition, is just function application. You introdue
a function by assuming arguments and deriving a result. You
use a function by *apply*ing
it.
```lean
#eval swap (0, false)
#eval swap ("No", "Way")
```

## A Property of *swap* Formalized and Proved

Finally, a correctness condition: swap is involutive!
What that means is that applying it to any pair then
applying it to the result returns the original input.
```lean
theorem swap_involutive
  {α β : Type u}
  (x : α)
  (y : β) :
  Eq
    (swap (swap (x, y)))
    (x, y) :=
Eq.refl (x, y)

-- The Lean term, *(swap_comm 0 true)*, typechecks
-- as a proof of swap (swap (0, true))) = (0, true)
#check (swap_involutive 0 true)
```

The generalized function is the proof of the ∀. As
the proof is itself a function, you can *apply* it
to specific arguments as usual.

We thus see *∀ introduction*: assume an abitrary value,
derive the result for it. That is, define a *function*.
The the *∀ elimination* rule -- to use a function you
*apply* it to *specific* particulars (arguments). The
result is then produced for that special case. You will
here *∀ introduction* called *universal generalization*,
and *∀ elimination, *universal specialization*.

THe preceding example, for instance, shows universal
specialization. From a general theorem,
swap_comm, to the special case argments, 0 and true, in
this expression, *(swap_comm 0 true)*, to obtain a proof
that swap applied twice to the specific pair, (0, true),
works as expected and returns that very same value.
## The Polymorphic Equality Type

In Lean, if *a* and *b* are of the same type, then
*Eq a b* is the *proposition* that asserts *a = b*.
Indeed *a = b* in Lean is just notation for *Eq a b*.
```lean
#check (@Eq)
#check (Eq 1 1)
#check (Eq 1 2)
```

### The Type

inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a
### A proof

example : Eq 1 1 := Eq.refl 1
```lean
-- The *Eq.refl* constructor *cannot* prove 1 = 2
-- example : Eq 1 2 := _
```

You can think of *Eq a b* not only as a proposition
(that *a* and *b* are equal) but also as the type of
proofs of equality of *a* and *b*. Then the question
is, is that type *inhabited*? Is there a proof of it
or not?

The answer is given by the single constructor of the
Eq type. It's *Eq.refl*. It takes one argument and it
typechecks as a proof that that argument is equal to
itself. It's general, taking any single value of any
type. Any value, *a* of *any* type is provable equal
to itself, and there are no other proofs of equality.
This is the introduction rule for proofs of equality!
We'll address the elimination rule in due course.
## From Computation to Logic: And (∧) is Commutative

And now for some actual mathematical logic. Let's prove
that *logical And is commutative.* Let's start by proving
a particular conjuction, *And (7 > 0) (7 ≤ 10)*, usually
written with infix notation as *(7 > 0) ∧ (7 ≤ 10).* We'll
then show if this is true so is *(7 ≤ 10) ∧ (7 > 0).*

The Curry-Howard Correspondence observes that the Product
*type builder* is the direct *computational* analog of the
predicate logic *And* connective, or *proposition builder*.
Given two propositions (represented as types), *P* and *Q*,
it yields a new proposition (type), *And P Q*, or *P ∧ Q*.

In Lean it's expressed as an inductive type with two smaller
types in Prop as its arguments, with a single constructor
that expresses its logical meaning: if you have *proofs* of
the two individual argument types, respectively,then you can
*pair them up*, using the *And.intro* constructor, to have
(a term that typechecks as) a proof of *P ∧ Q*. Here's the
actual *And* type builder definition.

```lean
structure And (a b : Prop) : Prop where
  intro :: (left : a) (right : b)
```

You introduce a proof of *P ∧ Q* by applying *And.intro* to
proofs *(p : P)* and *(q : Q)*. Given a proof *(h : P ∧ Q)*
you use (eliminate) it by field projection: *(h.left : P)*,
*(h.right : Q)*.
```lean
#check And
```

Here's a first proof. The type we're proving here is a
logical (in *Prop*), not a computational type, and Lean
prefers that you use *theorem* instead of *def*. Try it.
```lean
#check (7 > 0)
#check (7 ≤ 10)
#check (7 > 0) ∧ (7 ≤ 10)

example : (7 > 0) ∧ (7 ≤ 10) :=
  And.intro         -- introduction applied to two proofs
    (by decide)     -- decision procedure, proof of 7 > 0
    (by decide)     -- decision procedure, proof of 7 ≤ 10
```

For this special case we can prove that *And commutes*.
Given a proof of (7 > 0) ∧ (7 ≤ 10) one can then derive
a proof (7 ≤ 10) ∧ (7 > 0). A proof of the former is just
a kind of *pair* of proofs, and the latter, a *pair* in
the swapped/opposite order.
```lean
theorem impExample : (7 > 0) ∧ (7 ≤ 10) → (7 ≤ 10) ∧ (7 > 0) :=
  fun conj =>       -- → introduction
    (
      And.intro     -- And introduction analogous to × introduction
        conj.2      -- And.elim_2/right
        conj.1      -- And.elim_1/left
    )

-- Now we can generalize to arbitrary propositions, *P* and *Q*
theorem impEx2'' {P Q : Prop} : P ∧ Q → Q ∧ P :=
  fun pq =>         -- → introduction
    And.intro       -- And introduction
      pq.right      -- And.elim_right
      pq.left       -- And.elim_left

-- As Prod.mk has notation (_,_), And.intro uses ⟨_, _⟩
theorem impEx2' {P Q : Prop} : P ∧ Q → Q ∧ P :=
  fun ⟨ p, q ⟩  =>  ⟨ q, p ⟩

-- Just another way to write it (more notation), preferred.
-- Using case analysis and destructuring notation (drops :=)
theorem impEx2 {P Q : Prop} : P ∧ Q → Q ∧ P
  | ⟨ p, q ⟩  =>  ⟨ q, p ⟩

-- Yay, we have a simple and general proof ∧ commutes
-- Now we can apply our general theorem to any special case
-- It's just going to be function application; let's set it up

-- define abbreviations for the following propositions
abbrev sGtZ : Prop := 7 > 0
abbrev sLe10 : Prop := 7 ≤ 10

-- invoke decision procedures to obtain proofs of each
theorem sGtZ_pf : sGtZ := (by decide)
theorem sLe10_pf : sLe10 := (by decide)

-- Assemble proof of conjunction using And.intro
theorem a_conj_pf : sGtZ ∧ sLe10 := ⟨ sGtZ_pf, sLe10_pf ⟩

-- Unclear? Go look at the definition of And!
```

structure And (a b : Prop) : Prop where
  intro :: (left : a) (right : b)
```lean
-- Look at the type of And (infix notation is ∧)
#check And

-- The introduction rule applied
#check And.intro sGtZ_pf sLe10_pf
-- ⟨sGtZ_pf, sLe10_pf⟩ : sGtZ ∧ sLe10
-- read the colon as *is a proof of*

-- Elimination rules examples (structure field names as elim rules)
#check And.left a_conj_pf     -- Like Prod.fst
#check a_conj_pf.left         -- Dot notation
#check And.right a_conj_pf    -- Like Prod.fst
#check a_conj_pf.right        -- Dot notation
```

### The Curry Howard Correspondence

The term, Curry-Howard Correspondence, names the
recognition that the *inference rules* of deductive
*reasoning* in predicate logic (here higher-order and
dependently typed) have mirror images as dependently
typed pure functional *programms*.

You've just seen a good example. `Prod` and `And` are
Curry-Howard twins. So are the commutativity of `And`
and the swappability of `Prod`. Your preparation for
next class includes illustrating the same duality for
the flippability of `Sum` and the commutative of `Or`.
## The Sum-Or Correspondence

Recall that `Sum α β` or (`α ⊕ β`) is the type of term
that holds either a value (a : α) or a value (b : β).
Any term of this type is of exlusively one of these forms.
To have a term of this type proves that *at least one* of
the summand types is inhabited. Think about that to be
sure you see it clearly. A value of a product type, by
contrast, is proof that *both* multiplicand types are.
### The Sum Type

Here's the computational Sum type builder.

```lean
inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α) : Sum α β
  | inr (val : β) : Sum α β
```
```lean
-- all inhabited, with mk as default constructor
structure Rice
structure Potato
structure Fish
structure Chicken

def choiceChicken : Chicken ⊕ Fish := Sum.inl Chicken.mk
def choiceFish : Chicken ⊕ Fish := Sum.inr Fish.mk

-- Elimination is by case analysis

def meatToString : Chicken ⊕ Fish → String
| Sum.inl _ => "Chicken"
| Sum.inr _ => "Fish"

#eval meatToString choiceChicken
#eval meatToString choiceFish
```

## EXERCISES:
```lean
-- #1: PROVE: Chicken ⊕ Fish → Fish ⊕ Chicken
```

#2: PROVE: that someone who ordered "Fish, and either
Rice or Potato" should be satisfied to be served
"Rice or Potato, and Fish. Clearly, it's true: you
just have to turn the plate a little! To prove it
it would do to show there's a function that applied
to a whole *meal, "Fish, and either Rice or Potato"
derives and returns a meal, "either Rice or Potato,
and Fish."
```lean
example : Fish × (Rice ⊕ Potato) → (Rice ⊕ Potato) × Fish
| _ => sorry    -- replace this line
```

That's just commutativity of × again. We proved it by
running the whole proof strategy again for this special
case of the general principle; but we don't have to, as
we have a general "theorem" (swap function) for that.

The reason we prefer to prove generalized theorems or
write general-purpose functions is because we can then
*apply* them where needed without having to reproduce
the whole derivation from scratch. It's makes math work!
```lean
example :
  Fish × (Rice ⊕ Potato) → (Rice ⊕ Potato) × Fish
  | meal => swap meal
```

#3: Prove. Here's an example suggesting that × distributes
over ⊕ just as numerical multiplication distributes over
addition: x * (y + z) = x * y + x * z. Show that the
same principle holds for × and ⊕, first in a specific
example, then in general.
```lean
example :
  Fish × (Rice ⊕ Potato) → Fish × Rice ⊕ Fish × Potato
  | (f, rop) =>
      sorry
  -- you've got fish; now does rop hold rice or potato?

-- #4 Prove the other direction too.
example :
  Fish × Rice ⊕ Fish × Potato → Fish × (Rice ⊕ Potato)
  | _ => sorry    -- replace line with your code
```

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
```lean
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
```


<div class="issue-box">📝 <a href="https://github.com/kevinsullivan/Lean4CS1/issues/new">Report an issue</a> with this section</div>

