/- @@@
# Existential Quantification
@@@ -/

/- @@@
The previous chapter introduced *predicates*: functions from
values to propositions, `P : α → Prop`. A predicate is a family
of propositions, one for each value of α, and it becomes a
definite claim only when applied to a particular value.

Predicates are what the quantifiers quantify over. `∀ x : α, P x`
says that every value of α satisfies P. `∃ x : α, P x` says that
at least one does. This chapter is about the second of these.

Like every connective we have studied, `∃` comes with an
*introduction* rule, telling us how to build a proof, and an
*elimination* rule, telling us how to use one. We take them in
that order, first on a small concrete example, then in general.
@@@ -/

/- @@@
## Introduction: Exhibiting a Witness

An existential proof is a pair: a value, and evidence about that
value. We build up to that rule on a concrete example, state it,
and then exercise it in other settings.

To be concrete we now use the expressiveness of higher-order
predicate logic in Lean to model DogWorld, a world with three
dogs (Iris, Fido, and Sargent), and the properties of these dogs
being Friendly, and being Furry.

 is a type with three values and two predicates applicable
to them. Read each constructor as a piece of evidence sufficient to
prove friendliness. `Friendly` outright stipulates that Isis, a Dog,
is Friendly, precisely because `Frienly d` has just two proofs: one
where `d` is `Iris` and one where `d` is `Fido`. No constructor of
the type as defined can possibly produce the term `Friendly Sargent`.
The typechecker will therefore reject it as a value of the `dependent
type, `Friendly d`. As `Friendly d` is in `Prop`, we must read it as
a proposition, that *the Dog, d (to be given as an actual parameter),
is friendly)*, and that fact that there is no way to construct that
term, means that there *can be no proof* of `Friendly Sargent`. That
in turn is how as a designer of worlds you declare that proposition
to be false by making sure no proof of it can be constructed.

### Dogs
@@@ -/


-- Three Dogs
inductive Dog : Type where
| Iris
| Fido
| Sargent

open Dog

/- @@@
### Two Properties of Dogs and their Proofs
@@@ -/

inductive Friendly : Dog → Prop where
| irisIs : Friendly Iris
| fidoIs : Friendly Fido

-- The second property
inductive Furry : Dog → Prop where
| irisIs : Furry Iris
| sargentIs : Furry Sargent

open Friendly Furry


/- @@@
### Compound Properties are Properties

Look at the available proofs. One proves Iris is
friendly. Another proves Iris is furry. Iris thus
has the conjoined, or *compound*, property of being
both friendly and furry. Let's assert and prove it.
@@@ -/

example : Friendly Iris ∧ Furry Iris :=
  -- Exists.intro Friendly.irisIs Furry.irisFurry
  ⟨ Friendly.irisIs, irisIs ⟩


/- @@@
We now have the tools to express this conjunction
more abstractly as a single new *compound* property,
we'll call `Suitable`. We will say that a `Dog`, `d`,
is suitable if it is both friendly and furry. A quick
check confirms that in our world, `Iris` is `Suitable`.
Indeed, that's what we just proved.
@@@ -/

/- @@@
Here are two ways to write (or formalize) this idea
in Lean. The shape of the type declaration in the first
example, `Dog → Prop`, makes it visibly clear that we
are defining a predicate on, a property of Dogs. The
cost is that the formal parameter `d` has to be bound
in the body of th function. Declaring `d` to the left
of the colon makes it global to the function definition.
The second version is concise and I usually prefer it.
@@@ -/

def Suitable' : Dog → Prop :=
  fun d => (Friendly d ∧ Furry d)


def Suitable (d : Dog) : Prop :=
  (Friendly d ∧ Furry d)

/- @@@
Now we'll assert and prove that Iris is
suitable. Here's a mathematical English
proof.

Prove: Iris is Suitable
Proof. By the definition of Suitable,
all that remains to prove is that Iris
is Friendlly *and* Iris is Furry. This
is proved by `And.intro` applied to the
proofs we already have of those claims.

Here it is in Lean. We also take a first
opportunity to introduce *tactic mode* in
Lean. Instead of writing directly in the
Lean functional programming language you
write tactic scripts: sequences of calls
to what you should think of as subroutines
from an ever growing library that try
to automate certain proof construction
steps, from the extremely simple (such as
`Apply And.intro p q`, to the complex,
e.g., to invoke a solver to reduce a
system of linear inequalitys or other
complex constraints.

Tactic mode is entered using `by`.
@@@ -/
example : Suitable Iris :=
  by
    unfold Suitable
    apply And.intro
    exact Friendly.irisIs
    exact Furry.irisIs

/- @@@
## Exists vs. Forall

What makes *function terms* work as proofs of universal
(`∀`) propositions is that the functions that they define
and compute are necessarily *total. A proof of `∀ x, P x`
show that for *any* `x` and can obtain a proof of `P x`.
How? By *applying* the function that *is* the proof of
`∀ x, P x`.

The introduction rule for proving `∀ x, P x` is to
assume an arbitrary `x` and show that from it one can
derive a proof that `x` has property `P`. Heck, one can
even write tghe type, `∀ x, P x` as `(x : X) → P x`, the
type of function from any `x` (totality! to a proof `x`
has property `P`.
@@@ -/


-- Every Dog that's not Sargent is Friendly
theorem anyDogNotSargentIsFriendly : ∀ d, d ≠ Sargent → Friendly d :=
  fun d h =>        -- assume arbitrary Dog and a proof d ≠ Sargent
    match d with    -- show that that Dog, d, is friendly
    | Iris => irisIs          -- Iris ≠ Sargent ✓
    | Fido => fidoIs          -- Fido ≠ Sargent ✓
    | Sargent => nomatch h    -- Sargent ≠ Sargent impossible case

/- @@@
The *introduction* rule for ∀ here says, assume you're
given *any* Dog, d, along with a proof that d ≠ Sargent
(the formal parameters of =a function) and show that from
those assumptions, from those data and proof values, one
can then derive a proof that d is Friendly. Lean accepts
the function term, proving the universal generalization.

The elimination rule, to use such a proof now that we have
one, says to *apply* the proof of the *generalization* to
any *particular* to get a proof for that special case. In
the language of predicate logic, this is also called the
rule of *universal specialization*. The intuitive reasoning
is that if *every* dog that's not Sargent is friendly, then
we can use that proof to show that any specific dog, let's
pick Iris, that is provably not Sargent, is friendly.

To prove Iris, for example, is friendly, from the *universal
generalization*, `∀ x, P x`, just *apply* the proof of it (a
total function) to the particular `x` at issue, here `Iris,`
and evaluate/reduce that application to have Lean compute and
for you to obtain a proof that `Iris` in particular is friendly.
This is the inference rule called *universal specialization*
in certain circles and just ∀ elimination in others. It tells
you exactly how you can use such a proof. Apply it!

Where an understanding of these ideas is especially useful is
in the creating work that you have to do when you have done
all the mechanical work to load up your proof context, with
some demanding goal remaining to be proved. Then you have to
have to be able to see ways to put multiple elements in your
context together, using just the applicable rules, to get a
proof of whatever remains to be proved in that moment. "Oh,
I can apply this proof, `h : ∀ (x : X), P x`, to this value,
(a : X), by writing the function application `h a` to get a
proof of `P a`, encoding the propostion, `a` has property `P`.

The result will prove that Iris is not Sargent.
That Iris is not Sargent is proved by *negation*. Assume
Iris = Sargent, then have Lean determine that's impossible.
There is no equality (`Eq`) constructor that can possibly
account for a proof of equality, (`h : Iris = Sargent`).
Such a case is impossible and so can simply be dismissed.
@@@ -/

-- This check shows that the result proves `Friendly Iris`
#check anyDogNotSargentIsFriendly Iris (fun i => nomatch i)

/- @@@
`#guard_msgs` checks the expected error, so this intentionally
unfinished attempt does not prevent the file from compiling.
@@@ -/

/--
error: don't know how to synthesize placeholder
context:
d : Dog
⊢ Friendly Sargent
-/
#guard_msgs in
example : ∀ (d : Dog), Friendly d :=
  fun d =>
    match d with
    | Iris => Friendly.irisIs
    | Fido => Friendly.fidoIs
    | Sargent => _

/- @@@
In fact the universal claim is refutable. Assume it, apply it to
Sargent, and we obtain a purported proof of `Friendly Sargent`.
No constructor of `Friendly` could have produced such a proof, so
`nomatch` discharges the case and we have our contradiction.
@@@ -/

example : ¬(∀ (d : Dog), Friendly d) :=
  fun allDogsFriendly =>
    let sf := allDogsFriendly Sargent
    nomatch sf

/- @@@
The existential claim, by contrast, is easy. Is *some* dog
friendly? Yes, and to show it we name one and supply its evidence.
To prove that something exists, produce it, then show that it
works.
@@@ -/

example : ∃ (d : Dog), Friendly d :=
  -- Exists.intro Iris irisIs
  ⟨ Iris, irisIs ⟩

def simpf : Prop :=
  (∃ d, Suitable d) →
  (∃ d, Friendly d)

-- example : simpf :=
--   fun pfs =>
--     _

/- @@@
### The Rule Behind That Proof

That pair of things, a value and a proof about that value, is all
an existential proof ever is. So where does `Exists.intro` come
from? It is just the constructor of an inductive type, like every
introduction rule we have used. Here is Lean's definition of
`Exists`, copied under a new name so that it compiles here without
clashing with the library's.
@@@ -/

inductive MyExists {α : Sort u} (p : α → Prop) : Prop where
| intro (w : α) (h : p w) : MyExists p

#check Exists

/- @@@
One type, one constructor, so there is exactly one way to build a
proof. Read the pieces. `MyExists` takes the *predicate* p as a
parameter, not a value, which is what makes it a claim about some
value of α rather than about a particular one. Its constructor
takes two arguments: a *witness* `w : α`, and `h : p w`, evidence
that p holds of that very w. Note that the type of the second
argument depends on the first. That is the introduction rule, and
it is the entire content of an existential proof.

The library's `Exists` is this same type, and its `intro` has
exactly the signature just described.
@@@ -/

#check @Exists
#check @Exists.intro

/- @@@
Now match our dog proof against the rule. The predicate is
`Friendly`, so α is `Dog`. We supplied `Iris` for w and
`Friendly.irisIs` for h, and Lean checked that the latter
really is a proof of `Friendly Iris`, the predicate applied to the
witness we chose. Had we offered `Sargent` as the witness, the
second argument would have had to be a proof of `Friendly Sargent`,
and we have none to give.

The evidence can be compound, since h is only ever required to
prove `p w`, whatever proposition that turns out to be. To prove
that some dog is suitable, exhibit Iris together with a proof of
the conjunction.
@@@ -/

example : ∃ (d : Dog), Suitable d :=
  Exists.intro Iris (And.intro Friendly.irisIs irisIs)

/- @@@
### The Same Rule, More Examples

Nothing about the rule is special to dogs. Here it is on `Nat`,
where the witness is a number and the evidence is a proof about
that number.
@@@ -/

example : ∃ n : Nat, n = 3 :=
  Exists.intro 3 rfl

example : ∃ n : Nat, n + 1 = 4 := Exists.intro 3 rfl

/- @@@
The angle-bracket notation `⟨w, pf⟩` is Lean's *anonymous
constructor*: it means "apply the sole constructor of the expected
type to these arguments." For an existential it means exactly
`Exists.intro w pf`. We used it for `And.intro` above, and it
works here for the same reason: one constructor, so there is
nothing to disambiguate.
@@@ -/

example : ∃ n : Nat, n + 1 = 4 := ⟨3, rfl⟩
example : ∃ n : Nat, n > 3 := ⟨4, Nat.le.refl⟩

/- @@@
Nested existentials are nested pairs, and the anonymous
constructor notation nests to match.
@@@ -/

example : ∃ a : Nat, ∃ b : Nat, a + b = 5 := ⟨2, 3, rfl⟩

/- @@@
### Which Witness? The Proposition Does Not Say

One last observation, and it is a crucial one. The *proposition*
`∃ n : Nat, n < 10` records only that a witness exists. Two proofs
can use different witnesses and still prove the very same
proposition, and nothing in the proposition tells us which one was
used.
@@@ -/

example : ∃ n : Nat, n < 10 := ⟨0, Nat.zero_lt_succ 9⟩
example : ∃ n : Nat, n < 10 := ⟨9, Nat.le.refl⟩

/- @@@
Hold on to that point. It is the reason the elimination rule, the
subject of the next section, comes with a restriction.
@@@ -/

/- @@@
## Elimination: Unpack the Witness

To *use* a proof of `∃ x : α, R x`, take it apart. Because there
is only one constructor, a proof must have been built as
`Exists.intro w pf`, so we may pattern match to recover a name
w for the witness and a proof pf of `R w`, then use them to build
whatever we are trying to prove.

Two constraints govern this unpacking. First, w is a *local*
name, bound only inside the branch of the match. Second, and as a
consequence, the goal being proved must be stated without
mentioning w: we are proving one fixed conclusion no matter which
value was hidden inside.

Here is the general rule, stated and proved by matching. Read the
second hypothesis as "whatever the witness turns out to be, it
lets us conclude S."
@@@ -/

example {α : Type} (R : α → Prop) (S : Prop) :
    (∃ x : α, R x) → (∀ x : α, R x → S) → S :=
  fun existsRx =>
    fun useWitness =>
      match existsRx with
      | Exists.intro w pf => useWitness w pf

/- @@@
The same rule is packaged in the standard library as
`Exists.elim`, so this pattern need not be rewritten each time.
@@@ -/

#check @Exists.elim

/- @@@
```lean
Exists.elim.{u}                 -- *IF* u is any universe level
  {α : Sort u}                  -- and if α is any type in universe u
  {p : α → Prop}                -- and if p is any property of α values
  {b : Prop}                    -- and if b is any desired conclusion

  -- the two explicit arguments to exists.elim
  (h₁ : ∃ x, p x)               -- and if there is at least one x with p
  (h₂ : ∀ (a : α), p a → b)   -- and if any a has property p, then b
  :                             -- *THEN*
  b
```                           -- b, by the rule of false elimination

The main source of confusion arises from bad parsing (precedence)

- (h₂ : ∀ (a : α), p a → b) as
- (h₂ : (∀ (a : α), p a) → b))    -- wrong, → precedence than ∀
- (h₂ : ∀ (a : α), (p a → b))     -- right, → grabs (p a) and b before ∀

So the correct reading of (h₂ : ∀ (a : α), p a → b) is "given any a, if
a has property p then b" rather than "if every a has property p, then b".

Now the logical reasoning should be clear. Focus on seeing how the last two
assumptions make the conclusion true. First, suppose there is at least one
x with propery p, Second, if a is *any* α value, then if a has property p,
then (you can have a proof of) b. Put the two together and you get b by the
logical inference rule of Exists elimination (Exists.elim in Lean).
@@@ -/

/- @@@
Anonymous constructor notation works in patterns, too, which makes
`fun ⟨w, pf⟩ => ...` the idiomatic way to eliminate an existential
in term mode. In the next example we weaken what we know about the
witness: we keep the same witness and upgrade its evidence.
@@@ -/

example
  {α : Type}
  (P Q : α → Prop)
  (imp : ∀ x : α, P x → Q x) :
  (∃ x : α, P x) →
  (∃ x : α, Q x) :=
  fun ⟨w, pw⟩ => ⟨w, imp w pw⟩

/- @@@
Patterns nest, so a conjunction inside an existential can be
unpacked in the same binder. Here we eliminate an existential and
then immediately introduce a new one, reusing the witness we were
handed.
@@@ -/

example {α : Type} (P Q : α → Prop) :
    (∃ x : α, P x ∧ Q x) →
    (∃ x : α, Q x ∧ P x) :=
  fun ⟨w, pw, qw⟩ => ⟨w, qw, pw⟩

/- @@@
Existentials and negation combine as expected. A witness that
*fails* a predicate refutes the claim that the predicate holds
universally: unpack the counterexample, apply the universal claim
to that witness, and hand the result to the negation. The
refutation of `∀ (d : Dog), Friendly d` above was this rule,
specialized to Sargent.
@@@ -/

example {α : Type} (P : α → Prop) :
    (∃ x : α, ¬P x) →
    ¬(∀ x : α, P x) :=
  fun ⟨w, notPw⟩ =>
    fun allP => notPw (allP w)

/- @@@
## A Witness Is Not Data

Finally, the boundary. The witness genuinely cannot escape the
match. `Exists` lives in `Prop`, so a proof of an existential may
be taken apart to build another *proof*, but not to compute a
*value*. The following is rejected by Lean, and the error is worth
reading: `recursor Exists.casesOn can only eliminate into Prop`.
We were asking proof-level evidence to yield data. It is left
commented out because its full error text includes metavariable
numbers that shift between Lean versions.
@@@ -/

/-
example : (∃ n : Nat, n > 3) → Nat :=
  fun ⟨w, _⟩ => w
-/

/- @@@
This is the same phenomenon we met with classical negation
elimination. `∃` is a logical claim of existence. When we want a
witness *as data*, usable in later computation, we need a value in
`Type`, such as a `Subtype` or a dependent pair `Σ`, rather than a
proof in `Prop`.
@@@ -/

/- @@@
## Nonconstructive Existence

Everything above introduced an existential by exhibiting a
witness. Classically, we can also prove existence *by
contradiction*, without constructing anything: assume that no
such x exists, derive False, and conclude that one does. This is
our earlier double-negation elimination with `∃ x, R x`
substituted for P. See `E05_ClassicalVsConstructive.lean` for an
introduction to `open Classical` and the `em` it provides.
@@@ -/

open Classical

example
  {α : Type}
  (R : α → Prop)
  :
  (¬(∃ x : α, R x) → False) →
  ∃ x : α, R x :=
fun notNotExists =>
  match em (∃ x : α, R x) with
  | Or.inl existsRx => existsRx
  | Or.inr notExists => False.elim (notNotExists notExists)

/- @@@
Read what this proof does and does not deliver. It establishes
the proposition `∃ x : α, R x`. It names no witness, and there is
nothing in it to run. The next section makes that cost concrete.
@@@ -/

/- @@@
### Example: Is There an Odd Perfect Number?

Before any Lean, here is the question.

Call a positive number *perfect* if it is the sum of its proper
divisors, meaning its divisors other than itself. 6 is perfect:
its proper divisors are 1, 2, and 3, and 1 + 2 + 3 = 6. So is 28,
since 1 + 2 + 4 + 7 + 14 = 28. Perfect numbers appear in Euclid's
*Elements*, so people have been studying them for a very long time.

Every perfect number anyone has ever found is even. Nobody has
produced an odd one, and nobody has proved that none exists. This
is not for lack of effort: it is known that an odd perfect number,
if there is one, must be greater than 10^2200, and must satisfy a
long list of further constraints. The question

Is there an odd perfect number? is one of the oldest unresolved
questions in mathematics.

Hold that question in mind. It is an existential claim, so this
chapter has given us two ways to try to settle it. We can exhibit
a witness, or we can go classical. Watch what each one delivers.
@@@ -/

/- @@@
First, the part that is ordinary programming. Summing the proper
divisors of a number is a computation. Every proper divisor of n
is smaller than n, so it suffices to scan the numbers below n.
Don't worry about the programming of this function for now.
@@@ -/

def sumProperDivisors (n : Nat) : Nat :=
  (List.range n).foldl
    (fun acc d => if d > 0 && n % d == 0 then acc + d else acc) 0


-- Translate this computable "Boolaen predicate"
def isPerfect (n : Nat) : Bool := n > 0 && sumProperDivisors n == n

/- @@@
These are total functions, and we can run them. Lean prints the
results below, and `#guard_msgs` checks that they are what we
claim they are.
@@@ -/

-- not perfect numbers
/-- info: 0 -/
#guard_msgs in
#eval sumProperDivisors 1

/-- info: 1 -/
#guard_msgs in
#eval sumProperDivisors 2

/-- info: 1 -/
#guard_msgs in
#eval sumProperDivisors 3

/-- info: 3 -/
#guard_msgs in
#eval sumProperDivisors 4

/-- info: 1 -/
#guard_msgs in
#eval sumProperDivisors 5

-- two perfect numbers
/-- info: 6 -/
#guard_msgs in
#eval sumProperDivisors 6

/-- info: 28 -/
#guard_msgs in
#eval sumProperDivisors 28

/- @@@
Searching a *bounded* range is also ordinary programming. Here
are all the perfect numbers below ten thousand. This is a real
mathematical result about a finite range, and the code that
produced it is the evidence: we can rerun it, and we can read it
to see what it checked. (Comment out the #guard line to run it).
@@@ -/

/-- info: [6, 28, 496, 8128] -/
#guard_msgs in
#eval (List.range 10000).filter isPerfect

/- @@@
Look at that output: 6, 28, 496, 8128. Every one of them is even.
That is the observation that makes the open question interesting,
and we just computed it ourselves.

Testing whether a *given* number is an odd perfect number is
equally ordinary. 28 is perfect but even, so it fails.
@@@ -/

def isOddPerfect (n : Nat) : Bool := n % 2 == 1 && isPerfect n

/-- info: false -/
#guard_msgs in
#eval isOddPerfect 28

/- @@@
So far nothing is in doubt. Each function above carries executable
content, and every answer we got came out of running it.

Now state the open question as a proposition. It is exactly an
existential: not a claim about any particular n, nor about any
finite range of them, but the claim that some n works. Assert:
there is an odd perfect number.
@@@ -/

def SomeOddPerfect : Prop := ∃ n, isOddPerfect n = true

/- @@@
To prove this the way the introduction rule asks, we would write
`⟨w, pf⟩` for some specific numeral w, together with a proof that
`isOddPerfect w = true`. But today nobody has a way to fill in w.
A witness would settle a question that has stood for centuries. We
do know that if one exists it has more than 2200 digits (base 10).

Now watch how cheap the classical route is. A single application
of excluded middle settles the disjunction, right now, with no
search and no witness whatsoever.
@@@ -/

theorem oddPerfectOrNot : SomeOddPerfect ∨ ¬SomeOddPerfect :=
  em SomeOddPerfect

/- @@@
That is a complete proof, and Lean checks it. Read carefully what
we have and what we do not have. We have a proof that the question
has an answer. We do not have the answer. No n comes out of
`oddPerfectOrNot`, and there is nothing in it to run. A question
that has resisted mathematicians for centuries was not settled
here; only the claim that it has *some* answer, which we got for
free from *em* (by applying the additional non-constructive axiom
of the excluded middle).

The gap turns into a compiler error the moment we try to *use* the
answer in a program. Recall the `open Classical` above, which
brings `Classical.propDecidable` into scope. That makes every
proposition count as `Decidable`, so the `if` below typechecks:
Lean accepts it as a well-formed program that branches on whether
an odd perfect number exists. Then code generation runs, and fails.
The error names exactly what is missing.
@@@ -/


-- The precise error if code is unguarded, as a doc string.
-- Comment out the guard to see the error.
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'propDecidable', which is 'noncomputable'
-/
#guard_msgs in
def oddPerfectAnswer : String :=
  if SomeOddPerfect then "one exists" else "none exists"

/- @@@
We are allowed to keep the definition if we mark it
`noncomputable`, because that marking is an honest declaration
that no code will be produced for it. The definition is then
accepted, and `#eval` still cannot run it.
@@@ -/

noncomputable def oddPerfectAnswer' : String :=
  if SomeOddPerfect then "one exists" else "none exists"

-- comment out docstring and @guard to see the error
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'oddPerfectAnswer'', which is 'noncomputable'
-/
#guard_msgs in
#eval oddPerfectAnswer'

/- @@@
Compare the two parts of this example. `isPerfect` and the
filter that finds all perfect numbers up to 10000 are computable.
`oddPerfectAnswer` on the other hand looks like a program but the
constructive reading of `∃` would demand a witness that we do not
have. Classical logic, with excluded middle (em), gave us the
proposition "this question has an answer" one way or the other,
for free, but gave us no way to compute it. That is the price of
nonconstructive existence.

One caution about what this example does and does not show. For
this one fixed question, some constant program is correct: either
"one exists" or "none exists" is the right answer, and we simply
do not know which. So what failed here is *extraction* of code
from the proof. The classical proof does not hand us a program we
can run.

### Another Example: The Halting Problem

The stronger claim is about `em` read uniformly, as the machine
`∀ P : Prop, P ∨ ¬P` that answers for *every* P. No such machine
can have executable code. To see why, specialize it to
propositions of the form `∃ n, f n = true` for an arbitrary
`f : Nat → Bool`, which is the shape of `SomeOddPerfect`. A
program implementing that case would decide whether an arbitrary
computation ever succeeds, and that is the halting problem, which
is known to be undecidable. So the absence of code behind `em` is
not a gap in Lean's implementation that a better compiler might
close. It is a theorem about computation.
@@@ -/

/- @@@
```lean
Exists.elim.{u}                 -- Given u as any universe level
  {α : Sort u}                  -- α as any type in any universe
  {p : α → Prop}                -- p as any property of α values
  {b : Prop}                    -- and b is any arbitrary proposition

  -- you can have a proof of `b` if ...
  (h₁ : ∃ a, p a)               -- (1) at least one `a` has propery `p`
  (h₂ : ∀ (a : α), p a → b)     -- (2) if *any* -- and if every `a` having `p` means `b` is true
  :                             -- *THEN*
  b                             -- b is true
```
@@@ -/

/- @@@
Example: Suppose, `h₁`, there's at least one red dog,
and, `h₂`, if every dog is red means you needn't worry
then `b`, you needn't worry.
@@@ -/

/- @@@
First we'll define the *predicate*, `Red`, on Dogs,
with proofs for all three dogs, which is all of them.
@@@ -/

inductive Red : Dog → Prop
| irisIs : Red Iris
| fidoIs : Red Fido
| sargentIs : Red Sargent
open Red

/- @@@
Now we can have a theorem proving all dogs are red.
@@@ -/

theorem allDogsRed : ∀ d, Red d :=
  fun d =>
    match d with
    | Iris => irisIs
    | Fido => fidoIs
    | Sargent => sargentIs

/- @@@
Next, we'll show that with the additional
assumption that if all dogs are red then you
needn't worry, and show from that and boh
@@@ -/

/- @@@
Finally we'll prove there's at least one red
dog. Recall that a proof of ∃ x, P x has the
shape of a (dependent) pair, where the first
element is a value and the second is a proof
of the property for that specific dog. Having
to provide a witness shows there's at least
one value of the type, while the proof shows
that that dog (whichever it might be) is red,
then together these facts prove that there is
at least one red dog.

@@@ -/

theorem existsRedDog : ∃ d, Red d :=
  Exists.intro    -- introduction rule for ∃
    Iris          -- proposed witness to the ∃ claim
    irisIs        -- proof that that dog is red


/- @@@
Note: Here's the same code using a nice notation.
It de-sugars to that type's single constructor, in
this case, `Exists.intro`.
@@@ -/
example : ∃ d, Red d := ⟨ Iris, irisIs ⟩

/- @@@
Now we have all the pieces to show that from
`∃ d, Red d`, these additional facts, and the
assumption that if every dog being red means
`b`, you needn't worry, the we can prove that
you needn't worry. Note: we assume `noWorry`
(aka, `b`) can be any proposition at all.
@@@ -/

example
  {noWorry : Prop}
  (allRedRelax : (∀ d : Dog, (Red d → noWorry))) :
  noWorry :=
  Exists.elim  existsRedDog allRedRelax

  /- @@@
I keep telling you the wrong thing here. Look at
`allRedRelax`. It now has the parentheses right. It
*if any dog is red the you have no worries*. It is
that fact combined with the fact that *there is at
least one red dog* that means you can relax now.
No worries!

`∀ d` translates to *for any dog, `d`*. Then the
part after the comma says, *if `d` (which now could
be *any* dog) is red, then `b`: you needn't worry:
if any dog is red you needn't worry.

Note that it's *not* enough in general to leave out
the existence proof. That's what ensures that there
is at least one red dog. Without that, were the Dog
type empty. We've already seen that you can always
have a function from any `uninhabited` type to `False`
(or to anything you want), as your only obligation is
to define a total function taking *every* value of the
uninhabited type, *of which there are none*, to proofs
or values of the return type.
@@@ -/

-- Suppose there are exactly zero Cows
inductive Cow where

-- and being Red or not is a property of a Cow
inductive RedCow : Cow → Prop

/- @@@
Then *all* cows, of which there are zero, are red.
To prove it, as usual you first assume you're given
any cow as an argument. As there aren't any, all of
them are red.
@@@ -/

theorem allCowsRed : ∀ c, RedCow c :=
  fun c =>      -- assume an impossibility
    nomatch c   -- then anything goes

/- @@@
From that we can prove that the proposition
asserting that if any cow is red, then there
is a proof of False, precisely because there
is no Cow at all, so the assumption that there
is one is inconsistent.
@@@ -/

theorem ifAllCowsRedThenFalse : ∀ c, (RedCow c → False) :=
  fun c => nomatch c

/- @@@
Finally let's use Lean's `axiom` keyword to force
it to accept a bad definition of exists elmination:
one that fails to require a proof of existence (which
we just comment out here to make the change visible).
This bad axiom makes our logic inconsistent, enabling
us to prove that False is true.
@@@ -/
axiom badExistsElim.{u}         -- If given `u` as any universe level
  {α : Sort u}                  -- `α` as any type in universe `u`
  {p : α → Prop}                -- `p` as any property of `α` values
  {b : Prop}                    -- and `b` as any proposition at all

  (h₂ : ∀ (a : α), p a → b) :   -- then from `∀ (a : α), (p a → b)`
  b                             -- we can derive a proof of `b`

-- Here we derive a proof of False
theorem oops : False := badExistsElim ifAllCowsRedThenFalse

/- @@@
OOPS! This is very, very bad. Adding badFalseElim
as an axiom to our logic makes it *inconsistent*.
and an inconsistent logic is useless, as everything
then becomes true, or false, as you wish.
@@@ -/

#check oops


/- @@@
The precondition that `α` be inhabited is what
protects us from such a logical catastrophe, as
it ensures that we're *not* quantifying over an
empty set so we *cannot* derive a proof of false
from it. Remember: you can never define a total
funciton from an inhabited to an uninhabited set,
as you'd have to return an result from the latter
for at least that one inhabitant, and that is not
possible, as there are no values of that type to
return. Here we'll use the correct rule of exists
elimination to derive a proof of False. You figure
out where is the inconsistent assumption that makes
this possible? If we didn't have that argument, we
would simple be unable to apply `Exists.elim` as it
requires such an argument even to be fully applied.
@@@ -/

example
  (h₁ : ∃ (c : Cow), RedCow c)               -- if at least one `a` has property `p`
  (h₂ : ∀ (c : Cow), RedCow c → False) :   -- if *any* `a` has `p` then `b`
  False :=
Exists.elim h₁ h₂

/- @@@
Of course we don't need `Exists.elim` here.
We can just eliminate the inconsisten assumption,
showing that *this can never happen*, and be
done with it.
@@@ -/

example
  (h₁ : ∃ (c : Cow), RedCow c)               -- if at least one `a` has property `p`
  (_h₂ : ∀ (c : Cow), RedCow c → False) :   -- if *any* `a` has `p` then `b`
  False :=
    nomatch h₁

/- @@@
Universal quantifications over uninhabited types
are always trivially true. You can use the word
`vacuous` to describe what you learn from such a
proof, which is nothing at all. A real failure
mode to avoid in writing proofs is to show that
something interesting theorem is true only to find
out that that's meaningless because you actually
quantified over an empty set to obtain get it. In
logical circles, you will see the term `ex falso`
used for the axiom that anything is provable from
a proof of false. In this class you learn that it's
just the elimination for false: to use a proof of
False to prove any other proposition, just apply
this axiom. In Lean, it's `False.elim`. Now look
at the recursor, or induction principle, for such
a proof. That's *ex falso*.
@@@ -/

theorem exFalso {P : Prop} : False → P :=
  fun f => nomatch f

-- And that in turn is just *induction on False*
#check (@False.elim)
#check (@False.rec)

/- @@@
As a concrete example, consider the proposition,
if `False` has a proof then every dog is friendly,
even though by our definition that is clearly false.

That assumption of something that's not true is
what entitles you to accept the entire argument as
it's premised on an assumption that can never hold.
@@@ -/

-- If there's a proof of false then there's a
-- proof of anything: here, all dogs are friendly

example : False → ∀ d, Friendly d :=
  fun f => nomatch f

/- @@@
What to remember. The inference rule of predicate
logic states that it's valid to reason as follows:
(1) if there `exists` some object `o` with property
`P`, and (2) if *any* such object has property `p`
then `b` is valid, then there's a proof `b` is valid.

And remember too, a proof of `b` is meaningless if
it's derived from either a proof of an impossibility,
such as proof of `False`, or from a vacuous universal
quantification over an empty set (an uninhabited type
in Lean / type theory).
@@@ -/

example : ∀ (_c : Cow), False := fun c => nomatch c

/- @@@
You can't do that derivation from an inhabited set.
@@@ -/

/--
error: Missing cases:
Iris
Fido
Sargent
-/
#guard_msgs in
example : ∀ (d : Dog), False := fun d => nomatch d
