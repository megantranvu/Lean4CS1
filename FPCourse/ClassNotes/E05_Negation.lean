/- @@@

# Notes 9/21/26


- Curry-Howard Injection: Deductive Reasoning (Prop) => Computation (Type)

- Deep vs Shallow embedding of abstract theories into Lean 4
  - Deep embedding: Syntax as a type with constructor for each kind of term (propositional logic)
  - Shallow embedding: Syntax as collection of types, one for each kind of term (predicate logic)

  - Empty and False
  - Unit and True
  - Prod and And
  - Sum and Or
  - -> Empty and -> False (Not!)


@@@ -/

def e2e : Empty → Empty
| e => e

def fimpf : False → False
| f => f

inductive MyEmpty : Type where

def me2e : MyEmpty → Empty
| m => nomatch m

inductive MyFalse : Prop where
-- | mk

theorem myFalseIsReallyFalse : MyFalse → False
| m => nomatch m

def neg (a : Prop) : Prop := a → False

#check MyFalse

example : neg MyFalse
| m => nomatch m

example : ¬MyFalse
| m => nomatch m

#check (@And)

inductive KevinIsFromCville : Prop where
| driversLicense

example : KevinIsFromCville := KevinIsFromCville.driversLicense

inductive JorgIsFromToronto : Prop where
| driversLicense
| utilityBill
| healthCard

example : And KevinIsFromCville JorgIsFromToronto :=
And.intro
  KevinIsFromCville.driversLicense
  JorgIsFromToronto.healthCard

inductive Cat : Type where
| siamese
| tabby

example : ¬ (Cat.tabby = Cat.siamese)
| m => nomatch m

example :
JorgIsFromToronto.driversLicense = JorgIsFromToronto.healthCard :=
rfl


/- @@@
## DeMorgan's Laws

For arbitrary propositions P and Q, negation distributes over
disjunction in both directions, constructively:
  ¬(P ∨ Q) ↔ (¬P ∧ ¬Q).

For conjunction, only (¬P ∨ ¬Q) → ¬(P ∧ Q) holds constructively
in general. The reverse implication,
  ¬(P ∧ Q) → (¬P ∨ ¬Q),
does not: knowing that P and Q cannot both hold does not give us
a choice of which one to refute. A proof of the disjunction must
provide either a proof of ¬P or a proof of ¬Q. Excluded middle
would let us split on P, but is not available constructively.
@@@ -/

-- Warmup: Negation

theorem noContradiction {P : Prop} : ¬(P ∧ ¬P) :=
  fun pandNotP => pandNotP.right pandNotP.left



theorem deMorganNotOr (P Q : Prop) : ¬(P ∨ Q) → (¬P ∧ ¬Q) :=
  fun notPorQ =>
    And.intro
      (fun p => notPorQ (Or.inl p))
      (fun q => notPorQ (Or.inr q))

theorem deMorganAndNot (P Q : Prop) : (¬P ∧ ¬Q) → ¬(P ∨ Q) :=
  fun notPandNotQ =>
    fun porq =>
      match porq with
      | Or.inl p => notPandNotQ.left p
      | Or.inr q => notPandNotQ.right q

theorem deMorganOrNot (P Q : Prop) : (¬P ∨ ¬Q) → ¬(P ∧ Q) :=
  fun notPorNotQ =>
    fun pandq =>
      match notPorNotQ with
      | Or.inl notP => notP pandq.left
      | Or.inr notQ => notQ pandq.right

theorem deMorganNotOrIff (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) :=
  Iff.intro (deMorganNotOr P Q) (deMorganAndNot P Q)

/- @@@
Trying the reverse direction: choose the left disjunct, ¬P,
and assume P. To use ¬(P ∧ Q) to get False, we still need Q,
but nothing supplies it. Choosing the right disjunct instead
leaves the symmetric problem of needing P.

`#guard_msgs` checks the expected error, so this intentionally
unfinished attempt does not prevent the file from compiling.
@@@ -/

/--
error: don't know how to synthesize placeholder for argument `right`
context:
P Q : Prop
notPandQ : ¬(P ∧ Q)
p : P
⊢ Q
-/
#guard_msgs in
example (P Q : Prop) : ¬(P ∧ Q) → (¬P ∨ ¬Q) :=
  fun notPandQ =>
    Or.inl (fun p => notPandQ (And.intro p _))

example (P Q : Prop) : (¬P ∨ ¬Q) → ¬(P ∧ Q) :=
  fun notPorNotQ =>
    fun pandq =>
      match notPorNotQ with
      | Or.inl notP => notP pandq.left
      | Or.inr notQ => notQ pandq.right

/- @@@
## Proof by Negation and by Contradiction

Constructively, we can prove ¬P by assuming P and deriving False:
that is exactly what a proof of P → False does. The theorem above
uses this reasoning to prove that P and ¬P cannot both hold. This
*proof strategy* is properly called *proof by negation*. It is not
*proof by contradiction*, even though deriving a contradiction is
the key step.

But suppose we want to prove P by assuming ¬P and deriving False.
What we have constructed is (¬P → False), which is ¬¬P. In general,
constructive logic does not let us turn this into a proof of P.
This extra step is called double-negation elimination, or the
classical rule of proof by contradiction.

Here is where a term-mode attempt gets stuck. `False.elim` can
produce P from False, but to get False from `notNotP` we must
supply a proof of ¬P. We have no such proof. The hole below asks
for exactly that missing input. This illustrates the obstruction;
a failed attempt alone is not a proof of unprovability.
@@@ -/

/--
error: don't know how to synthesize placeholder
context:
P : Prop
notNotP : ¬¬P
⊢ ¬P
-/
#guard_msgs in
example (P : Prop) : ¬¬P → P :=
  fun notNotP => False.elim (notNotP _)

/- @@@
## One Additional Assumption: Excluded Middle

Put a single additional assumption on the left of an implication:

  (∀ P : Prop, P ∨ ¬P) → (∀ P : Prop, ¬¬P → P).

Call the supplied proof `em`. Its type is ∀ P : Prop, P ∨ ¬P.
Under Curry-Howard, this is a machine: give it any proposition P,
and `em P` gives us a *proof* of P ∨ ¬P, for free! We supply no
evidence about P. Its output is a proof-bearing disjunction:
either `Or.inl p`, carrying a proof p of P, or `Or.inr notP`,
carrying a proof notP of ¬P. It is not just a Boolean answer.
We are assuming this machine, not implementing a constructive
algorithm that decides every proposition.

Now split on the proof `em P`. In the first case we already have
the desired proof of P. In the second case we have precisely the
proof of ¬P missing above. Applying `notNotP` to it gives False,
and `False.elim` turns that contradiction into a proof of P.
@@@ -/

theorem proofByContradictionFromExcludedMiddle :
    (∀ P : Prop, P ∨ ¬P) → (∀ P : Prop, ¬¬P → P) :=
  fun em =>
    fun P =>
      fun notNotP =>
        match em P with
        | Or.inl p => p
        | Or.inr notP => False.elim (notNotP notP)

/- @@@
All steps in this proof are constructive uses of the supplied
assumption. The classical power comes from `em`: keeping it on
the left makes explicit what the proof-by-contradiction rule needs.
@@@ -/

/- @@@
## Constructive and Classical Logic in Lean

Constructive logic requires evidence for the claims we make;
it does not supply P ∨ ¬P for every arbitrary proposition P.
Classical logic adds excluded middle (or an equivalent principle),
so general proof by contradiction becomes available. Both logics
allow us to derive any proposition from a proof of False.

In Lean, we can write `open Classical` and then use `em P` to
obtain a proof of P ∨ ¬P. Opening the namespace only makes names
such as `Classical.em` available as `em`; it does not itself make
a proof classical. Using this principle supplies the classical
power. We can also write `Classical.em P` without opening anything.
Although we often call excluded middle an axiom of classical logic,
Lean's `Classical.em` is a theorem derived using its underlying
axioms, including classical choice.

The example below supplies the proof machine from Lean's library,
so we no longer need to ask for it as an explicit assumption.
The two cases are exactly the ones in our previous proof.
@@@ -/

open Classical

/- @@@
Here is the full type of the library's excluded-middle theorem:

  Classical.em : ∀ (P : Prop), P ∨ ¬P

It takes a proposition P and returns a proof of P ∨ ¬P, with no
proof about P required as input. `#check` displays its type;
`#print` displays its actual definition, including the library's
proof body. We use this existing theorem rather than declare a
new axiom.
@@@ -/

#check (em : ∀ (P : Prop), P ∨ ¬P)
#print em

/- @@@
Here then is the elimination rule for negation, which is *not*
constructively valid.
@@@ -/
example (P : Prop) : ¬¬P → P :=
  fun notNotP =>
    match em P with
    | Or.inl p => p
    | Or.inr notP => False.elim (notNotP notP)

/- @@@
## The Tradeoff: Proofs Without Executable Constructions

With `em`, we gain the general rule of proof by contradiction:
from ¬¬P we can prove P. The price is that our proof now relies
on a machine for which we have no executable implementation.
`em P` supplies a proof of P ∨ ¬P, but it is not an algorithm
we can run to discover which side holds for an arbitrary P.

Look again at the match above. Each branch tells us what to do
with its evidence: return p, or derive False from notP. Those
branches are explicit, but `em` does not supply executable code
to select a branch. Thus this proof of ¬¬P → P is a valid logical
construction, not a general executable procedure for turning a
proof of ¬¬P into a constructively computed proof of P.

Lean still checks the entire proof term, including both branches;
classical reasoning does not bypass proof checking. What we lose
is the guarantee of a computational interpretation for this step.
In Lean, proofs in `Prop` are erased during compilation anyway,
including constructive proofs. So going classical does not delete
existing program code. Rather, using `em` adds a logical capability
without adding an executable implementation of that capability.
@@@ -/

/- @@@
## Next Lecture: Existence, Witnesses, and Nonconstructive Proofs

`∃ x : α, R x` says that some value x has property R. To introduce
an existential proof constructively, provide a *witness* w : α
and a proof of R w. `Exists.intro` packages these together:
@@@ -/

example : ∃ n : Nat, n = 3 :=
  Exists.intro 3 rfl

/- @@@
To eliminate an existential proof, unpack its witness and evidence
and use them to prove a conclusion S. The conclusion must not
depend on which witness was hidden inside the existential:
@@@ -/

example {α : Type} (R : α → Prop) (S : Prop) :
    (∃ x : α, R x) → (∀ x : α, R x → S) → S :=
  fun existsRx =>
    fun useWitness =>
      match existsRx with
      | Exists.intro w rw => useWitness w rw

/- @@@
This is reasoning with a witness inside a proof. Lean's `Exists`
lives in `Prop`; unpacking it to prove S does not give us a general
executable function that returns its witness as data.

Classically, we can also prove existence by contradiction, without
explicitly constructing a witness. Substitute `∃ x, R x` for P
in our previous proof:
@@@ -/

example {α : Type} (R : α → Prop) :
    (¬(∃ x : α, R x) → False) → ∃ x : α, R x :=
  fun notNotExists =>
    match em (∃ x : α, R x) with
    | Or.inl existsRx => existsRx
    | Or.inr notExists => False.elim (notNotExists notExists)

/- @@@
## A Provocation: Banach–Tarski

The Banach–Tarski theorem (1924) says that a solid ball in
three-dimensional space can be partitioned into finitely many
sets, then those sets moved by rotations and translations to
form two disjoint balls, each the same size as the original.
The usual proof uses the axiom of choice. The pieces cannot all
have ordinary volume: nonmeasurable sets are involved. This is
a theorem about sets of points, not a physical recipe for cutting
up a ball and doubling its material.
See [Banach and Tarski's original paper](https://pldml.icm.edu.pl/pldml/element/bwmeta1.element.bwnjournal-article-fmv6i1p27bwm)
and [Terence Tao's explanation](https://www.math.ucla.edu/~tao/resource/general/121.1.00s/tarski.html).

It vividly illustrates the constructive objection: what counts
as evidence that these pieces exist if we cannot construct them
in the required sense? A constructivist does not have to accept
the classical proof as a constructive existence proof. The issue
is the justification of existence, not merely that the conclusion
is surprising. Excluded middle alone should not be confused with
the choice principle used in the Banach–Tarski argument.

Historically, this did not launch constructive mathematics:
Brouwer's foundational work dates to 1907–1908, before this
theorem. Use Banach–Tarski as an illustration of the demand for
construction that motivated constructive approaches, rather than
as their historical cause. Heyting later formalized intuitionistic
(constructive) logic. See [the history of intuitionistic logic](https://plato.stanford.edu/entries/intuitionistic-logic-development/).
@@@ -/
