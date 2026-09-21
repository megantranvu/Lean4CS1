/- @@@
# Deep Embedding (here) vs Shallow Embedding

We've started "implementing" the langauge of predicate
logic by mapping logical connectives, such as *And* (∧)
to corresponding types. The implementation of the language
comprises multiple type definitions, includig one type for
each connective. This method is called *shallow* embedding
of a language into the logic of Lean.

A deep embdedding by contrast maps each connective in
the syntax of the language to a corresponding constructor
of a single language-syntax-defining type. Here's what we
define in class: both the syntax and the semantics of
*propositional* (isomorphic to Boolean) logic.
@@@ -/

/- @@@
## Used to Distinguish Variable Expressions
@@@ -/
inductive Variable where
| Xvar
| Yvar
| Zvar

open Variable

/- @@@
## Syntax of Propositional Logic
@@@ -/
inductive PropLogicSyntax where
-- literal expressions
| T
| F
-- operator expressions
| And (left right : PropLogicSyntax) : PropLogicSyntax
| Or (left right : PropLogicSyntax) : PropLogicSyntax
| Not (p : PropLogicSyntax)
-- variable expressions
| Var (v : Variable)

open PropLogicSyntax

/- @@@
## Three Variable Expressions
@@@ -/
def X : PropLogicSyntax := PropLogicSyntax.Var Xvar
def Y : PropLogicSyntax := PropLogicSyntax.Var Yvar
def Z : PropLogicSyntax := PropLogicSyntax.Var Zvar

/- @@@
## Interpretations
@@@ -/

def varInterp : Type := Variable → Bool

-- Two distinct interpretations
def i1 : varInterp :=
  fun (v : Variable) =>
    match v with
    | Xvar => true
    | Yvar => true
    | Zvar => true

def i2 : varInterp :=
  fun (v : Variable) =>
    match v with
    | Xvar => false
    | Yvar => true
    | Zvar => true

/- @@@
## Operational semantics
@@@ -/
def eval : PropLogicSyntax → varInterp → Bool
| T, _ => true
| F, _ => false
| (PropLogicSyntax.And p1 p2), i => (eval p1 i) && (eval p2 i)
| (PropLogicSyntax.Or p1 p2), i => (eval p1 i) || (eval p2 i)
| (PropLogicSyntax.Not p1), i => !(eval p1 i)
| (PropLogicSyntax.Var v), i => i v

/- @@@
## Examples
@@@ -/
def e1 := F
def e2 := T
def e3 := PropLogicSyntax.And e1 e2
def e4 := PropLogicSyntax.And X Y

#eval eval e1 i1
#eval eval e2 i1
#eval eval e3 i1
#eval eval e4 i1
#eval eval e4 i2
