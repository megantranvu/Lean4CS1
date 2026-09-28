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
## Used to Distinguish Variable Expressions
```lean
inductive Variable where
| Xvar
| Yvar
| Zvar

open Variable
```

## Syntax of Propositional Logic

- literal expressions (T, F)
- operator expressions (And, Or, Not)
- variable expressions (Var)
```lean
inductive PropLogicSyntax where
| T
| F
| And (left right : PropLogicSyntax) : PropLogicSyntax
| Or (left right : PropLogicSyntax) : PropLogicSyntax
| Not (p : PropLogicSyntax)
| Var (v : Variable)

open PropLogicSyntax
```

## Three Variable Expressions
```lean
def X : PropLogicSyntax := PropLogicSyntax.Var Xvar
def Y : PropLogicSyntax := PropLogicSyntax.Var Yvar
def Z : PropLogicSyntax := PropLogicSyntax.Var Zvar
```

## Interpretations
```lean
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
```

## Operational semantics for propositional logic
```lean
def eval : PropLogicSyntax → varInterp → Bool
| T, _ => true
| F, _ => false
| (PropLogicSyntax.And p1 p2), i => (eval p1 i) && (eval p2 i)
| (PropLogicSyntax.Or p1 p2), i => (eval p1 i) || (eval p2 i)
| (PropLogicSyntax.Not p1), i => !(eval p1 i)
| (PropLogicSyntax.Var v), i => i v
```

## Examples
```lean
def e1 := F
def e2 := T
def e3 := PropLogicSyntax.And e1 e2
def e4 := PropLogicSyntax.And X Y

#eval eval e1 i1
#eval eval e2 i1
#eval eval e3 i1
#eval eval e4 i1
#eval eval e4 i2
```

## Notations: A Concrete Syntax for Our Language

Everything above is written in *abstract syntax*: we build
expressions by applying constructors, as in

  *PropLogicSyntax.And (PropLogicSyntax.Not X) Y*

Logicians instead write *¬X ∧ Y*. Nothing changes about the
language: notations add a *concrete syntax*, a surface form
that the parser translates back into exactly those constructor
applications. A notation declaration fixes three things:

- the **token(s)**, e.g. *∧*, and where the operands sit;
- the **precedence**, a numPr3pleber saying how tightly the operator
  binds: higher numbers grab their operands first, so *∧* at 35
  beats *∨* at 30 and *¬X ∧ Y ∨ Z* means *((¬X) ∧ Y) ∨ Z*;
- the **associativity**, which settles how an operator combines
  with itself: *infixr* groups to the right, *infixl* to the
  left, plain *infix* refuses to group at all.

The levels we choose are exactly the ones Lean uses for the
corresponding connectives on *Prop*, so reading our language
and reading Lean's own logic are the same skill:

| Notation | Declaration | Level | Associativity |
|----------|-------------|-------|---------------|
| *⊤*, *⊥* | *notation:max* | max | n/a (atoms) |
| *¬p*     | *notation:max ... p:40* | max, arg at 40 | n/a (prefix) |
| *p ∧ q*  | *infixr:35* | 35 | right |
| *p ∨ q*  | *infixr:30* | 30 | right |
| *p ⇒ q*  | *infixr:25* | 25 | right |
| *p ⇔ q*  | *infix:20*  | 20 | none |

Two things to notice. First, *¬* is declared at *max* but takes
its argument at level 40: that is what makes *¬* bind tighter
than every binary connective while still refusing to swallow
one (*¬X ∧ Y* is *(¬X) ∧ Y*, never *¬(X ∧ Y)*). Second, *⇔* is
*infix*, not *infixr*, so *X ⇔ Y ⇔ Z* is a *parse error* rather
than a silently chosen grouping. That is a feature: the
biconditional is not associative in ordinary mathematical usage,
so we make the parser demand parentheses.
```lean
namespace PropLogicSyntax
```

### Two Derived Connectives

Implication and the biconditional get notations too, but they are
*not* new constructors: *PropLogicSyntax* is unchanged, and so
*eval* remains exhaustive and needs no new case. They are simply
functions that build expressions out of the primitive three. This
is the standard move of defining a *derived* connective: *p ⇒ q*
abbreviates *¬p ∨ q*, and *p ⇔ q* abbreviates *(p ⇒ q) ∧ (q ⇒ p)*.
```lean
def Imp (p q : PropLogicSyntax) : PropLogicSyntax := Or (Not p) q
def Iff (p q : PropLogicSyntax) : PropLogicSyntax := And (Imp p q) (Imp q p)
```

### The Notations Themselves

*scoped* means these notations are active only where the
*PropLogicSyntax* namespace is open, so they do not leak into
files that merely import this one.

We write *⇒* and *⇔* rather than *→* and *↔* deliberately: *→*
is Lean's own function-type arrow, which is built into the term
grammar, and overloading it would be genuinely ambiguous. By
contrast *∧*, *∨*, and *¬* are safe to overload: Lean already
uses them for *Prop*, and since our operands have type
*PropLogicSyntax* rather than *Prop*, elaboration picks the
right reading from the types.
```lean
-- Literal expressions: atomic, so they bind as tightly as possible
scoped notation:max "⊤" => PropLogicSyntax.T
scoped notation:max "⊥" => PropLogicSyntax.F

-- Negation: prefix, binding tighter than any binary connective
scoped notation:max "¬" p:40 => PropLogicSyntax.Not p

-- Binary connectives, each binding more loosely than the last
scoped infixr:35 " ∧ " => PropLogicSyntax.And
scoped infixr:30 " ∨ " => PropLogicSyntax.Or
scoped infixr:25 " ⇒ " => PropLogicSyntax.Imp

-- Biconditional: infix, not infixr, so it will not self-associate
scoped infix:20 " ⇔ " => PropLogicSyntax.Iff

end PropLogicSyntax
```

### Expressions in Concrete Syntax

The notations are available here because *PropLogicSyntax* was
opened at the top of this file. Notations work in both directions:
Lean parses them, and it also *prints* results using them, so
*#check* below echoes the concrete syntax back at us.
```lean
#check ¬X ∧ Y                 -- (¬X) ∧ Y
#check X ∧ Y ∨ Z              -- (X ∧ Y) ∨ Z
#check X ∨ Y ⇒ Z              -- (X ∨ Y) ⇒ Z
#check X ⇒ Y ⇔ Z              -- (X ⇒ Y) ⇔ Z
#check ⊤ ∧ ⊥

-- e4 from above, now in concrete syntax
def e5 := X ∧ Y
#eval eval e5 i1              -- true
#eval eval e5 i2              -- false

#eval eval (¬X ∧ Y) i2        -- true: X is false under i2
#eval eval (X ⇒ Y) i1         -- true
#eval eval (X ⇔ Y) i2         -- false
```

### Checking That the Parser Agrees

Claims about precedence and associativity are claims about what
expression the parser builds, and those are claims we can *prove*.
Each theorem below says that a notated expression is literally the
same term as the constructor application we intended, so *rfl*
suffices. If a precedence were wrong, the proof would fail.
```lean
-- ¬ binds tighter than ∧
example : (¬X ∧ Y) = PropLogicSyntax.And (PropLogicSyntax.Not X) Y := rfl

-- ∧ binds tighter than ∨
example : (X ∧ Y ∨ Z) = PropLogicSyntax.Or (PropLogicSyntax.And X Y) Z := rfl
example : (X ∨ Y ∧ Z) = PropLogicSyntax.Or X (PropLogicSyntax.And Y Z) := rfl

-- ∧ and ∨ associate to the right
example : (X ∧ Y ∧ Z) = PropLogicSyntax.And X (PropLogicSyntax.And Y Z) := rfl
example : (X ∨ Y ∨ Z) = PropLogicSyntax.Or X (PropLogicSyntax.Or Y Z) := rfl

-- ∨ binds tighter than ⇒, and ⇒ associates to the right
example : (X ∨ Y ⇒ Z) = PropLogicSyntax.Imp (PropLogicSyntax.Or X Y) Z := rfl
example : (X ⇒ Y ⇒ Z) = PropLogicSyntax.Imp X (PropLogicSyntax.Imp Y Z) := rfl

-- ⇒ binds tighter than ⇔
example : (X ⇒ Y ⇔ Z) = PropLogicSyntax.Iff (PropLogicSyntax.Imp X Y) Z := rfl
example : (X ⇔ Y ⇒ Z) = PropLogicSyntax.Iff X (PropLogicSyntax.Imp Y Z) := rfl

-- Uncomment to see the non-associativity of ⇔ reported as a parse error:
-- #check X ⇔ Y ⇔ Z
```

### Exercise

Add a notation for exclusive or. Define *Xor* as a derived
connective in terms of the primitives, choose a token and a
precedence level (should it bind more or less tightly than *∨*?),
decide on its associativity, and then write the *rfl* theorems
that confirm your choices parse the way you expect.

<div class="issue-box">📝 <a href="https://github.com/kevinsullivan/Lean4CS1/issues/new">Report an issue</a> with this section</div>

