/- @@@
# 4. Either

The second builder, and the one that will change how you write programs.

Data with alternatives is everywhere. A traffic light is red or yellow or
green. A payment is by card or cash or transfer. A lookup either found
something or did not. A file read either gave you the contents or gave
you a reason it could not.

Chapter 2 showed that the right tool for alternatives is a **sum**, and
that the usual substitute — a product of flags — invents states that
cannot happen and then makes you defend against them. This chapter gives
you the readable way to write sums down, and the one construct, `match`,
that takes them apart.
@@@ -/

namespace C04

/- @@@
## 4.1 The raw form, and why we leave it behind

`α ⊕ β` is the built-in sum, tagged `Sum.inl` on the left and `Sum.inr`
on the right.
@@@ -/

def aNumber : Nat ⊕ String := Sum.inl 42
def aMessage : Nat ⊕ String := Sum.inr "not a number"

#eval aNumber
#eval aMessage

/- @@@
It works, and it does not scale past two cases. Three cases means
`Unit ⊕ String ⊕ String`, four means another nesting, and at every use
site you are reading `Sum.inr (Sum.inl x)` and counting brackets to
work out which case you are in. The *counting* was right in Chapter 2;
the *notation* was indefensible.

So: `inductive`, which lets you build a sum whose cases have names.

## 4.2 Naming the cases

Here is a sum with three cases, none of which carries any data:
@@@ -/

inductive Light where
  | red
  | yellow
  | green
deriving Repr, BEq, DecidableEq

/- @@@
Read it as: a `Light` is a `red`, **or** a `yellow`, **or** a `green`.
The names after `|` are *constructors* — the only ways to build a value
of this type, and therefore the complete inventory of it.
@@@ -/

def stop : Light := Light.red
def go : Light := Light.green

#eval stop
#eval go
#eval (Light.yellow)

/- @@@
The count is `1 + 1 + 1 = 3`. Three cases, three values, exactly as many
as the world has. There is no fourth `Light`, no `"purple"`, no empty
string, nothing to defend against. Compare the `String` version from
§2.6 and notice how much work just disappeared.

When Lean already knows which type you mean, you may drop the type name
and write just the dot and the constructor:
@@@ -/

def caution : Light := .yellow

#eval caution

/- @@@
## 4.3 `match` takes a sum apart

Building a sum is choosing a case. *Using* one is asking which case you
have, and that is `match`:
@@@ -/

def description (l : Light) : String :=
  match l with
  | .red    => "stop"
  | .yellow => "prepare to stop"
  | .green  => "go"

#eval description .red
#eval description .green

/- @@@
One branch per case, and in each branch you know exactly which case you
are in. There is no "what if it is none of these" branch, because there
is no such possibility.

Lean also lets you write the `match` as the definition itself, dropping
the argument name — the form you will see most often in this book:
@@@ -/

def next : Light → Light
  | .red    => .green
  | .green  => .yellow
  | .yellow => .red

#eval next .red
#eval next (next .red)
#eval next (next (next .red))    -- back to red

/- @@@
> **Checkpoint — cycling.** `next` sends red to green, green to yellow,
> yellow to red. **Predict** `next (next .green)` before checking.
@@@ -/

#eval next (next .green)   -- predict first

/- @@@
### Exhaustiveness is checked

This is the feature that pays for the whole chapter. Leave a case out
and the program does not compile. Uncomment the following to see it:
@@@ -/

-- def incomplete : Light → String
--   | .red   => "stop"
--   | .green => "go"

/- @@@
The error says a case is missing and names it. Think about when that
error arrives: not at three in the morning when a user hits the yellow
light, but the moment you write the function.

Better still, think about what happens when you later add a fourth
light. Every `match` in your program that does not handle it becomes a
compile error, and the compiler hands you the complete list of places
you must go and think. That is the refactor that would otherwise be a
week of searching and a fortnight of bugs.

If you genuinely want to treat several cases the same way, say so with
`_`, which matches anything:
@@@ -/

def isStop : Light → Bool
  | .red => true
  | _    => false

#eval isStop .red
#eval isStop .green

/- @@@
Use `_` deliberately and sparingly. It is also a way to switch off the
exhaustiveness check that you were just told was the point, so every `_`
is a small promise that you will remember to revisit this function when
the type grows.

## 4.4 Cases that carry data

Now the real thing. A constructor may carry values, and — this is what
makes sums so much better than flags — *different cases may carry
different data*.

Here is the network status from §2.6, done properly:
@@@ -/

inductive Status where
  | loading
  | succeeded (content : String)
  | failed (code : Nat) (reason : String)
deriving Repr

/- @@@
The loading case carries nothing, because a request in flight has
nothing to report. The success case carries content. The failure carries
a code and a reason. Count it: `1 + |String| + (|Nat| × |String|)` —
precisely the three real situations, each with precisely its own data.

There is no `content` field to be empty when loading, no `code` to be
meaningless on success. The nonsense states from §2.6 are not handled;
they cannot be written.
@@@ -/

def pending : Status := .loading
def ok : Status := .succeeded "the report"
def bad : Status := .failed 404 "not found"

#eval pending
#eval ok
#eval bad

/- @@@
`match` binds the carried data to names, one branch at a time:
@@@ -/

def report : Status → String
  | .loading            => "still working…"
  | .succeeded content  => "got it: " ++ content
  | .failed code reason => "failed (" ++ toString code ++ "): " ++ reason

#eval report pending
#eval report ok
#eval report bad

/- @@@
Inside the `.succeeded` branch, `content` exists. Inside `.failed`, it
does not — and `code` and `reason` do. You can only reach data that the
case you matched actually has, which is the type system enforcing the
design rather than a comment asking you to be careful.

> **Checkpoint — carried data.** **Predict** the output of
> `report (.failed 500 "server error")`, including the punctuation, then
> check.
@@@ -/

#eval report (.failed 500 "server error")   -- predict first

/- @@@
## 4.5 `Option`: a value, or nothing

Some functions cannot answer. What is the first element of an empty
list? What is the entry for a key that is not in the table? What is
`10 / 0`?

The usual answers are bad. Return `-1` and hope no real answer is `-1`.
Return an empty string, ambiguous with an empty result. Crash. Or return
a null pointer, and let the caller find out at runtime — an idea whose
inventor called it his billion-dollar mistake.

The kit already has the answer: one case for "nothing", and one for "a
value". That is `1 + |α|`, and it is built in, called `Option`:
@@@ -/

#check (none : Option Nat)
#check (some 42 : Option Nat)
#eval (none : Option Nat)
#eval some 42

/- @@@
Had it not been built in, you would write it yourself in three lines —
and you should, once, to see that there is no magic:
@@@ -/

inductive Maybe (α : Type) where
  | nothing
  | just (value : α)
deriving Repr

#eval (Maybe.just 5)
#eval (Maybe.nothing : Maybe Nat)

/- @@@
(The `(α : Type)` part is the fifth builder, **abstract**, arriving early
because `Option` needs it. Chapter 7 is about it properly. For now read
`Maybe α` as "a `Maybe` holding `α`s".)

Now functions that might not answer can say so in their type:
@@@ -/

def safeDiv (a b : Nat) : Option Nat :=
  if b == 0 then none else some (a / b)

#eval safeDiv 10 2     -- some 5
#eval safeDiv 10 0     -- none

/- @@@
The payoff is at the call site. A caller cannot use the result without
deciding what to do when there is none, because the only way in is a
`match`, and `match` must cover both cases:
@@@ -/

def showDiv (a b : Nat) : String :=
  match safeDiv a b with
  | some n => toString n
  | none   => "undefined"

#eval showDiv 10 2
#eval showDiv 10 0

/- @@@
Read `Option Nat` as a promise made in the type: *I might not have an
answer, and you must handle that.* Compare a language where every value
might secretly be null: there, the promise is made nowhere and must be
remembered everywhere.

`Option` composes with everything else in the kit. A lookup in a list of
pairs is the classic:
@@@ -/

def lookup (key : String) : List (String × Nat) → Option Nat
  | []          => none
  | (k, v) :: rest => if k == key then some v else lookup key rest

def ages : List (String × Nat) := [("ada", 36), ("grace", 45), ("alan", 41)]

#eval lookup "grace" ages     -- some 45
#eval lookup "kevin" ages     -- none

/- @@@
(That definition takes a list apart by cases, which is Chapter 6's
business. Skim it; the point here is the `Option` in the result type.)

> **Checkpoint — `Option` at the call site.** **Predict** both values
> below, and say why the second cannot be confused with an age of zero.
@@@ -/

#eval lookup "ada" ages     -- predict first
#eval lookup "zoe" ages     -- predict first

/- @@@
## 4.6 `Except`: nothing, with a reason

`Option` says there is no answer. It does not say why, and often the why
is the most important thing you have.

`Except ε α` is the sum for that: either an error of type `ε`, or a
success of type `α`. Count: `|ε| + |α|`. Same shape as `Option`, with
the "nothing" case upgraded to carry an explanation.
@@@ -/

def parsePositive (s : String) : Except String Nat :=
  match s.toNat? with
  | none   => .error ("not a number: " ++ s)
  | some 0 => .error "zero is not positive"
  | some n => .ok n

#eval parsePositive "42"
#eval parsePositive "0"
#eval parsePositive "banana"

/- @@@
Note the middle branch: it matches `some 0` specifically, and `some n`
catches everything else. Patterns may look inside other patterns, and
they are tried in order, so the specific case goes first.

Consuming an `Except` is a `match` over its two cases:
@@@ -/

def describeParse (s : String) : String :=
  match parsePositive s with
  | .ok n      => "parsed " ++ toString n
  | .error msg => "rejected: " ++ msg

#eval describeParse "7"
#eval describeParse "banana"

/- @@@
Choosing between the two is straightforward. Use `Option` when absence
is ordinary and self-explanatory — a key that is not in the table, an
empty list's first element. Use `Except` when the caller will want to
know what went wrong, report it, or decide based on it.

## 4.7 What you have

| Situation | Builder | Count |
|---|---|---|
| a fixed set of named cases | `inductive`, no data | one per case |
| cases with their own data | `inductive`, constructors with fields | sum of each case's product |
| a value or nothing | `Option α` | `1 + m` |
| a value or an error | `Except ε α` | `n + m` |
| either of two types | `α ⊕ β` | `m + n` |

And three habits worth keeping:

1. **Alternatives mean a sum.** The moment you catch yourself adding a
   second `Bool` flag to describe one thing, stop and list the cases.
2. **Let each case carry its own data.** A field that is meaningless in
   some cases belongs to a constructor, not to the whole type.
3. **Let the exhaustiveness checker do the work.** Avoid `_` unless you
   mean it, and treat "non-exhaustive match" as good news.

## Exercises

**[4.1]** Define `inductive Suit` with the four card suits, deriving
`Repr`, `BEq`, `DecidableEq`. Then `isRed : Suit → Bool`, true for hearts
and diamonds. Write it *without* `_` so the compiler checks all four.

```lean
#guard isRed .hearts = true
#guard isRed .diamonds = true
#guard isRed .spades = false
#guard isRed .clubs = false
```

**[4.2]** Define `inductive Shape` with three cases: a circle carrying a
radius, a rectangle carrying width and height, and a square carrying one
side. All lengths are `Float`. Then `area : Shape → Float`.

```lean
#guard area (.square 3.0) == 9.0
#guard area (.rectangle 2.0 5.0) == 10.0
```

Then answer: your `Shape` can represent a square in two ways — as
`.square 3.0` and as `.rectangle 3.0 3.0`. Is that a problem? Say what
it costs, and what you would have to give up to remove it.

**[4.3]** Define `safeHead : List Nat → Option Nat`, returning the first
element if there is one. Pattern-match on `[]` and `x :: _`.

```lean
#guard safeHead [] = none
#guard safeHead [7, 8, 9] = some 7
```

**[4.4]** Define `initial : Status → String` over §4.4's `Status`, giving
`"L"`, `"S"`, `"F"` for the three cases. Now add a fourth case,
`| cancelled`, to `Status` and recompile. Write down every error you
get, fix them, and say in one line what that experience tells you about
adding a case to a type in a large program.

**[4.5]** `Option Bool` — how many values, and what are they? Write them
all out. Now: someone proposes using `Option Bool` for a yes/no/no-answer
survey question. Is the count right? Is the *naming* right? Which would
you ship, and why?

```lean
#guard allOptionBools.length = 3
```

**[4.6]** Rewrite `safeDiv` from §4.5 to return
`Except String Nat`, with a message naming the problem. Then say which
of the two versions you would want if you were writing a calculator's
display, and which if you were writing a spreadsheet cell — and why the
answers differ.

```lean
#guard exceptDiv 10 2 = .ok 5
#guard exceptDiv 10 0 = .error "division by zero"
```
@@@ -/

end C04
