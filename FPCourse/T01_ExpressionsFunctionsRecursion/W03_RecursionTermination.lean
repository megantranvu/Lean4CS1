-- FPCourse/T01_ExpressionsFunctionsRecursion/W03_RecursionTermination.lean
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

/-! @@@
# Recursion and Termination

## Structural recursion

Here is a way to think about recursion that is the *inverse* of the usual
story.

The usual story: "the function calls itself on a smaller input until it
reaches a base case."  That describes *execution*, but it does not explain
*why the definition gives a correct answer for every input*.

The better story starts from what you actually need in order to define a
function on the natural numbers:

1. **A base case.** You supply the answer for input `0` directly.
2. **A step function.** You supply a rule that, *given any input `n` and the
   answer for `n`*, produces the answer for `n + 1`.

Those two ingredients are enough to determine the answer for *every* natural
number: start with the answer for `0`, apply the step once to get the answer
for `1`, again to get the answer for `2`, and so on.  However large the input,
you can always reach it by iterating the step enough times from the base.

This is the content of the *principle of recursion* (or primitive recursion)
on the natural numbers.  The recursive definition in Lean is just a compact
way of writing down these two ingredients:

- The `| 0 => ...` clause supplies the base-case answer.
- The `| n + 1 => ...` clause supplies the step function.  The right-hand side
  may refer to `n` (the previous input) and to the recursive call `f n` (the
  answer for `n`).  That recursive call is not "calling itself" in some
  mysterious way — it is simply *using the assumption that the answer for `n`
  is already in hand*, which the step function is entitled to assume by
  construction.

Lean can verify termination automatically for structural recursion because
it can see that the step clause only ever asks for the answer at `n`, not at
any larger value.
@@@ -/

namespace W03

/-! @@@
## 3.1  Factorial — direct recursive definition
@@@ -/

def factorial : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 0   -- 1
#eval factorial 5   -- 120
#eval factorial 10  -- 3628800
-- rfl-based tests: both sides reduce to the same normal form
example : factorial 0 = 1   := rfl
example : factorial 5 = 120 := rfl

/-! @@@
**Reading the definition.**  Apply the two-ingredient view to `factorial`:

- **Base case** (`| 0 => 1`): the answer for `0` is `1`.
- **Step** (`| n + 1 => (n + 1) * factorial n`): given input `n + 1`, and
  given that the answer for `n` is already `factorial n`, multiply them.

To see why this gives the right answer for `3`, iterate the step up from the base:

```
factorial 0 = 1                              -- base case
factorial 1 = 1 * factorial 0 = 1 * 1 = 1   -- step: n = 0, answer for 0 = 1
factorial 2 = 2 * factorial 1 = 2 * 1 = 2   -- step: n = 1, answer for 1 = 1
factorial 3 = 3 * factorial 2 = 3 * 2 = 6   -- step: n = 2, answer for 2 = 2
```

Each line uses the answer from the line above — exactly the "answer for `n`
already in hand" that the step clause is entitled to assume.

Lean's evaluator runs this in the opposite order — it unfolds `factorial 3`
toward the base case and assembles the result on the way back up.  Either
direction produces `6`.  The inductive framing explains *why* there is
a well-defined answer for every input, not just how to compute it.
@@@ -/

/-! @@@
> **Checkpoint — `factorial`.** Iterate the step once more from `factorial 3 = 6`:
> `factorial 4 = 4 * factorial 3`.  **Predict** the value below before reading it.
@@@ -/

#eval factorial 4   -- predict first  (4 * 6)

/-! @@@
## 3.2  Tail recursion and accumulators

The direct definition rebuilds the product on the way *back* from the
base case.  A tail-recursive version accumulates the product on the way
*down*, so the recursive call is the last thing done.

Tail-recursive functions are important in practice because they run in
constant stack space.  They can also have different proofs of correctness,
which is why we need to state the relationship between the two versions.
@@@ -/

def factorialAcc : Nat → Nat → Nat
  | 0,     acc => acc
  | n + 1, acc => factorialAcc n ((n + 1) * acc)

def factorialTR (n : Nat) : Nat := factorialAcc n 1

-- Evaluation: factorialTR 3
--   ↝ factorialAcc 3 1
--   ↝ factorialAcc 2 (3 * 1)   ↝ factorialAcc 2 3
--   ↝ factorialAcc 1 (2 * 3)   ↝ factorialAcc 1 6
--   ↝ factorialAcc 0 (1 * 6)   ↝ factorialAcc 0 6
--   ↝ 6                          (first clause: acc is returned)
-- Notice: the accumulator grows on the way DOWN; no work on the way back up.
#eval factorialTR 5   -- 120
example : factorialTR 5 = 120 := rfl

/-! @@@
> **Checkpoint — `factorialTR` accumulates on the way down.** The accumulator carries the
> running product, so the recursive call is the last thing done.  **Predict** `factorialTR 4`
> (trace the accumulator from `1`), then check.
@@@ -/

#eval factorialTR 4   -- predict first

/-! @@@
## 3.3  Specification: the two definitions agree

The following theorem states that the accumulator version computes the
same value as the direct version, for any starting accumulator.

**You are not expected to construct this proof.**  It is provided so
you can see that such a proof exists and what it looks like.  The proof
is a term — a recursive function on `n` whose type is the specification.

Read the term as: "by induction on n; the base case is a calculation;
the step uses the inductive hypothesis for n with a different accumulator."
@@@ -/

-- Provided term-mode proof.  Read it; do not reproduce it.
theorem factorialAcc_spec : ∀ (n acc : Nat),
    factorialAcc n acc = acc * factorial n := by
  intro n
  induction n with
  | zero => intro acc; simp [factorialAcc, factorial]
  | succ n ih =>
    intro acc
    simp only [factorialAcc, factorial]
    rw [ih]
    ring

-- Corollary: factorialTR agrees with factorial
theorem factorialTR_spec (n : Nat) : factorialTR n = factorial n :=
  Eq.trans (factorialAcc_spec n 1) (Nat.one_mul (factorial n))

/-! @@@
> **Checkpoint — the two definitions agree.** `factorialTR_spec` says `factorialTR n =
> factorial n` for every `n`.  **Predict** the Boolean below *from the spec* (not by
> computing both sides), then check.
@@@ -/

#eval decide (factorialTR 6 = factorial 6)   -- predict from factorialTR_spec

/-! @@@
## 3.4  Non-structural termination

When recursion does not follow the structure of an inductive type,
Lean requires an explicit *termination measure*: a quantity that strictly
decreases at each recursive call with respect to some well-founded relation.

The `termination_by` clause names the measure.
@@@ -/

-- Euclidean GCD — not structurally recursive on either argument,
-- but decreases on the second argument at each step.
def gcd : Nat → Nat → Nat
  | a, 0     => a
  | a, b + 1 => gcd (b + 1) (a % (b + 1))
termination_by _ b => b
decreasing_by apply Nat.mod_lt; omega

#eval gcd 48 18   -- 6
#eval gcd 100 75  -- 25

/-! @@@
> **Checkpoint — `gcd` (non-structural termination).** `gcd` recurses on a *decreasing
> measure* (the second argument), not on a strict subterm.  **Predict** `gcd 24 36`, then
> check.  Because `gcd` is well-founded, only `#eval` reduces it — `rfl`/`decide` cannot,
> as the note below explains.
@@@ -/

#eval gcd 24 36   -- predict first

-- Note: rfl-based tests do NOT work for gcd.
-- gcd uses well-founded (non-structural) recursion; the kernel cannot reduce it.
-- Neither rfl nor decide can close goals about gcd on concrete values.
-- #eval works because it uses the compiled code path, not the kernel.
-- This distinction matters: rfl-based tests are available only for
-- structurally recursive functions (like factorial above).

-- Specification: gcd divides both arguments.
-- This is a Prop.  The proof is provided for you to read.
def divides (d n : Nat) : Prop := ∃ k, n = d * k

-- Nat.gcd_dvd_left and Nat.gcd_dvd_right are Mathlib lemmas.
-- Our gcd coincides with Nat.gcd (provable, provided here):
theorem gcd_eq_nat_gcd : ∀ a b : Nat, gcd a b = Nat.gcd a b := by
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    cases b with
    | zero =>
      simp only [gcd, Nat.gcd_zero_right]
    | succ b =>
      simp only [gcd]
      have key := ih (a % (b + 1)) (Nat.mod_lt a (Nat.succ_pos b)) (b + 1)
      rw [key, Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]

/-! @@@
## 3.5  The termination / totality distinction

A function in Lean must be *total*: it must return a value for every input.
Lean enforces totality through two mechanisms:

- **Structural recursion**: automatically verified by checking recursive
  calls are on strict subterms.
- **Well-founded recursion**: you provide a termination measure; Lean
  verifies it decreases at each call.

A function that does not terminate cannot be given a type in Lean without
using the `partial` keyword — which removes termination guarantees and
disables proof of properties about the function.

This is not a limitation.  It is a *feature*: if a function has a type
in Lean, it terminates on all inputs.  This means any specification you
write about it is asking a question that always has an answer.

## 3.6  Reading specifications about recursive functions

A specification for a recursive function is almost always a ∀ proposition:
"for all inputs, the output satisfies this condition."

Practice reading these:
@@@ -/

-- "For all n, factorial n is positive"
-- You should be able to read and understand the proposition.
-- The proof term is here for your curiosity; you are not expected to produce it.
theorem factorial_pos : ∀ n : Nat, 0 < factorial n :=
  fun n => Nat.recOn n (Nat.lt_add_one 0) (fun n ih => Nat.mul_pos (Nat.succ_pos n) ih)

/-! @@@
> **Checkpoint — `factorial` is positive.** `factorial_pos` says `0 < factorial n` for
> every `n`.  **Predict** the Boolean below *from that spec* (not by computing `factorial 6`),
> then check.
@@@ -/

#eval decide (0 < factorial 6)   -- predict from factorial_pos

-- "factorial is monotone: each value is no greater than the next"
-- You should be able to read and understand the proposition.
-- The proof term is here for your curiosity; you are not expected to produce it.
theorem factorial_mono : ∀ n : Nat, factorial n ≤ factorial (n + 1) :=
  fun n => Nat.le_mul_of_pos_left (factorial n) (Nat.succ_pos n)

/-! @@@
> **Checkpoint — `factorial` is monotone.** `factorial_mono` says `factorial n ≤
> factorial (n + 1)` for every `n`.  **Predict** the Boolean below *from that spec*, then check.
@@@ -/

#eval decide (factorial 4 ≤ factorial 5)   -- predict from factorial_mono

/- @@@
## Worked out in class
@@@ -/


-- Check out the induction axiom for Nat!
#check (@Nat.rec)

/- @@@
Formatted more nicely:

```lean
@Nat.rec :
  {motive : ℕ → Sort u_1} →
  motive Nat.zero →
  ((n : ℕ) → motive n → motive n.succ) →
  (t : ℕ) → motive t
```
@@@ -/

/- @@@
Problems worked out in class. Define some familar
functions on ordinary data types by induction. Any
recursive function is basically a *universal* built
by applicaiton of the induction axiom for a given
type to answer for base cases and step functions.
@@@ -/

def fac0 := 1
def facStep (n facn : Nat) : Nat := (n+1) * facn
#check @Nat.rec (fun _ => Nat) fac0 facStep
#eval (@Nat.rec (fun _ => Nat) fac0 facStep) 5

/-! @@@
> **Checkpoint — recursion *is* the recursor.** Applying `Nat.rec` to a base value and a
> step function rebuilds `factorial`.  **Predict** the value below (it is `factorial 4`),
> then check.
@@@ -/

#eval (@Nat.rec (fun _ => Nat) fac0 facStep) 4   -- predict first

/- @@@
@List.rec :
  {α : Type u_2} →
  {motive : List α → Sort u_1} →
  motive [] →
  ((head : α) → (tail : List α) → motive tail → motive (head :: tail)) →
  (t : List α) → motive t
@@@ -/

def listLenBase := 0
def stepListLen (_ : String) (_ : List String) (ansL : Nat) := ansL + 1

#check @List.rec String (fun _ => Nat) listLenBase stepListLen
#eval (@List.rec String (fun _ => Nat) listLenBase stepListLen) ["", "", ""]
#check (@List.rec)

/-! @@@
> **Checkpoint — `length` from `List.rec`.** The same universal shape computes list length:
> base `0`, step `+1` per element.  **Predict** the length below, then check.
@@@ -/

#eval (@List.rec String (fun _ => Nat) listLenBase stepListLen) ["a", "b"]   -- predict first


/- @@@
@BinTreeNat.rec :
  {motive : BinTreeNat → Sort u_1} →
  motive BinTreeNat.empty →
  ((n : ℕ) → (l r : BinTreeNat) → motive l → motive r → motive (BinTreeNat.node n l r)) →
  (t : BinTreeNat) → motive t
@@@ -/


inductive BinTreeNat where
| empty
| node (n : Nat) (l r : BinTreeNat)

open BinTreeNat

#check (@BinTreeNat.rec)
#reduce (@BinTreeNat.rec (fun _ => Nat) 0 (fun n _ _ al ar => n + al + ar)) BinTreeNat.empty

def myTree : BinTreeNat :=
  node 1
  (node 2 empty empty)
  (node 5 empty empty)

#reduce (@BinTreeNat.rec (fun _ => Nat) 0 (fun n _ _ al ar => n + al + ar)) myTree

/-! @@@
> **Checkpoint — folding a tree with `BinTreeNat.rec`.** The recursor sums a tree: base
> `0` at `empty`, step `n + al + ar` at each `node`.  **Predict** the sum for `myTree`
> (its node labels are `1`, `2`, `5`), then check.  (A custom recursor has no compiled
> code path, so this checkpoint uses `#reduce` — the kernel reducer — not `#eval`.)
@@@ -/

#reduce (@BinTreeNat.rec (fun _ => Nat) 0 (fun n _ _ al ar => n + al + ar)) myTree   -- predict first

/-! @@@
## Exercises

Each exercise carries a banner — `[id] · competency · tier · level · target` — and,
where it asks you to build something, an **acceptance check**: paste it beneath your
definition in your own file and it must succeed.  `#guard` is silent on success and
errors on failure, so the compiler is your grader.  See `EXERCISE_CONVENTIONS.md` for
the schema.  Do every **core** exercise; **stretch** exercises go deeper and are
optional.

---

**[E3.1]** · *type-directed derivation* · tier 2 · **core** · target `sumTo`

Derive `sumTo : Nat → Nat` computing `0 + 1 + ... + n`.  Produce a **derivation trace**
in the Week 2 §2.6 format — the trace is the graded artifact — then the `def`.
*First-step hint:* the input is a `Nat`, so eliminate on its constructor (`0` vs `n + 1`)
first, exactly as `factorial` does (§3.1); the step clause may use the answer `sumTo n`
already in hand.  Effort: ~4 trace steps, 3 lines of code.

```lean
#guard sumTo 0 = 0
#guard sumTo 1 = 1
#guard sumTo 3 = 6
#guard sumTo 10 = 55
```

---

**[E3.2]** · *specification writing* · tier 1 (+ tier-3 reading) · **core** · target `SumToClosedForm`

State, as a `Prop`, the closed-form specification *"`∀ n, sumTo n = n * (n + 1) / 2`."*
Do **not** prove the general statement (that is a proof by induction, off-limits here).
Instead confirm the spec on instances and on one bounded, decidable slice:

```lean
-- def SumToClosedForm : Prop := ∀ n : Nat, sumTo n = n * (n + 1) / 2
#guard sumTo 5 = 5 * (5 + 1) / 2
#guard sumTo 10 = 10 * (10 + 1) / 2
#guard decide (∀ n ∈ List.range 20, sumTo n = n * (n + 1) / 2) = true
```

In one line: which tier does the *general* `∀ n : Nat` statement live in, and which the
three checks?

---

**[E3.3]** · *counterexample finding* · tier 1 · **core**

A student proposes the closed form *"`sumTo n = n * n / 2`."*  It is **wrong**.  Find
concrete inputs witnessing the mismatch and encode each witness as an **inequality**, so
the check **succeeds** (it confirms the two sides differ):

```lean
#guard sumTo 3 ≠ 3 * 3 / 2
#guard sumTo 5 ≠ 5 * 5 / 2
```

*First-step hint:* evaluate `sumTo 3` and `3 * 3 / 2` by hand and compare.  Then state, in
one line, the *single edit* to the student's formula that makes it correct (compare with
the spec in E3.2).

---

**[E3.4]** · *decidability identification* · tier 1 · **core**

For each claim, say **whether `decide` (equivalently an `rfl`-test) can close it, and why**
— is the function *structural* (kernel-reducible, like `factorial`) or *well-founded*
(only `#eval`/`#guard` reduce it, like `gcd` — §3.4), and is the quantifier *bounded* or
*unbounded*?  The judgment is the point; then check only the ones that are decidable:

(a) `factorial 5 = 120`  (b) `gcd 48 18 = 6`
(c) `∀ n ∈ ([0, 1, 2, 3] : List Nat), sumTo n = n * (n + 1) / 2`  (d) `∀ n : Nat, sumTo n = n * (n + 1) / 2`

```lean
#guard decide (factorial 5 = 120) = true
#guard decide (∀ n ∈ ([0, 1, 2, 3] : List Nat), sumTo n = n * (n + 1) / 2) = true
-- (b) and (d) have no check on purpose: say why decide/rfl cannot close each
--     (hint for (b): §3.4 — gcd is well-founded, so the kernel cannot reduce it;
--      for (d): the domain of n is infinite).
```

---

**[E3.5]** · *specification writing* · tier 1 · **stretch** · target `GcdDividesSpec`

State the specification for `gcd` as **two** `∀` propositions expressing *"`gcd a b`
divides `a`"* and *"`gcd a b` divides `b`."*  Do not prove the general statements; confirm
the divisibility on instances (using the remainder-is-zero form `a % gcd a b = 0`), and —
reusing `gcd_eq_nat_gcd` and Mathlib's `Nat.Coprime` — check that `8` and `15` are coprime:

```lean
#guard 48 % gcd 48 18 = 0
#guard 18 % gcd 48 18 = 0
#guard 100 % gcd 100 75 = 0
#guard Nat.gcd 8 15 = 1        -- Nat.Coprime 8 15 unfolds to this
```

*First-step hint:* `divides d n := ∃ k, n = d * k` (§3.4); the raw `∃ k` is not decidable,
so the checks use the equivalent remainder-is-zero form, which is.  Note that `gcd` is
well-founded — `#guard`/`#eval` reduce it (compiled path), but `rfl`/`decide` cannot.

---

**[E3.6]** · *specification reading* · tier 3 (read-only) · **stretch**

Read the *provided* proof of `factorialAcc_spec` (§3.3):
`∀ n acc, factorialAcc n acc = acc * factorial n`.  In two or three sentences explain
**why the specification is generalized over `acc`** — what breaks in the `succ` step if you
try to prove only the special case `factorialAcc n 1 = factorial n`, without the `∀ acc`?
Then identify which line of the provided proof *applies the inductive hypothesis at a
different accumulator*.  No code to submit.
---

**[E3.7]** · *specification writing + type-directed derivation* · tier 1 · **stretch** · target `sumToAcc`

Define a tail-recursive companion to `sumTo` (E3.1): `sumToAcc : Nat → Nat → Nat`, carrying
the running total in its second argument.  State, as a `Prop`, the relationship between the
two — the accumulator-generalized `∀ n acc, sumToAcc n acc = acc + sumTo n` — and confirm it
on instances.  Do **not** prove the general statement; instead say, in one or two sentences
and reusing the reasoning of E3.6, *why* it must be stated for every `acc` rather than only
for `acc = 0`.

```lean
#guard sumToAcc 0 0 = 0
#guard sumToAcc 4 0 = 10          -- 0 + 1 + 2 + 3 + 4
#guard sumToAcc 4 5 = 15          -- the incoming accumulator is added in
#guard sumToAcc 10 0 = 55
```

*First-step hint:* recurse on the first argument; the accumulator grows on the way *down*,
so the recursive call is the last thing done.  Effort: ~4 lines of code.

@@@ -/

end W03

-- uncomment to see error
-- def collatz : Nat → Nat
--   | 0 => 0
--   | 1 => 1
--   | n => if n % 2 == 0 then collatz (n / 2) else collatz (3 * n + 1)

/- @@@
```lean
fail to show termination for
  collatz
with errors
failed to infer structural recursion:
Cannot use parameter #1:
  failed to eliminate recursive application
    collatz (n / 2)


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n : ℕ
h✝ : (n % 2 == 0) = true
⊢ n / 2 < nLean 4
collatz : ℕ → ℕ
```
@@@ -/
