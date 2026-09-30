-- theorem DM1 : ∀ (P Q : Prop), ¬(P ∧ Q) → ¬P ∨ ¬Q :=
-- fun P Q =>
-- fun h =>
-- Or.inl _ => _
-- Not possible to prove in regular Lean, because



theorem DM2 : ∀ (P Q : Prop), ¬P ∨ ¬Q → ¬(P ∧ Q) :=
fun P _Q => -- ∀ intro (twice)
fun h => -- ∀ intro
fun pandq => -- → intro
let p : P := And.left pandq -- And.elim on left
let q := pandq.right -- And.elim on right
match h with -- Or elim (by cases)
| Or.inl np => np p -- → elim (fn application)
| Or.inr nq => nq q -- → elim (fn application)



/- @@@
Mandatory homework: State and prove the two remaining
variants of DeMorgan's laws, involving distribution of
nation over disjunction (not over or).
@@@ -/

theorem DM3 : ∀ (P Q : Prop), ¬(P ∨ Q) → ¬P ∧ ¬Q :=
fun P Q => -- given some P and some Q
fun h => -- assume ¬(P ∨ Q)
  let np : ¬P := fun p => h (Or.inl p) -- function takes in P and returns False
  -- (Or.inl p) makes a P ∨ Q
  -- then h(P ∨ Q) gives False
  let nq : ¬Q := fun q => h (Or.inr q) -- function takes in Q and returns False
  -- (Or.inr q) makes a P ∨ Q
  -- then h(P ∨ Q) gives False
  And.intro np nq -- construct ¬P ∧ ¬Q


theorem DM4 : ∀ (P Q : Prop), ¬P ∧ ¬Q → ¬(P ∨ Q) :=
fun P Q => -- given some P and some Q
fun h => -- assume ¬P ∧ ¬Q
fun porq => -- → intro
let np : ¬P := And.left h -- And.elim on left
let nq : ¬Q := h.right -- And.elim on right
match porq with -- Or elim (by cases)
| Or.inl p => np p -- I can't have P and ¬P
| Or.inr q => nq q -- I can't have Q and ¬Q
