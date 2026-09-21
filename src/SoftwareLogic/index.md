<div style="text-align: center; margin: 0.6rem 0 1.8rem;">
  <div style="font-size: 2.8em; font-weight: 700; line-height: 1.05;">Software Logic</div>
  <div style="font-size: 1.22em; font-weight: 500; line-height: 1.12; margin-top: 0.38em;">Intellectual Control, Assurance, and Accountability</div>
  <div style="font-size: 1.22em; font-weight: 500; line-height: 1.12; margin-top: 0.04em;">in the Era of Agentic Software Engineering and Autoformalized Mathematics</div>
  <div style="font-size: 1.05em; font-weight: 500; line-height: 1.2; margin-top: 0.9em;">Kevin Sullivan</div>
  <div style="font-size: 0.95em; font-weight: 400; line-height: 1.2; margin-top: 0.15em;">CS6501-010 Fall 2026</div>
</div>

- **Instructor:** Kevin Sullivan · <sullivan@virginia.edu>
- **Department:** Computer Science, University of Virginia
- **Meetings:** Mondays & Wednesdays, 11:00 AM – 12:15 PM · Rice 508 — 28 sessions
- **Office hours:** Tuesdays, 1:00 – 3:00 PM · Rice 508
- **Course book (living):** <https://kevinsullivan.github.io/Lean4CS1> · source: <https://github.com/kevinsullivan/Lean4CS1>

> This syllabus is subject to change. Any such changes will be pre-announced and documented
> here.

---

## About This Course

Software development is being transformed by AI in at least two big ways. First, AI is
automating the production of a great deal of imperative code. Second, combined with the
breakout success of proof assistants for formalization of abstract mathematical statements
and proofs, AI promises far greater practicality and utility of formal specification and
proof construction in routine industrial software production.

As of Fall 2026 there is exploding interest in the use of Lean for both formal mathematics and
formal software specification and verification. A snapshot of where that stood at the start of
this semester is in the appendix, [Lean 4 beyond research](../lean4-industry.md).

However big challenges remain. Even with formal and machine-checked specifications, the
rate at which generative AIs can produce specifications and proofs, now mixed together
with ordinary programming types and functions and effects, means that one's constructions
can easily escape one's intellectual control, even when it's all formalized and proven.

The problem with loss of intellectual control is that it's antithetical to good faith acceptance of
accountability for harmful failures that were, or could and should have been, foreseen and averted.
The social equation is you-are-accountable implies you-are-less-likely-to-fail implies
I-can-trust-you-more and act accordingly. That trust is what a user pays for: assurances that the
product is fit for use in all agreed respects, and the freedom to ignore the complexity behind them
because someone else has taken care of it. The same reasoning underpins a legal system in which
real people are punished. (At least that's the theory.) And trust of that kind is crucial to the
success of a system and of the society around it.

This course will emphasize the development of formal specification architectures as a
vital practice for both guiding generative AIs to produce useful results and to maintain
the intellectual control necessary for human beings to be held accountable for the harmful
failures their systems produce.

Durable intellectual control depends on abstract software specification and proofs rooted in the
generalized mathematics of the application domain, stating that theory precisely, and certifying
separate computable implementations against it. It is also required for the sustained quality of
evolving, long-lived software systems.

What formal methods give the developer is justified confidence that they can actually uphold the
assurances their users are paying for and then relying upon. That confidence rests on two distinct
objects of trust: the validity of the statements of the formal theory itself and verification of
the proof certificates that connect implementation to the abstract theories they are required to
implement in some form. Lean 4 provides a practical language in which theories, implementations,
and proofs can coexist, but it does not eliminate either obligation: one must understand the
mathematics being formalized, and one must understand the trusted proof-checking base on which that
confidence depends.

This is a course for graduate students in computer science. The course has two main threads:
learning to think and express concepts formally in Lean 4, and learning deep and abiding principles
of intellectual control over software through readings of seminal papers leading up to the present
moment.

## Mathematical Thread: Two Parts

The mathematical thread in this course is in two parts.

- **Part I — Certified Computation (the FP book).** A functional-programming foundation, taught
  through the Curry–Howard correspondence, in which specifications are types. Students learn to read
  and write specifications as types, to derive terms that inhabit them, and to check their claims
  with the compiler. Part I does not assess proof construction. The proofs it contains are provided
  for students to read.
- **Part II — Proof Construction.** Part II builds on the Part I foundations and asks students to
  produce proofs of their own. The objects of study carry over (data, specifications, recursion,
  higher-order functions, sets, relations, type classes), reoriented from `Type` to `Prop`. Part II
  follows the discipline general theory → separate computable realization → certified bridge, and
  works toward the endpoint the semester is designed around: institutions and the satisfaction
  condition.

Lean is used from Week 1 onward. Part II changes the kind of work students do in Lean; it does not
introduce Lean.

## Schedule (Fall 2026 · Mondays & Wednesdays)

Two tracks run in parallel and are scheduled independently. **Paper readings** (Line I) keep
their weekly cadence: one theme per paper-week, with full bibliographic references and PDF links
given in each paper cell. A set is due at the session where it is listed and, where a `↳ (cont.)`
cell appears, carries into that week's second session. The exception is **Week 2**, which carries
two sets: **set 1 due Wed Sep 2** and **set 2 due Mon Sep 7**. The **Part I book track**
is compressed to **two chapters per class session** (one each on Wed Sep 16 and Mon Sep 28), run in order, beginning
**Wed Sep 2**; once
the book is complete (Mon Sep 28) the class proceeds to **Part II** (Lean programming and proof
construction). Class does not meet Mon Oct 5 (fall reading days) or Wed Nov 25 (Thanksgiving);
Labor Day (Mon Sep 7) meets. 28 sessions total.

| # | Date | Paper readings (Line I — by week) | Part I book (2 ch/session, starts Sep 2) → Part II |
|---:|---|---|---|
| | **▸ Week 1** · course intro & Lean setup | *Aug 26 + Aug 31* | |
| 1 | Wed Aug 26 | *course intro — no paper reading due* | *course intro · Lean/Mathlib setup — no chapter due* |
| 2 | Mon Aug 31 | *intro — no paper reading due (Paper set 1 due Wed Sep 2 ▸)* | *course intro · Lean/Mathlib setup — no chapter due* |
| | **▸ Week 2** · Part I book · 2 ch/session | *Sep 02 + Sep 07* | |
| 3 | Wed Sep 02 | **Paper set 1 — Wk 1: Software as Intellectual Instrument.**<br>— Brooks, [“The Computer ‘Scientist’ as Toolsmith”](https://andymatuschak.org/files/papers/Brooks%20-%201977%20-%20The%20computer%20scientist%20as%20toolsmith.pdf), *Information Processing 77*, 1977, pp. 625–634.<br>— Hutchins, Hollan & Norman, [“Direct Manipulation Interfaces”](https://hci.ucsd.edu/hollan/direct-manip.pdf), *Human–Computer Interaction* 1(4), 1985, pp. 311–338. | Algebraic Types — Computation & Logic · Expressions, Types, Values |
| 4 | Mon Sep 07 · Labor Day (meets) | **Paper set 2 — Wk 2: Program Understanding.**<br>— Simon, [“The Architecture of Complexity”](https://www2.econ.iastate.edu/tesfatsi/ArchitectureOfComplexity.HSimon1962.pdf), *Proc. Am. Philosophical Society* 106(6), 1962, pp. 467–482.<br>— Letovsky, “Cognitive Processes in Program Comprehension,” *J. Systems and Software* 7(4), 1987, pp. 325–339, [doi:10.1016/0164-1212(87)90032-X](https://doi.org/10.1016/0164-1212%2887%2990032-X) — subscription; UVA Library.<br>— Brooks, [“No Silver Bullet”](https://www.cs.unc.edu/techreports/86-020.pdf), UNC TR86-020, 1986 (also *Computer* 20(4), 1987, pp. 10–19). | Functions & Specifications · Recursion & Termination |
| | **▸ Week 3** · Part I book · 2 ch/session | *Sep 09 + Sep 14* | |
| 5 | Wed Sep 09 | **Wk 3: Conceptual Design.**<br>— Jackson, [“Towards a Theory of Conceptual Design for Software”](https://groups.csail.mit.edu/sdg/pubs/2015/concept-essay.pdf), *Onward! 2015*, pp. 282–296.<br>— Perez De Rosso & Jackson, [“Purposes, Concepts, Misfits, and a Redesign of Git”](https://groups.csail.mit.edu/sdg/pubs/2016/gitless-oopsla16.pdf), *OOPSLA 2016*, pp. 292–310. | Algebraic Datatypes · Lists |
| 6 | Mon Sep 14 | ↳ *(wk 3 — cont.)* | Trees & BST Invariants · Polymorphism & Decidability |
| | **▸ Week 4** · Part I book · 2 ch/session | *Sep 16 + Sep 21* | |
| 7 | Wed Sep 16 | **Wk 4: Modularity & Software Architecture.**<br>— Parnas, [“On the Criteria To Be Used in Decomposing Systems into Modules”](https://dl.acm.org/doi/pdf/10.1145/361598.361623), *CACM* 15(12), 1972, pp. 1053–1058.<br>— Perry & Wolf, [“Foundations for the Study of Software Architecture”](https://users.ece.utexas.edu/~perry/work/papers/swa-sen.pdf), *ACM SIGSOFT SEN* 17(4), 1992, pp. 40–52.<br>— Garlan & Shaw, [“An Introduction to Software Architecture”](https://www.cs.cmu.edu/afs/cs/project/able/ftp/intro_softarch/intro_softarch.pdf), 1993, pp. 1–39. | Higher-Order Functions |
| 8 | Mon Sep 21 | ↳ *(wk 4 — cont.)* | Specifications in Practice · Sets & Relations |
| | **▸ Week 5** · Part I book · 2 ch/session — **book completes** | *Sep 23 + Sep 28* | |
| 9 | Wed Sep 23 | **Wk 5: Specification & the Architecture of Claims.**<br>— Hoare, [“An Axiomatic Basis for Computer Programming”](https://www.cs.cmu.edu/~crary/819-f09/Hoare69.pdf), *CACM* 12(10), 1969, pp. 576–580, 583.<br>— Dijkstra, [“Guarded Commands, Nondeterminacy and Formal Derivation of Programs”](https://www.cs.utexas.edu/~EWD/ewd04xx/EWD472.PDF), *CACM* 18(8), 1975, pp. 453–457. | Abstract Types · Type Classes & Decidability |
| 10 | Mon Sep 28 | ↳ *(wk 5 — cont.)* | Curry–Howard ← **Part I book complete** |
| | **▸ Week 6** · Part II · Lean prog. & proof — *tentative* — **begins** | *Sep 30 + Oct 07* · (reading-day break between sessions) | |
| 11 | Wed Sep 30 | **Wk 6: Abstraction, Types & Intellectual Compression.**<br>— Liskov & Zilles, [“Programming with Abstract Data Types”](https://gleitzman.com/media/docs/adt-liskov.pdf), 1974, pp. 50–59.<br>— Reynolds, [“Types, Abstraction and Parametric Polymorphism”](https://home.ttic.edu/~dreyer/course/papers/reynolds.pdf), *Information Processing 83*, pp. 513–523.<br>— Wadler, [“Propositions as Types”](https://www.pure.ed.ac.uk/ws/portalfiles/portal/20001186/propositions_as_types.pdf), *CACM* 58(12), 2015, pp. 75–84. | ⟶ **Part II begins** (all Part II topics tentative) ‡ · **Relations** — abstract theory `A→B→Prop`: id, converse, composition, orders |
| 12 | Wed Oct 07 · post-reading-day | ↳ *(wk 6 — cont.)* | ‡ Relations — computable: finite relations as pair-lists; decidable membership |
| | **▸ Week 7** · Part II · Lean prog. & proof — *tentative* | *Oct 12 + Oct 14* | |
| 13 | Mon Oct 12 | **Wk 7: Semantics: Making Meaning Explicit.**<br>— Plotkin, [“A Structural Approach to Operational Semantics”](https://homepages.inf.ed.ac.uk/gdp/publications/sos_jlap.pdf), *JLAP* 60–61, 2004, pp. 17–139.<br>— Goguen & Burstall, [“Institutions: Abstract Model Theory for Specification and Programming”](https://dl.acm.org/doi/pdf/10.1145/147508.147524), *JACM* 39(1), 1992, pp. 95–146. | ‡ Relations — **bridge**: executable ops agree extensionally with abstract theory |
| 14 | Wed Oct 14 | ↳ *(wk 7 — cont.)* | ‡ **Transition systems** — transition relations; reflexive/transitive closure |
| | **▸ Week 8** · Part II · Lean prog. & proof — *tentative* | *Oct 19 + Oct 21* | |
| 15 | Mon Oct 19 | **Wk 8: Formal Proof as an Intellectual Tool.**<br>— Leroy, [“Formal Verification of a Realistic Compiler”](https://xavierleroy.org/publi/compcert-CACM.pdf), *CACM* 52(7), 2009, pp. 107–115.<br>— Trusted-base limitation: Lean 4.32.2 kernel soundness fix — [release notes](https://lean-lang.org/doc/reference/latest/releases/v4.32.2/), [issue #14576](https://github.com/leanprover/lean4/issues/14576). | ‡ Transition systems — computable: finite-state graph + reachability search |
| 16 | Wed Oct 21 | ↳ *(wk 8 — cont.)* | ‡ Transition systems — **bridge**: computed reachability iff abstract; invariant soundness |
| | **▸ Week 9** · Part II · Lean prog. & proof — *tentative* | *Oct 26 + Oct 28* | |
| 17 | Mon Oct 26 | **Wk 9: Construction by Meaning-Preserving Transformation.**<br>— Meertens, [“Algorithmics—Towards Programming as a Mathematical Activity”](https://www.kestrel.edu/people/meertens/publications/papers/Algorithmics.pdf), 1986, pp. 289–334.<br>— Backus, [“Can Programming Be Liberated from the von Neumann Style?”](https://dl.acm.org/doi/pdf/10.1145/359576.359579), *CACM* 21(8), 1978, pp. 613–641. | ‡ **Relational algebra** — extensional operators + laws |
| 18 | Wed Oct 28 | ↳ *(wk 9 — cont.)* | ‡ Relational algebra — computable: finite tables; select/project/join/union/diff/rename |
| | **▸ Week 10** · Part II · Lean prog. & proof — *tentative* | *Nov 02 + Nov 04* | |
| 19 | Mon Nov 02 | **Wk 10: Behavior, State, Time & Invariants.**<br>— Clarke, Emerson & Sistla, [“Automatic Verification of Finite-State Concurrent Systems…”](https://dl.acm.org/doi/pdf/10.1145/5397.5399), *TOPLAS* 8(2), 1986, pp. 244–263.<br>— Lamport, [“Time, Clocks, and the Ordering of Events in a Distributed System”](https://www.cs.cornell.edu/courses/cs614/2002sp/Clocks.Lamport.1.pdf), *CACM* 21(7), 1978, pp. 558–565. | ‡ Relational algebra — **bridge**: each operator denotes its abstract counterpart |
| 20 | Wed Nov 04 | ↳ *(wk 10 — cont.)* | ‡ **Inductive relational algebra** — query syntax + compositional denotation |
| | **▸ Week 11** · Part II · Lean prog. & proof — *tentative* | *Nov 09 + Nov 11* | |
| 21 | Mon Nov 09 | **Wk 11: Representation, Refinement & Substitutability.**<br>— Hoare, “Proof of Correctness of Data Representations,” *Acta Informatica* 1(4), 1972, pp. 271–281, [doi:10.1007/BF00289507](https://doi.org/10.1007/BF00289507) — subscription; UVA Library.<br>— Liskov & Wing, [“A Behavioral Notion of Subtyping”](https://www.cs.cmu.edu/~wing/publications/LiskovWing94.pdf), *TOPLAS* 16(6), 1994, pp. 1811–1841. | ‡ Inductive rel. algebra — computable: evaluator/compiler over finite relations |
| 22 | Wed Nov 11 | ↳ *(wk 11 — cont.)* | ‡ Inductive rel. algebra — **bridge**: evaluation preserves denotation (structural) |
| | **▸ Week 12** · Part II · Lean prog. & proof — *tentative* | *Nov 16 + Nov 18* | |
| 23 | Mon Nov 16 | **Wk 12: Evidence, Autoformalization & the Economics of Proof.**<br>— Claessen & Hughes, [“QuickCheck: A Lightweight Tool for Random Testing of Haskell Programs”](http://www.eecs.northwestern.edu/~robby/courses/395-495-2009-fall/quick.pdf), *ICFP 2000*, pp. 268–279.<br>— Wu et al., [“Autoformalization with Large Language Models”](https://papers.nips.cc/paper_files/paper/2022/file/d0c6bc641a56bebee9d985b937307367-Paper-Conference.pdf), *NeurIPS 2022*. | ‡ **Categories** — objects, morphisms, identity, composition, functoriality |
| 24 | Wed Nov 18 | ↳ *(wk 12 — cont.)* | ‡ Signatures, sentences, models, interpretations, satisfaction |
| | **▸ Week 13** · Part II · Lean prog. & proof — *tentative* | *Nov 23 + Nov 30* · (Thanksgiving break between sessions) | |
| 25 | Mon Nov 23 | **Wk 13: Trust & Machine-Generated Verified Construction.**<br>— Necula, [“Proof-Carrying Code”](https://dl.acm.org/doi/pdf/10.1145/263699.263712), *POPL 1997*, pp. 106–119.<br>— Thompson, [“Reflections on Trusting Trust”](https://web.mit.edu/6.857/OldStuff/Fall03/ref/Thompson-ReflectionsOnTrustingTrust.pdf), *CACM* 27(8), 1984, pp. 761–763.<br>— Saltzer, Reed & Clark, [“End-to-End Arguments in System Design”](https://www.cs.cmu.edu/afs/cs.cmu.edu/academic/class/15712-s12/www/papers/saltzer84.pdf), *TOCS* 2(4), 1984, pp. 277–288.<br>— Aggarwal, Parno & Welleck, [“AlphaVerus: Bootstrapping Formally Verified Code Generation…”](https://proceedings.mlr.press/v267/aggarwal25a.html), *ICML 2025*, pp. 587–615. | ‡ Concrete categories/finite models; executable satisfaction; **bridge** (functor laws; exec ⟺ abstract) |
| 26 | Mon Nov 30 · post-Thanksgiving | ↳ *(wk 13 — cont.)* | ‡ **Institutions** — signature category; sentence & model functors; indexed satisfaction |
| | **▸ Week 14** · Part II · Lean prog. & proof — *tentative* | *Dec 02 + Dec 07* | |
| 27 | Wed Dec 02 | **Wk 14: Understanding Change, Evolution & Accountability.**<br>— Sillito, Murphy & De Volder, [“Questions Programmers Ask During Software Evolution Tasks”](https://citeseerx.ist.psu.edu/document?doi=3dda5d9a5e4eb27760e8a4a381a1057ce0ba7d65&repid=rep1&type=pdf), *FSE 2006*, pp. 23–34.<br>— Lehman, [“Programs, Life Cycles, and Laws of Software Evolution”](https://users.ece.utexas.edu/~perry/education/SE-Intro/lehman.pdf), *Proc. IEEE* 68(9), 1980, pp. 1060–1076.<br>— Parnas, [“Software Aging”](https://plg.uwaterloo.ca/~migod/846/papers/parnas-SwAging.pdf), *ICSE 1994*, pp. 279–287. | ‡ Institutions — package the semester's machinery as a concrete executable institution; **satisfaction condition** |
| 28 | Mon Dec 07 · last class | ↳ *(wk 14 — cont.)* | ‡ **Endpoint** — prove the satisfaction condition; project synthesis & recoverability |

‡ **Part II topics (sessions 11–28) are tentative.** The per-topic pacing (≈3 sessions each) is
provisional. Part II keeps the discipline general theory → separate computable realization →
certified bridge.

---

## Grading

Course grades will be based on two components, weighted equally.

| Component | Weight |
|---|---|
| Participation | 50% |
| Two to three projects — details TBD | 50% |

Participation means demonstrated preparation for and participation in class, including attendance
and active participation in discussions. You have two “just out” days for the semester: two class
meetings you may miss for any reason, with no explanation needed and no cost to your grade. Beyond
those, habitual absences or inattention will result in losses against full credit, assessed
periodically by the instructor. If you have special circumstances, talk with the instructor to reach
a common understanding.

The competencies above describe what the work is assessed against. Weekly exercise sets are
machine-checked for immediate feedback and count as preparation for class.

---

## Course Materials in This Book

The Part I book track above draws on the [CS1 Full Course](../FPCourse/T01_ExpressionsFunctionsRecursion/W00_AlgebraicTypes.md)
chapters listed here. Part II builds new theory on top of these chapters. It introduces no further
book chapters.

**Unit 1 — Expressions, Functions, Recursion**

- [Week 0: Algebraic Types — Computation and Logic](../FPCourse/T01_ExpressionsFunctionsRecursion/W00_AlgebraicTypes.md)
- [Week 1: Expressions, Types, and Values](../FPCourse/T01_ExpressionsFunctionsRecursion/W01_ExpressionsTypesValues.md)
- [Week 2: Functions and Specifications](../FPCourse/T01_ExpressionsFunctionsRecursion/W02_FunctionsSpecifications.md)
- [Week 3: Recursion and Termination](../FPCourse/T01_ExpressionsFunctionsRecursion/W03_RecursionTermination.md)

**Unit 2 — Algebraic Datatypes, Lists, Trees, Decidability**

- [Week 4: Algebraic Datatypes](../FPCourse/T02_InductiveTypes/W04_AlgebraicDatatypes.md)
- [Week 5: Lists](../FPCourse/T02_InductiveTypes/W05_Lists.md)
- [Week 6: Trees and BST Invariants](../FPCourse/T02_InductiveTypes/W06_Trees.md)
- [Week 7: Polymorphism and Decidability](../FPCourse/T02_InductiveTypes/W07_PolymorphismDecidability.md)

**Unit 3 — Higher-Order Functions, Specifications**

- [Week 8: Higher-Order Functions](../FPCourse/T03_HigherOrderAndSpecification/W08_HigherOrderFunctions.md)
- [Week 9: Specifications in Practice](../FPCourse/T03_HigherOrderAndSpecification/W09_Specifications.md)

**Unit 4 — Sets and Relations**

- [Week 10: Sets and Relations](../FPCourse/T04_SetsAndRelations/W10_SetsRelations.md)

**Unit 5 — Abstract Types, Type Classes**

- [Week 11: Abstract Types](../FPCourse/T05_AbstractTypesAndTypeClasses/W11_AbstractTypes.md)
- [Week 12: Type Classes and Decidability](../FPCourse/T05_AbstractTypesAndTypeClasses/W12_TypeClassesDecidable.md)

**Unit 6 — Curry-Howard**

- [Week 14: The Curry-Howard Correspondence](../FPCourse/T06_StreamsAndCurryHoward/W14_CurryHoward.md)

