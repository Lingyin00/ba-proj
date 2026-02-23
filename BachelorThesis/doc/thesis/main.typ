#import "template.typ":*
#let target_date = datetime(year: 2026, month: 2, day: 23)
#show : official.with(
  title: [
    Extending the Group Theory Library in Mathlib
  ],
  author: "Lingyin Luo",
  email: "Luo.Lingyin@campus.lmu.de",
  matriculation: [TODO],
  thesis-type: [Bachelor's Thesis],
  advisor: [Xavier Généreux],
  supervisor: [Prof. Dr. Jasmin Blanchette],
  submission_date: target_date.display("[month repr:long] [day], [year]"),
  glossary: (
    (key: "DTT", short: "DTT", long: "dependent type theory"),
  ),
  abstract: [
This thesis investigates the formalization of classic group-theoretic arguments in the proof assistant Lean, with a focus on the interaction between mathematical structures and library design in Mathlib. Two case studies have been developed: a theorem characterizing abelian simple groups and two theorems concerning Hall subgroups and the coprimality under intersection, product and quotient by normal subgroups. 

The first case study led to a contribution to Mathlib, including a refinement of an existing lemma and a generalization motivated by the review process. This experience illustrates how formal developments evolve from problem-driven proofs toward structurally reusable library components.
 
The second case study analyses the formal reconstruction of textbook proofs of the Hall subgroup theorems under the type theoretic setting. While the underlying mathematics relies only on elementary index computations and isomorphism theorems, the formalization requires careful coordination of several APIs and careful treatments on type correctness. In particular, the Hall condition is treated as a coprimality invariant transported along explicit chains of divisibility relations, highlighting how structural and numerical reasoning must be carefully integrated in formal proof development.

  ],
  acknowledgement: [I would like to thank Prof. Dr. Jasmin Blanchette for his excellent teaching, through which I was introduced to the field of interactive theorem proving.

I would like to thank my advisor Xavier Généreux for his generous support in  many aspects of this project; for his great patience and warm encouragement even when I was a complete beginner; and for his trust in me, which allowed me the freedom to explore the scope of this project according to my own interests.

I would like to thank my fellow students Henrik Böving, Xingyu Long and Daniel Soukup for their support in my bachelor studies. I also thank Henrik for answering many Lean questions from me, for reading the earliest draft of this thesis and giving valuable suggestions.

Deep thanks to my parents for their unconditional love, and to my good friends Baoyi, Hongbo, Linjing,  Marie, Mona, Ni Nan, and Ziqing, for simply being around.

Special thanks to my high school teachers Ms. Liu and Mr. Mellish, whose inspiration has stayed with me over the years; to Daniel Tanzer and the Faction Ski community, for teaching me to approach challenges with creativity and independence.
  ],
)  

#include("sections/01-introduction.typ")
#include("sections/02-background.typ")
#include("sections/03-implementation.typ")
#include("sections/04-evaluation.typ")
#include("sections/07-Discussion.typ")
#include("sections/05-related-work.typ")
#include("sections/06-conclusion.typ")

