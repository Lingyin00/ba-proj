#import "template.typ":*
#let target_date = datetime(year: 2026, month: 2, day: 24)
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
TODO
  ],
  acknowledgement: [
TODO
  ],
)  

#include("sections/01-introduction.typ")
#include("sections/07-math.typ")
#include("sections/02-background.typ")
#include("sections/03-implementation.typ")
#include("sections/04-evaluation.typ")
#include("sections/05-related-work.typ")
#include("sections/06-conclusion.typ")
  
