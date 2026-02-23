#import "@preview/ctheorems:1.1.3": *
#import "@preview/lovelace:0.3.0": *
#import "@preview/glossarium:0.5.8": make-glossary, print-glossary, register-glossary
#import "@preview/curryst:0.5.1"

//This is installed but doesnt seem to do anything :(
//#let font = "Linux Libertine O"
#let font = "Libertinus Serif"
#let font_mono = "JuliaMono"


// math specific text
#let mita(e) = text(font: font, style: "italic")[#e]
#let mkw(e) = text(font: font)[\"] + text(size: 9pt, font: font, weight: "bold")[#e] + text(font: font)[\"]

// Colors used across the template.
#let ctext(x, color) = text(fill: color)[#x]
#let agda_green = rgb("#006C5C")
#let agda_blue = rgb("#003050")
#let lmu_blue = rgb("#0F1987")
#let lmu_cyan = rgb("#009FE3")
#let lmu_orange = rgb("#ff8c00")
#let lmu_green = rgb("#00883A")

// Custom boxes
#let answer = e => block(fill: luma(240), inset: 1em, stroke: (left: 0.25em), breakable: true)[#e]
#let black_box = e => box(stroke: black, inset: 1em, width: 100%)[#e]
#let sblock(x) = block(fill: luma(240), inset: 10pt, radius: 3pt, width: 100%)[#x]
#let bx(col) = box(fill: col, width: 1em, height: 1em)

// Custom table cells
#let table_green = table.cell(fill: green.lighten(60%))[]
#let table_red = table.cell(fill: red.lighten(60%))[]
#let table_aqua = table.cell(fill: aqua.lighten(60%))[]
#let table_greentext(txt) = table.cell(fill: green.lighten(60%))[#txt]

#let pseudocode(..e) = pseudocode-list(booktabs: true, booktabs-stroke: 1pt + black, hooks: .5em, ..e)

// ctheorems
#let theorem = thmbox(
  "theorem", "Theorem", fill: rgb("#eeffee"), inset: 10pt, breakable: true
)
#let definition = thmbox(
  "definition", "Definition", inset: (top: 0em), breakable: true
)
#let example = thmplain("example", "Example", inset: (top: 0em), breakable: true)
#let proof = thmproof("proof", "Proof", inset: (top: 0em), breakable: true)
#let question = thmbox(
  "question", "Question", fill: rgb("#eeffee"), inset: 10pt, breakable: true, base_level: 0
)

// curryst
#let inf-rule = curryst.rule
#let proof-tree = curryst.prooftree

#let titlepage(
  title: "",
  author: "",
  email: "",
  matriculation: "",
  thesis-type: "",
  advisor: "",
  supervisor: "",
  submission_date: "",
  paper-size: "",
) = {
  set page(numbering: none)
  set align(center)
  // Institution
  text(14pt, smallcaps("LUDWIG-MAXIMILIANS-UNIVERSITÄT MÜNCHEN"))
  linebreak()
  linebreak()
  text(14pt,smallcaps("CHAIR OF THEORETICAL COMPUTER SCIENCE AND THEOREM PROVING"))
  v(7%)
  image("lmu-sigillium.svg", width: 35%)

  // Title
  v(11%)
  text(21pt, weight: 500, title)
  v(2%)
  text(14pt)[#author]
  v(2%)
  text(17pt)[#thesis-type]
  linebreak()
  text(14pt)[in Computer Science plus Computer Linguistics]
  v(8%)
  text(14pt)[Supervisor: #supervisor]
  v(0.8%)
  text(14pt)[Advisor: #advisor]
  v(0.8%)
  text(14pt)[Submission date: #submission_date]
}

#let disclaimer_page(author: str, submission_date: str) = {
  set page(numbering: none)
  align(center)[
    #v(1fr)
    Disclaimer
  ]
  [Ich erkläre hiermit, dass ich die vorliegende Arbeit selbstständig und nur mit den angegebenen Hilfsmitteln verfasst habe. Alle Passagen, die ich aus einer Literatur oder anderen Quellen übernommen habe, sind eindeutig als Zitate mit Quellenangabe gekennzeichnet.
Diese gedruckte Fassung ist ein Ausdruck der eingereichten elektronischen Fassung.

I hereby declare that I have written this work independently and only with the aids specified. All passages that I have taken from literature or other sources have been clearly marked as quotations with reference to the source.
This printed copy is a printout of the submitted electronic copy.

]
  v(10mm)
  grid(
    columns: (250pt, 250pt),
    [
      //TODO: is there a signature required?
      //#line(length: 60%)
      //Munich, Date
      Munich, #submission_date
    ],
    [
      //#line(length: 60%)
      //Author
      #author
    ]
  )
  pagebreak()

}

#let acknowledgement_page(acknowledgement: "") = {
  if acknowledgement != "" [
    #set page(numbering: none)
    #align(center)[
      #heading(
        outlined: false,
        numbering: none,
        text(0.85em, smallcaps[Acknowledgements]),
      )
    ]
    #acknowledgement
    #counter(page).update(1)
    #pagebreak()
  ]
}

#let abstract_page(abstract: "") = {
  if abstract != "" [
    //#set page(numbering: "I", number-align: center)
    #set page(numbering: none)
    #align(center)[
      #heading(
        outlined: false,
        numbering: none,
        text(0.85em, smallcaps[Abstract]),
      )
    ]
    #abstract
    #counter(page).update(1)
    #pagebreak()
  ]
}

#let official(
  title: "",
  author: "Daniel Soukup",
  email: "D.Soukup@campus.lmu.de",
  matriculation: "",
  thesis-type: "",
  supervisor: "",
  advisor: "",
  submission_date: "",
  glossary: (),
  abstract: "",
  acknowledgement: "",
  paper-size: "a4",
  lang: "en",
  body
) = {
  set document(title: title, author: author)
  set text(font: font, size: 12pt, lang: lang)
  set page(
    paper: paper-size,
    // eh, not even needed
    //header: [
    //  #smallcaps("TODO")  #h(1fr) #smallcaps(author)  #h(1fr) #smallcaps("TODO")
    //  #line(length: 100%)
    //],
    // margin: (left: 20mm, right: 20mm, top: 15mm, bottom: 20mm),
  )
  set par(leading: 0.75em, justify: true, spacing: 1.2em)
  set heading(numbering: "1.")
  show heading: set block(below: 12pt)
  set list(indent: 1em, spacing: 10pt, tight: false)
  set enum(numbering: "1.", indent: 1em, spacing: 10pt, tight: false)

  show link: set text(fill: blue.darken(60%))
  show raw: set text(font: font_mono, size: 10pt, features: (calt: 0))
  show outline.entry.where(level: 1): it => {
    v(12pt, weak: true)
    strong(it)
  }
  // Break large tables across pages.
  show figure.where(kind: table): set block(breakable: true)
  // Use smallcaps for table header row.
  //show table.cell.where(y: 0): smallcaps
  set table(
    inset: 7pt, // default is 5pt
    stroke: (0.5pt + luma(100))
  )
  show raw.where(lang: "lean"): r => {
  show "theorem": set text(purple)
  show "sorry": set text(maroon)
  show "lemma": set text(purple)
  show "by": set text(olive)
  show "Type": set text(black)
  show "have": set text(olive)
  show "exact": set text(olive)
  show "simpa": set text(olive)
  show "using": set text(olive)
  show "let": set text(olive)
  show "apply": set text(olive)
  show "rw": set text(olive)
  show "aesop": set text(olive)
  show "{": set text(gray)
  show "}": set text(gray)
  show "(": set text(gray)
  show ")": set text(gray)
  show "[": set text(gray)
  show "]": set text(gray)
  show "def": set text(purple)
  show "@": set text(maroon)
  show "to_additive": set text(maroon)
  show "noncomputable": set text(purple)
  show "by_contra": set text(olive)
  show "obtain": set text(olive)
  show "infer_instance": set text(maroon)
  show "rcases": set text(olive)
  show "contradiction": set text(olive)
  show "inferInstance": set text(maroon)
  show "use": set text(olive)
  show "constructor": set text(olive)
  show "rfl": set text(olive)
  show "this": set text(black)
  show "⟨": set text(gray)
  show "⟩": set text(gray)
  r
}
  show: thmrules
  show: make-glossary
  register-glossary(glossary)

  titlepage(
    title: title,
    author: author,
    email: email,
    matriculation: matriculation,
    thesis-type: thesis-type,
    supervisor: supervisor,
    advisor: advisor,
    submission_date: submission_date,
    paper-size: paper-size
  )
  disclaimer_page(author: author, submission_date: submission_date)
  acknowledgement_page(acknowledgement: acknowledgement)
  abstract_page(abstract: abstract)

  outline(depth: 3, indent: auto)
  // Is this needed?
  //outline(
  //  title: [List of Figures],
  //  target: figure.where(kind: image),
  //)
  pagebreak(weak: true)
  // Main Matter
  counter(page).update(1)
  body

  pagebreak(weak: true)
  bibliography("literature.bib", title: [References])
  pagebreak(weak: true)

  //set heading(numbering: "A.1")
  //counter(heading).update(0)
  //heading("Appendix", level: 1)
  //heading("Glossary", level: 2)
  //print-glossary(glossary)
}

