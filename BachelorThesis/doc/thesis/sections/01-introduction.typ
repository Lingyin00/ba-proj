= Introduction (2 pages)

In recent years, the formalization of mathematical proofs has become an increasingly important topic in both mathematics and computer science (*citation*).
(*Examples to be added.*)

Formalizing mathematics refers to the process of writing machine-checkable proofs in a proof assistant such as Lean, Rocq, or Isabelle (*citation*). At first glance, this process may appear to be a straightforward translation from pen-and-paper proofs into a formal language. In practice, however, formalization is significantly more involved. It often reveals many hidden steps that are typically carried out implicitly in a mathematician’s head when reasoning informally (*citation*). As a result, even seemingly trivial tasks—such as formulating correct definitions or theorem statements—can require substantial effort (*citation*). More subtly, higher-level decisions, such as choosing an appropriate proof schema, often turn out to be even more demanding (*citation*).

Group theory, which studies algebraic structures encoding symmetry, is typically the first major topic encountered by undergraduate students when learning abstract algebra. Many subsequent areas including ring theory and commutative algebra, are built upon concepts from group theory. Given its fundamental role in mathematics, the formalization of group theory requires particularly careful treatment.

For these reasons, group theory is chosen as the primary subject of investigation in this formalization project. The work is carried out using the proof assistant Lean together with its mathlib library (*citation*). As the group theory component of mathlib is among its most mature parts, it provides a suitable foundation for formalization. 

During the process of formalizing group-theoretic theorems on top of mathlib, several interesting observations arise. In some cases, the structure of formal proofs closely aligns with standard pen-and-paper arguments found in the literature. In other cases, however, formalization exposes a tension between informal proofs and their formal counterparts. Moreover, many assumptions that remain implicit in informal reasoning must be made explicit in the formal setting, and the act of formalization itself reshapes one’s understanding of the underlying mathematical content.

Following the narrative of Chapter 3, Quotient Groups and Homomorphisms, from Abstract Algebra by Dummit and Foote (*citation*), this project formalizes two selected exercises. The first concerns _abelian simple groups_, and the second concerns _Hall Subgroups_. These examples are chosen to concretely illustrate the phenomena discussed above. In addition, the project includes a case study of contributing a pull request to mathlib and reflects on the role that proof assistants can play in the learning and formalization of undergraduate mathematics.



