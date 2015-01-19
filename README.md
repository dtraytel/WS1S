This repository contains an Isabelle formalization of a decision procedure for
WS1S presented in the paper draft

  A Coalgebraic Decision Procedure for WS1S
  
by Dmitriy Traytel.

The formalization has been processed with Isabelle2014 which is available here:

    http://isabelle.in.tum.de/website-Isabelle2014

The formalization can be browsed in both pdf (formalization.pdf) and html
(MSO_Derivatives/index.html) formats. Additionaly, the theorems from the paper
are available as a separate document (paper_theorems.pdf,
Paper_Theorems/index.html), where a notation similar to the one employed in the
paper is used. It can be seen as an entrypoint of the paper's reader to the
formalization. The raw Isabelle sources are contained in the thys/ directory.

There are few deviations from the description in the paper:

* The de Bruijn namespaces for first-order and second-order variables are disjoint.

* Formulas also split into an abstract and a concrete part (abstract formulas
  include the Boolean connectives and quantifiers and a single constructor for
  the concrete formulas, which in turn include the base formulas).

* Formulas include conjunctions and universal quantifiers. This means, e.g.,
  that the reasoning must happen not only modulo \/-ACI, but also modulo /\-ACI.

* We prove only soundness (and conditional completeness assuming termination)
  for a stronger normalization function (that is doing strictly more than ACI).

For readers unfamiliar with Isabelle, two separate implementations of the
algorithm in Standard ML are also available: one automatically extracted using
Isabelle's code generator with guaranteed soundness (WS1S_Generated.sml) and one
unverified manual minimal implementation (WS1S.sml).
