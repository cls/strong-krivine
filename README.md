Strong Krivine machine
======================

The Krivine machine (Krivine 2007) is a well-known abstract machine for
the evaluation of λ-terms, but it can achieve only weak normalisation.
This variant, based on the λσ⇑-calculus (Hardin and Lévy 1989), uses an
explicit substitution instead of an environment, and a context instead
of a stack, in order to achieve strong normalisation, as well as fixing
a ‘space leak’ normally patched by an auxiliary lookup function.

This was first described by the author (Smith 2014), and has since been
cited in later research (Accattoli et al. 2015).

* Krivine (2007) – A call-by-name lambda-calculus machine.
* Hardin and Lévy (1989) – A confluent calculus of substitutions.
* Smith (2014) – Abstract machines for higher-order term sharing.
* Accattoli, Barenbaum, and Mazza (2015) – A strong distillery.
