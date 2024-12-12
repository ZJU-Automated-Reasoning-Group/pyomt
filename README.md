# A library for OMT(BV) Solving


Optimization Modulo Theory (OMT) extends Satisfiability Modulo Theories (SMT)
by incorporating optimization objectives.

## The Engines

### Reduce to Quantified SMT

- Z3
- CVC5
- Yices-QS
- Bitwuzla

### Reduce to Weighted MaxSAT


- The OBV-BS algorithm
- The FM algorithm
- The RC2 algorithm
- Off-the-shelf MaxSAT solvers
~~~~
https://github.com/FlorentAvellaneda/EvalMaxSAT

~~~~

### SMT-based Iterative Search

- Linear search
- Binary search

## TBD

Differential testing?

Exiting OMT solvers?
- Z3 (to MaxSAT?)
- OptimathSAT
- ...

~~~~
pysmt.exceptions.ConvertExpressionError: Unsupported expression: bvxnor(bv_41-0, bv_41-0)

~~~~
## References
