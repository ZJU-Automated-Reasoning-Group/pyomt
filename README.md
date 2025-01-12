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

### Integration
Exiting OMT solvers?
- Z3 (to MaxSAT?)
- OptiMathSAT
- ...

### Optimizations

**Improvements to the OBV-BS algorithm**
- Variable Polarity Setting: prefer 1 over 0 during the search?

The relevant API (NOTE: some SAT solvers in pysat do not support this API)
~~~~
    def set_phases(self, literals=[]):
        """
            Sets polarities of a given list of variables.
        """
~~~~
TBD: to see how to use this API...

## References

- Sebastiani, R., & Tomasi, S. (2015). Optimization in SMT with LA(Q) cost functions. In International Conference on Principles and Practice of Constraint Programming (pp. 484-498). Springer, Cham.
- Bjørner, N., Phan, A. D., & Fleckenstein, L. (2015). νZ-an optimizing SMT solver. In International Conference on Tools and Algorithms for the Construction and Analysis of Systems (pp. 194-199). Springer, Berlin, Heidelberg.
- Martins, R., Manquinho, V. M., & Lynce, I. (2014). Open-WBO: A modular MaxSAT solver. In International Conference on Theory and Applications of Satisfiability Testing (pp. 438-445). Springer, Cham.