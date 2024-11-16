"""
Reduce OMT(BV) to QSMT and call SMT solvers
that support quantified bit-vector formulas
- Z3
- CVC5
- Q3B
- ...?
"""

import z3


def opt_with_qsat(self, exp: z3.ExprRef, minimize: bool):
    """
    Quantified Satisfaction based OMT
    TODO: currently only works when exp is a variable (need to handle a term)?
    TODO: change to bv, or extend to bv?
    """
    if z3.is_real(exp):
        exp_misc = z3.Real(str(exp) + "_m")
    else:
        exp_misc = z3.Int(str(exp) + "m")
    s = z3.Solver()
    new_fml = z3.substitute(self.formula, (exp, exp_misc))
    if minimize:
        qfml = z3.And(self.formula, z3.ForAll([exp_misc], z3.Implies(new_fml, exp <= exp_misc)))
    else:
        # TODO: why not working when x can be +oo????
        qfml = z3.And(self.formula, z3.ForAll([exp_misc], z3.Implies(new_fml, exp_misc <= exp)))
    s.add(qfml)
    if s.check() == z3.sat:
        tt = s.model().eval(exp)
        return tt
    else:
        print(s.to_smt2())
        print("UNSAT")
