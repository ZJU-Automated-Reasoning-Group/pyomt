"""
Reduce OMT(BV) to QSMT and call SMT solvers
that support quantified bit-vector formulas
- Z3
- CVC5
- Q3B
- ...?
"""

import z3
from omt.utils.bin_solver import solve_with_bin_smt


def opt_with_qsmt(self, exp: z3.ExprRef, minimize: bool, solver_name: str):
    """ Quantified Satisfaction based OMT
    """
    exp_misc = z3.BitVec(str(exp) + "m", exp.size())
    new_fml = z3.substitute(self.formula, (exp, exp_misc))
    # TODO: bvule or < (distinguish between unsigned and signed...)
    if minimize:
        qfml = z3.And(self.formula,
                      z3.ForAll([exp_misc], z3.Implies(new_fml, z3.ULE(exp, exp_misc))))
    else:
        qfml = z3.And(self.formula,
                      z3.ForAll([exp_misc], z3.Implies(new_fml, z3.ULE(exp_misc, exp))))

    """
    s = z3.Solver()
    s.add(qfml)
    if s.check() == z3.sat:
        tt = s.model().eval(exp)
        return tt
    """
    return solve_with_bin_smt("BV", qfml=qfml, solver_name=solver_name)
