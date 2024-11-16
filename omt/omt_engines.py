"""
TODO: use utils.z3_plus_smtlib_solver to integrate third-party engine
"""

import z3
from enum import Enum

from omt.utils.z3_plus import Z3SolverPlus


class OMTEngineType(Enum):
    # FIXME: ...
    LINEAR_SEARCH = 0
    BINARY_SEARCH = 1  # not implemented
    MIXED_LINEAR_BINARY_SEARCH = 2  # not implemented
    QUANTIFIED_SATISFACTION = 3  # has bugs??
    Z3OPT = 4
    OptiMathSAT = 5  # external?
    CVC5 = 6  # does it support int and real?
    PYSMT = 7  # what does pysmt support


class OMTEngine:
    def __init__(self):
        self.initialized = False
        self.formula = None
        self.compact_opt = True
        self.engine_type = OMTEngineType.Z3OPT

    def maximize_with_linear_search(self, obj: z3.ExprRef):
        """
        Linear Search based OMT
        """
        raise NotImplementedError

    def opt_with_qsat(self, exp: z3.ExprRef, minimize: bool):
        """
        Quantified Satisfaction based OMT
        """
        raise NotImplementedError

    def max_with_qe(self, exp: z3.ExprRef):
        """
        Quantifier Elimination based OMT
        """
        raise NotImplementedError

    def minimize_with_z3opt(self, obj: z3.ExprRef):
        NotImplementedError

    def maximize_with_z3opt(self, obj: z3.ExprRef):
        NotImplementedError

    def minimize_with_optimathsat(self, obj: z3.ExprRef):
        s = Z3SolverPlus()  # FIXME: maybe change to use other ways?
        return s.optimize(self.formula, obj, minimize=True)

    def maximize_with_optimathsat(self, obj: z3.ExprRef):
        """
        Use OptiMathSAT (currently via pipe)
        """
        s = Z3SolverPlus()
        return s.optimize(self.formula, obj, minimize=False)

    def init_from_file(self, filename: str):
        try:
            self.formula = z3.And(z3.parse_smt2_file(filename))
            self.initialized = True
        except z3.Z3Exception as ex:
            print("error when initialization")
            print(ex)

    def init_from_fml(self, fml: z3.BoolRef):
        try:
            self.formula = fml
            self.initialized = True
        except z3.Z3Exception as ex:
            print("error when initialization")
            print(ex)

    def min_once(self, exp):
        """
        Minimize the objective exp
        """
        if self.engine_type == OMTEngineType.Z3OPT:
            return NotImplementedError
        elif self.engine_type == OMTEngineType.LINEAR_SEARCH:
            return NotImplementedError
        elif self.engine_type == OMTEngineType.BINARY_SEARCH:
            raise NotImplementedError
        elif self.engine_type == OMTEngineType.MIXED_LINEAR_BINARY_SEARCH:
            raise NotImplementedError
        elif self.engine_type == OMTEngineType.QUANTIFIED_SATISFACTION:
            return self.opt_with_qsat(exp, minimize=True)
        elif self.engine_type == OMTEngineType.OptiMathSAT:
            return self.minimize_with_optimathsat(exp)
        else:
            return self.minimize_with_z3opt(exp)

    def max_once(self, exp: z3.ExprRef):
        """
        Maximize the objective exp
        """
        if self.engine_type == OMTEngineType.Z3OPT:
            return self.maximize_with_z3opt(exp)
        elif self.engine_type == OMTEngineType.LINEAR_SEARCH:
            return self.maximize_with_linear_search(exp)
        elif self.engine_type == OMTEngineType.BINARY_SEARCH:
            raise self.maximize_with_linear_search()
        elif self.engine_type == OMTEngineType.QUANTIFIED_SATISFACTION:
            return self.opt_with_qsat(exp, minimize=False)
        elif self.engine_type == OMTEngineType.OptiMathSAT:
            return self.maximize_with_optimathsat(exp)
        else:
            return self.maximize_with_z3opt(exp)
