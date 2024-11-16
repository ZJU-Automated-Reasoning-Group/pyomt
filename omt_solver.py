# coding: utf-8
"""The uniformed interface for solving OMT(BV) problems
FIXME:
  - This file was used for EFSMT. We should fix it...
  - This file is the high-level, final interface. We should move "low-level"
      APIs to omt/omt_engines.
"""
import logging

logger = logging.getLogger(__name__)


class OMTSolver:

    def __init__(self, logic: str, **kwargs):
        self.phi = None
        self.obj = None

        self.logic = logic

        self.seed = kwargs.get("seed", 1)  # random seed
        self.solver = kwargs.get("solver", "z3")

    def solve(self):
        """
        Solve formulas via different strategies
        """
        print("OMT solver: {}".format(self.solver))
        # 1. Quantifier instantiation approach
        if self.solver == "z3":
            raise NotImplementedError
        elif self.solver == "cvc5":
            raise NotImplementedError
        elif self.solver == "btor":
            raise NotImplementedError
        elif self.solver == "yices2":
            raise NotImplementedError
        elif self.solver == "mathsat":
            raise NotImplementedError
        elif self.solver == "bitwuzla":
            raise NotImplementedError

        # 2. MaxSAT-based approach
        elif self.solver == "obv-bs":
            raise NotImplementedError
        else:
            raise NotImplementedError

        # 3. Simple SMT-based iterative approach
