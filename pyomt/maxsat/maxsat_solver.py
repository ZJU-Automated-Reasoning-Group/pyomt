# coding: utf-8
"""
This module provides a MaxSATSolver class that wraps different MaxSAT engines and implements
methods for solving weighted and unweighted MaxSAT problems

TODO: add interfaces for calling binary solvers?
"""

import copy

from pysat.formula import WCNF

from pyomt.maxsat.bs import obv_bs
from pyomt.maxsat.fm import FM  # is the FM correct???
from pyomt.maxsat.rc2 import RC2


class MaxSATSolver:
    """
    Wrapper of the engines in maxsat
    """

    def __init__(self, formula: WCNF):
        """
        :param formula: input MaxSAT formula
        """
        self.maxsat_engine = "FM"
        self.wcnf = formula
        self.hard = copy.deepcopy(formula.hard)
        self.soft = copy.deepcopy(formula.soft)
        self.weight = formula.wght[:]

        self.sat_engine_name = "m22"
        # g3, g4, lgl, mcb, mcm, mpl, m22, mc, mgh, z3

    def set_maxsat_engine(self, name: str):
        self.maxsat_engine = name

    def get_maxsat_engine(self):
        """Get MaxSAT engine"""
        return self.maxsat_engine

    def solve_wcnf(self):
        """TODO: support Popen-based approach for calling bin solvers (e.g., open-wbo)"""
        if self.maxsat_engine == "FM":
            fm = FM(self.wcnf, verbose=0)
            fm.compute()
            # print("cost, ", fm.cost)
            return fm.cost
        elif self.maxsat_engine == "RC2":
            rc2 = RC2(self.wcnf)
            rc2.compute()
            return rc2.cost
        elif self.maxsat_engine == "obv-bs":
            bits = []
            for i in reversed(range(len(self.soft))):
                bits.append(self.soft[i][0])
            return obv_bs(self.hard, bits)
        else:
            fm = FM(self.wcnf, verbose=0)
            fm.compute()
            return fm.cost
