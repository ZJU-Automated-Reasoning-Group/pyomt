# coding: utf-8
"""
This module provides a MaxSATSolver class that wraps different MaxSAT engines and implements methods for solving weighted and unweighted MaxSAT problems.

TODO: allow for calling binary MaxSAT solvers
"""

import copy
import time
import logging
from dataclasses import dataclass
from typing import List, Optional, Union, Dict
from enum import Enum

from pysat.formula import WCNF

from pyomt.maxsat.bs import obv_bs, obv_bs_anytime
from pyomt.maxsat.fm import FM
from pyomt.maxsat.rc2 import RC2

logger = logging.getLogger(__name__)

class MaxSATEngine(str, Enum):
    """Available MaxSAT solving engines"""
    FM = "FM"
    RC2 = "RC2"
    OBV_BS = "OBV-BS"
    OBV_BS_ANYTIME = "OBV-BS-ANYTIME"

@dataclass
class SolverResult:
    """Stores the results of a MaxSAT solving operation"""
    cost: float
    solution: Optional[List[int]] = None
    runtime: Optional[float] = None
    status: str = "unknown"
    statistics: Optional[Dict] = None

class MaxSATSolver:
    """
    Wrapper of the engines in maxsat with enhanced functionality
    """

    def __init__(self, formula: WCNF, timeout: float = 3600) -> None:
        """
        Initialize MaxSAT solver
        
        Args:
            formula: input MaxSAT formula
            timeout: solving timeout in seconds (default: 1 hour)
        """
        self.maxsat_engine = MaxSATEngine.FM
        self.wcnf = formula
        self.timeout = timeout
        
        # Store formula components
        self.hard = copy.deepcopy(formula.hard)
        self.soft = copy.deepcopy(formula.soft)
        self.weight = formula.wght[:]
        
        # Solver configuration
        self.sat_engine_name = "m22"
        self.statistics = {}
        self._last_result = None

    def set_maxsat_engine(self, name: Union[str, MaxSATEngine]) -> None:
        """Set MaxSAT engine by name or enum"""
        if isinstance(name, str):
            try:
                self.maxsat_engine = MaxSATEngine(name)
            except ValueError:
                logger.warning(f"Unknown engine {name}, falling back to FM")
                self.maxsat_engine = MaxSATEngine.FM
        else:
            self.maxsat_engine = name

    def get_maxsat_engine(self) -> MaxSATEngine:
        """Get current MaxSAT engine"""
        return self.maxsat_engine

    @property
    def formula(self) -> WCNF:
        """Get the current MaxSAT formula"""
        return self.wcnf

    @property
    def last_result(self) -> Optional[SolverResult]:
        """Get the result of the last solve call"""
        return self._last_result

    def solve(self) -> SolverResult:
        """
        Solve the MaxSAT problem using the selected engine
        
        Returns:
            SolverResult containing cost, solution, runtime and statistics
        """
        start_time = time.time()
        result = SolverResult(float('inf'))
        
        try:
            if self.maxsat_engine == MaxSATEngine.FM:
                fm = FM(self.wcnf, verbose=0)
                solved = fm.compute()
                if solved:
                    result.cost = fm.cost
                    result.solution = getattr(fm, 'model', None)
                    result.status = "optimal"
                else:
                    result.cost = float('inf')
                    result.solution = None
                    result.status = "unsat"
                
            elif self.maxsat_engine == MaxSATEngine.RC2:
                rc2 = RC2(self.wcnf)
                model = rc2.compute()
                if model is not None:
                    result.cost = rc2.cost
                    result.solution = model
                    result.status = "optimal"
                else:
                    result.cost = float('inf')
                    result.solution = None
                    result.status = "unsat"
                
            elif self.maxsat_engine == MaxSATEngine.OBV_BS:
                bits = [self.soft[i][0] for i in reversed(range(len(self.soft)))]
                solution = obv_bs(self.hard, bits)
                result.cost = sum(1 for bit in solution if bit > 0)
                result.solution = solution
                result.status = "optimal"
                
            elif self.maxsat_engine == MaxSATEngine.OBV_BS_ANYTIME:
                bits = [self.soft[i][0] for i in reversed(range(len(self.soft)))]
                solution = obv_bs_anytime(self.hard, bits, time_limit=self.timeout)
                result.cost = sum(1 for bit in solution if bit > 0)
                result.solution = solution
                result.status = "optimal" if len(solution) == len(bits) else "timeout"
                
            else:
                logger.warning(f"Unknown engine {self.maxsat_engine}, using FM")
                fm = FM(self.wcnf, verbose=0)
                solved = fm.compute()
                if solved:
                    result.cost = fm.cost
                    result.solution = getattr(fm, 'model', None)
                    result.status = "optimal"
                else:
                    result.cost = float('inf')
                    result.solution = None
                    result.status = "unsat"

        except Exception as e:
            logger.error(f"Error solving MaxSAT problem: {str(e)}")
            result.status = "error"
            result.statistics = {"error": str(e)}
            
        finally:
            result.runtime = time.time() - start_time
            self._last_result = result
            
        return result
