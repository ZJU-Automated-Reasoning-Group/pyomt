import pytest
import z3
from pyomt.omtbv.bv_opt_maxsat import bv_opt_with_maxsat
import logging

logger = logging.getLogger(__name__)


class TestBVOptMaxSAT:

    def test_maximize_simple(self):
        # Test maximization with y > 3 and y < 10
        y = z3.BitVec('y', 4)
        fml = z3.And(z3.UGT(y, 3), z3.ULT(y, 10))
        result = bv_opt_with_maxsat(fml, y, minimize=False, solver_name="FM")
        assert result == 9, "Should find maximum value 9"

    def test_minimize_simple(self):
        # Test minimization with y > 3 and y < 10
        y = z3.BitVec('y', 4)
        fml = z3.And(z3.UGT(y, 3), z3.ULT(y, 10))
        result = bv_opt_with_maxsat(fml, y, minimize=True, solver_name="FM")
        assert result == 4, "Should find minimum value 4"

    def test_larger_bitvec(self):
        # Test with 8-bit vector
        y = z3.BitVec('y', 8)
        fml = z3.And(z3.UGT(y, 100), z3.ULT(y, 200))
        result = bv_opt_with_maxsat(fml, y, minimize=False, solver_name="FM")
        assert result == 199, "Should find maximum value 199"

    def test_edge_case_max(self):
        # Test with maximum possible value in range
        y = z3.BitVec('y', 4)
        fml = z3.And(z3.UGE(y, 0), z3.ULE(y, 15))
        result = bv_opt_with_maxsat(fml, y, minimize=False, solver_name="FM")
        print(result)
        assert result == 15, "Should find maximum possible 4-bit value"

    def test_edge_case_min(self):
        # Test with minimum possible value in range
        y = z3.BitVec('y', 4)
        fml = z3.And(z3.UGE(y, 0), z3.ULE(y, 15))
        result = bv_opt_with_maxsat(fml, y, minimize=True, solver_name="FM")
        assert result == 0, "Should find minimum possible value"
