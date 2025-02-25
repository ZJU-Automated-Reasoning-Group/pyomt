"""
Test Bit-vector Optimization
1. To QSMT (E-matching, MBQI, CEGQI, ...)
2. To weighted MaxSAT (OBV-BS, General)
3. SMT-based iterative search (linear, binary, adaptive)
"""
import pytest
import z3
import logging
from typing import List, Optional

from pyomt.omtbv.bv_opt_qsmt import bv_opt_with_qsmt
from pyomt.omtbv.bv_opt_maxsat import bv_opt_with_maxsat
from pyomt.omtbv.bv_opt_iterative_search import (
    bv_opt_with_linear_search,
    bv_opt_with_binary_search
)

logger = logging.getLogger(__name__)

class TestBVOptimization:
    def test_qsmt_basic(self):
        """Test basic QSMT-based optimization"""
        x = z3.BitVec('x', 8)
        formula = z3.And(x >= 5, x <= 100)
        
        # Test minimization
        result = bv_opt_with_qsmt(formula, x, minimize=True)
        assert result == 5, "Minimum value should be 5"
        
        # Test maximization
        result = bv_opt_with_qsmt(formula, x, minimize=False)
        assert result == 100, "Maximum value should be 100"

    def test_maxsat_conversion(self):
        """Test MaxSAT-based optimization with bit-blasting"""
        x = z3.BitVec('x', 4)
        y = z3.BitVec('y', 4)
        formula = z3.And(x >= 2, y >= 2, x + y <= 10)
        
        # Test with different MaxSAT engines
        engines = ["FM", "RC2", "OBV-BS"]
        for engine in engines:
            result = bv_opt_with_maxsat(formula, x, minimize=True, solver_name=engine)
            assert result >= 2, f"Result with {engine} should be >= 2"
            assert result <= 8, f"Result with {engine} should be <= 8"

    def test_iterative_search(self):
        """Test iterative search methods"""
        x = z3.BitVec('x', 8)
        formula = z3.And(x >= 10, x <= 50)
        
        # Test linear search
        linear_result = bv_opt_with_linear_search(formula, x, minimize=True)
        assert linear_result == 10, "Linear search minimum should be 10"
        
        # Test binary search
        binary_result = bv_opt_with_binary_search(formula, x, minimize=False)
        assert binary_result == 50, "Binary search maximum should be 50"

    def test_edge_cases(self):
        """Test edge cases and corner conditions"""
        x = z3.BitVec('x', 4)  # 4-bit vector (0-15)
        
        # Test with maximum possible value
        formula = z3.And(x >= 0, x <= 15)
        result = bv_opt_with_qsmt(formula, x, minimize=False)
        assert result == 15, "Should find maximum possible value"
        
        # Test with minimum possible value
        result = bv_opt_with_qsmt(formula, x, minimize=True)
        assert result == 0, "Should find minimum possible value"

    def test_unsatisfiable(self):
        """Test handling of unsatisfiable formulas"""
        x = z3.BitVec('x', 8)
        formula = z3.And(x > 10, x < 5)  # Unsatisfiable
        
        result = bv_opt_with_qsmt(formula, x, minimize=True)
        assert result is None, "Should return None for unsatisfiable formula"

    def test_multiple_variables(self):
        """Test optimization with multiple variables"""
        x = z3.BitVec('x', 8)
        y = z3.BitVec('y', 8)
        formula = z3.And(
            x >= 0, y >= 0,
            x + y <= 20,
            x >= y
        )
        
        # Test optimization of sum
        obj = x + y
        result = bv_opt_with_qsmt(formula, obj, minimize=False)
        assert result <= 20, "Sum should respect the upper bound"
        
        # Test optimization of difference
        obj = x - y
        result = bv_opt_with_qsmt(formula, obj, minimize=True)
        assert result >= 0, "Difference should be non-negative"

    def test_performance_comparison(self):
        """Compare performance of different approaches"""
        import time
        x = z3.BitVec('x', 16)  # Larger bitvector for meaningful comparison
        formula = z3.And(x >= 1000, x <= 5000, x % 7 == 0)
        
        methods = [
            ("QSMT", lambda: bv_opt_with_qsmt(formula, x, minimize=True)),
            ("MaxSAT", lambda: bv_opt_with_maxsat(formula, x, minimize=True)),
            ("Binary", lambda: bv_opt_with_binary_search(formula, x, minimize=True))
        ]
        
        results = {}
        for name, method in methods:
            start = time.time()
            try:
                result = method()
                duration = time.time() - start
                results[name] = (result, duration)
                logger.info(f"{name}: result={result}, time={duration:.3f}s")
            except Exception as e:
                logger.error(f"{name} failed: {str(e)}")
        
        # Verify all methods found the same result
        values = [r[0] for r in results.values() if r[0] is not None]
        if values:
            assert all(v == values[0] for v in values), "All methods should find same optimum"

if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    pytest.main([__file__])


