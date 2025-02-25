"""
Boxed optimization (multi-independent objectives)
1. One-by-one
2. Compact

FIXME: by LLM, to check if this is correct
"""
import pytest
import z3
import time
import logging

from pyomt.omtbv.boxed.bv_boxed_seq import solve_boxed_sequential
from pyomt.omtbv.boxed.bv_boxed_obj_divide import solve_boxed_parallel
from pyomt.omtbv.boxed.bv_boxed_compact import get_input, map_bitvector, solve as solve_compact

logger = logging.getLogger(__name__)

class TestBoxedBVOpt:
    def test_simple_sequential(self):
        """Test sequential optimization with simple constraints"""
        x = z3.BitVec('x', 8)
        y = z3.BitVec('y', 8)
        formula = z3.And(x >= 0, y >= 0, x + y <= 10)
        objectives = [x, y]
        
        result = solve_boxed_sequential(formula, objectives, minimize=False)
        assert len(result) == 2, "Should return results for both objectives"
        assert result[0] <= 10, "First objective should respect sum constraint"
        assert result[1] <= 10, "Second objective should respect sum constraint"
        assert result[0] + result[1] <= 10, "Sum constraint should be satisfied"

    def test_simple_parallel(self):
        """Test parallel optimization with simple constraints"""
        x = z3.BitVec('x', 8)
        y = z3.BitVec('y', 8)
        formula = z3.And(x >= 0, y >= 0, x + y <= 10)
        objectives = [x, y]
        
        result = solve_boxed_parallel(formula, objectives, minimize=False, timeout=10)
        assert len(result) == 2, "Should return results for both objectives"
        assert all(r is not None for r in result), "All objectives should be solved"
        assert result[0] + result[1] <= 10, "Sum constraint should be satisfied"

    def test_minimize_maximize_mix(self):
        """Test mixed minimization and maximization objectives"""
        x = z3.BitVec('x', 4)
        y = z3.BitVec('y', 4)
        formula = z3.And(x >= 2, y >= 2, x + y <= 10)
        
        # Test sequential
        result_seq = solve_boxed_sequential(
            formula, [x, y], minimize=True, engine="qsmt"
        )
        assert result_seq[0] >= 2, "x should be >= 2"
        assert result_seq[1] >= 2, "y should be >= 2"
        
        # Test parallel
        result_par = solve_boxed_parallel(
            formula, [x, y], minimize=False, engine="qsmt"
        )
        assert result_par[0] >= 2, "x should be >= 2"
        assert result_par[1] >= 2, "y should be >= 2"

    def test_different_engines(self):
        """Test optimization with different engines"""
        x = z3.BitVec('x', 8)
        formula = z3.And(x >= 5, x <= 100)
        objectives = [x]
        
        engines = [
            ("qsmt", "z3"),
            ("maxsat", "FM"),
            ("iter", "z3-bs")
        ]
        
        for engine, solver in engines:
            result = solve_boxed_sequential(
                formula, objectives, minimize=True, 
                engine=engine, solver_name=solver
            )
            assert result[0] == 5, f"Minimum value with {engine} should be 5"

    def test_timeout_handling(self):
        """Test timeout handling in parallel solver"""
        x = z3.BitVec('x', 32)  # Larger bitvector to make it slower
        y = z3.BitVec('y', 32)
        formula = z3.And(x >= 0, y >= 0, x + y <= 1000000)
        objectives = [x, y]
        
        start_time = time.time()
        result = solve_boxed_parallel(
            formula, objectives, minimize=False,
            timeout=1.0  # Very short timeout
        )
        elapsed = time.time() - start_time
        
        assert elapsed < 2.0, "Should respect timeout"
        assert len(result) == 2, "Should return results for all objectives"

    def test_error_handling(self):
        """Test error handling with invalid inputs"""
        x = z3.BitVec('x', 8)
        formula = z3.And(x >= 0)
        objectives = [x]
        
        with pytest.raises(ValueError):
            solve_boxed_sequential(formula, objectives, engine="invalid_engine")
            
        with pytest.raises(ValueError):
            solve_boxed_sequential(
                formula, objectives, 
                engine="iter", solver_name="invalid_solver"
            )

    def test_compact_solver(self):
        """Test compact solver implementation"""
        x = z3.BitVec('x', 4)
        y = z3.BitVec('y', 4)
        formula = z3.And(x >= 0, y >= 0, x + y <= 10)
        objectives = [[x, 1], [y, 0]]  # maximize x, minimize y
        
        mapped_objectives = map_bitvector(objectives)
        result = solve_compact(formula, mapped_objectives)
        
        assert len(result) == 2, "Should return results for both objectives"
        assert all(len(r) == 4 for r in result), "Each result should have 4 bits"
        
        # Convert bit arrays to integers
        x_val = sum(b * (2 ** i) for i, b in enumerate(reversed(result[0])))
        y_val = sum(b * (2 ** i) for i, b in enumerate(reversed(result[1])))
        
        assert x_val + y_val <= 10, "Sum constraint should be satisfied"

if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    pytest.main([__file__])
