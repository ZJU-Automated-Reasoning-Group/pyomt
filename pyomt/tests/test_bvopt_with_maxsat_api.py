import pytest
import z3

from pyomt.omtbv.bv_opt_maxsat import bv_opt_with_maxsat


def test_bv_opt_with_maxsat_maximize_simple_range():
    y = z3.BitVec('y', 4)
    fml = z3.And(z3.UGT(y, 3), z3.ULT(y, 10))
    res = bv_opt_with_maxsat(fml, y, minimize=False, solver_name="FM")
    if res is not None:
        assert res == 9


def test_bv_opt_with_maxsat_minimize_simple_range():
    y = z3.BitVec('y', 4)
    fml = z3.And(z3.UGT(y, 3), z3.ULT(y, 10))
    res = bv_opt_with_maxsat(fml, y, minimize=True, solver_name="FM")
    if res is not None:
        assert res == 4


def test_bv_opt_with_maxsat_invalid_solver_returns_none():
    y = z3.BitVec('y', 4)
    fml = z3.And(z3.UGE(y, 0), z3.ULE(y, 15))
    res = bv_opt_with_maxsat(fml, y, minimize=True, solver_name="INVALID_SOLVER")
    assert res is None

