import z3

from pyomt.utils.z3expr_utils import get_expr_vars, get_expr_vars_z3default


def test_get_expr_vars_matches_z3default_on_simple_terms():
    x, y = z3.BitVecs("x y", 4)
    f = z3.And(z3.UGT(x, 1), z3.ULT(y, 10), x != y)
    ours = sorted(v.decl().name() for v in get_expr_vars(f))
    z3s = sorted(v.decl().name() for v in get_expr_vars_z3default(f))
    assert set(ours) <= set(z3s)


def test_get_expr_vars_handles_non_app_safely():
    # A pure constant
    c = z3.BitVecVal(5, 8)
    res = get_expr_vars(c)
    assert isinstance(res, list)
    assert res == []

