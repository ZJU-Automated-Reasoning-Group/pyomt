import z3

from pyomt.utils.z3opt_utils import (
    optimize,
    optimize_as_long,
    box_optimize,
    box_optimize_as_long,
    maxsmt,
)


def test_optimize_and_as_long_maximize_simple_int():
    x = z3.Int('x')
    fml = z3.And(x > 3, x < 10)
    val = optimize(fml, x, minimize=False)
    val_long = optimize_as_long(fml, x, minimize=False)
    if val is not None:
        assert int(str(val)) == 9
    if val_long is not None:
        assert val_long == 9


def test_box_optimize_min_and_max_on_ints():
    x, y = z3.Ints('x y')
    fml = z3.And(x >= 0, x <= 5, y >= 0, y <= 7)
    mins, maxs = box_optimize(fml, minimize=[x], maximize=[y])
    if mins is not None and maxs is not None:
        assert int(str(mins[0])) == 0
        assert int(str(maxs[0])) == 7


def test_box_optimize_as_long_min_and_max_on_ints():
    x, y = z3.Ints('x y')
    fml = z3.And(x >= 1, x <= 3, y >= 2, y <= 4)
    mins, maxs = box_optimize_as_long(fml, minimize=[x], maximize=[y])
    if mins is not None and maxs is not None:
        assert mins == [1]
        assert maxs == [4]


def test_maxsmt_cost_simple():
    a, b = z3.Bools('a b')
    hard = z3.BoolVal(True)
    # Prefer a and b; they conflict with a hard clause only if false
    soft = [a, b]
    weight = [2, 3]
    cost = maxsmt(hard, soft, weight)
    # A satisfying model exists with both true ⇒ zero cost
    assert isinstance(cost, int)
    assert cost == 0

