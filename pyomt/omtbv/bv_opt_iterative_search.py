"""
TODO. pysmt cannot handle bit-vector operations in a few formulas generaed by z3.
 E.g., it may haave a more strict restriction on
  the number of arguments to certain bit-vector options
"""
from pysmt.shortcuts import BVULT, BVUGT
from pysmt.shortcuts import Symbol, And, BV, BVUGE, BVULE, Solver
import logging
import z3
from pysmt.typing import INT, REAL, BVType, BOOL

from pyomt.utils.config import g_enable_debug
from pyomt.utils.z3expr_utils import get_expr_vars

# BV1, BV8, BV16, BV32, BV64, BV128
logger = logging.getLogger(__name__)
# NOTE: both pysmt and z3 have a class "Solver"


def to_pysmt_vars(z3vars: [z3.ExprRef]):
    res = []
    for v in z3vars:
        if z3.is_int(v):
            res.append(Symbol(v.decl().name(), INT))
        elif z3.is_real(v):
            res.append(Symbol(v.decl().name(), REAL))
        elif z3.is_bv(v):
            res.append(Symbol(v.decl().name(), BVType(v.sort().size())))
        elif z3.is_bool(v):
            res.append(Symbol(v.decl().name(), BOOL))
        else:
            raise NotImplementedError
    return res


def convert_to_pysmt(zf: z3.ExprRef, obj: z3.ExprRef):
    # FIXME: we use  the following two lines to hide warnings from PYSMT(?)
    #  However, they seem not to be necessary and z3.z3util.get_vars can be very slow
    #  (Is the warning caused py pySMT?)
    # zvs = z3.z3util.get_vars(zf)  # this can be very slow...
    zvs = get_expr_vars(zf)

    _ = to_pysmt_vars(zvs)

    #
    z3s = Solver(name='z3')
    pysmt_var = Symbol(obj.decl().name(), BVType(obj.sort().size()))
    pysmt_fml = z3s.converter.back(zf)
    return pysmt_var, pysmt_fml
    # return pysmt_vars, pysmt_fml


def bv_opt_with_linear_search(z3_fml: z3.ExprRef, z3_obj: z3.ExprRef,
                              minimize: bool, solver_name: str):
    """Linear Search based OMT using PySMT with bit-vectors.
    solver_name: the backend SMT solver for pySMT
    """

    obj, fml = convert_to_pysmt(z3_fml, z3_obj)
    # print(obj)
    # print(fml)

    with Solver(name=solver_name) as solver:
        solver.add_assertion(fml)

        if minimize:
            lower = BV(0, obj.bv_width())
            while solver.solve():
                model = solver.get_model()
                lower = model.get_value(obj)
                solver.add_assertion(BVULT(obj, lower))
            return str(lower)
        else:
            cur_upper = None
            if solver.solve():
                model = solver.get_model()
                cur_upper = model.get_value(obj)
                solver.add_assertion(BVUGT(obj, cur_upper))

            while True:
                if solver.solve():
                    model = solver.get_model()
                    cur_upper = model.get_value(obj)
                    solver.add_assertion(BVUGT(obj, cur_upper))
                else:
                    break
            return str(cur_upper) if cur_upper is not None else "error"


def bv_opt_with_binary_search(z3_fml, z3_obj, minimize: bool, solver_name: str):
    """Binary Search based OMT using PySMT with bit-vectors."""
    # Convert Z3 expressions to PySMT
    obj, fml = convert_to_pysmt(z3_fml, z3_obj)
    print(obj)
    print(fml)

    sz = obj.bv_width()
    max_bv = (1 << sz) - 1

    if not minimize:
        solver = Solver(name=solver_name)
        solver.add_assertion(fml)

        cur_min, cur_max = 0, max_bv
        upper = BV(0, sz)

        while cur_min <= cur_max:
            solver.push()

            cur_mid = cur_min + ((cur_max - cur_min) >> 1)
            if g_enable_debug:
                print(f"min, mid, max: {cur_min}, {cur_mid}, {cur_max}")
                print(f"current upper: {upper}")

            # cur_min_expr = BV(cur_min, sz)
            cur_mid_expr = BV(cur_mid, sz)
            cur_max_expr = BV(cur_max, sz)

            cond = And(BVUGE(obj, cur_mid_expr),
                       BVULE(obj, cur_max_expr))
            solver.add_assertion(cond)

            if not solver.solve():
                cur_max = cur_mid - 1
                solver.pop()
            else:
                model = solver.get_model()
                upper = model.get_value(obj)
                cur_min = int(upper.constant_value()) + 1
                solver.pop()

        return upper
    else:
        # Compute minimum
        solver = Solver(name=solver_name)
        solver.add_assertion(fml)
        cur_min, cur_max = 0, max_bv
        lower = BV(max_bv, sz)

        while cur_min <= cur_max:
            solver.push()
            cur_mid = cur_min + ((cur_max - cur_min) >> 1)
            if g_enable_debug:
                print(f"Min search - min, mid, max: {cur_min}, {cur_mid}, {cur_max}")

            cur_min_expr = BV(cur_min, sz)
            cur_mid_expr = BV(cur_mid, sz)
            # cur_max_expr = BV(cur_max, sz)
            cond = And(BVUGE(obj, cur_min_expr),
                       BVULE(obj, cur_mid_expr))
            solver.add_assertion(cond)

            if not solver.solve():
                cur_min = cur_mid + 1
                solver.pop()
            else:
                model = solver.get_model()
                lower = model.get_value(obj)
                cur_max = int(lower.constant_value()) - 1
                solver.pop()

        min_value = lower
        return min_value


def demo_iterative():
    import time
    x, y, z = z3.BitVecs("x y z", 16)
    fml = z3.And(z3.UGT(y, 3), z3.ULT(y, 10))
    print("start solving")
    lin_res = bv_opt_with_linear_search(fml, y, minimize=False, solver_name="z3")
    print(lin_res)
    bin_res = bv_opt_with_binary_search(fml, y, minimize=True, solver_name="z3")
    print(bin_res)
    start = time.time()
    print("solving time: ", time.time() - start)


if __name__ == '__main__':
    demo_iterative()
