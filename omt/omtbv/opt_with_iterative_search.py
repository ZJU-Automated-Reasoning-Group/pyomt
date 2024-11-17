"""
TODO: use PySMT to implement the algorithms
  Can we use PySMT to parse the OMT instance directly?
  The current implementation involves converting z3 expr to pysmt, which is
  strange and can be slow...
"""
from pysmt.shortcuts import BV, BVULT, BVUGT, Solver, Symbol
from pysmt.shortcuts import Symbol, And, Not, Or, Ite, BV, BVUGE, BVULE, Solver, is_sat
import logging
import z3
from pysmt.logics import QF_BV  # AUTO
from pysmt.typing import INT, REAL, BVType

# BV1, BV8, BV16, BV32, BV64, BV128

logger = logging.getLogger(__name__)


# NOTE: both pysmt and z3 have a class "Solver"

def convert_to_pysmt(zf: z3.ExprRef, obj: z3.ExprRef):
    # zvs = z3.z3util.get_vars(zf)
    # pysmt_vars = to_pysmt_vars(zvs)
    z3s = Solver(name='z3')
    pysmt_var = Symbol(obj.decl().name(), BVType(obj.sort().size()))
    pysmt_fml = z3s.converter.back(zf)
    return pysmt_var, pysmt_fml
    # return pysmt_vars, pysmt_fml


def optimize_with_linear_search(z3_fml: z3.ExprRef, z3_obj: z3.ExprRef,
                                minimize: bool, solver_name: str):
    """Linear Search based OMT using PySMT with bit-vectors."""

    obj, fml = convert_to_pysmt(z3_fml, z3_obj)
    print(obj)
    print(fml)

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


def optimize_with_binary_search(z3_fml, z3_obj, minimize: bool, solver_name: str):
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
            if True:
                print(f"min, mid, max: {cur_min}, {cur_mid}, {cur_max}")
                print(f"current upper: {upper}")

            # cur_min_expr = BV(cur_min, sz)
            cur_mid_expr = BV(cur_mid, sz)
            cur_max_expr = BV(cur_max, sz)

            cond = And(BVUGE(obj, cur_mid_expr), BVULE(obj, cur_max_expr))
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
            if True:
                print(f"Min search - min, mid, max: {cur_min}, {cur_mid}, {cur_max}")

            cur_mid_expr = BV(cur_mid, sz)
            cond = And(BVUGE(fml, cur_min), BVULE(obj, cur_mid_expr))
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
    # res = optimize_with_linear_search(fml, y, minimize=True, solver_name="z3")
    res = optimize_with_binary_search(fml, y, minimize=True, solver_name="z3")
    print(res)
    start = time.time()
    print("solving time: ", time.time() - start)


if __name__ == '__main__':
    demo_iterative()