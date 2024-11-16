"""
TODO: use PySMT to implement the algorithms
  Can we use PySMT to parse the OMT instance directly?
  The current implementation involves converting z3 expr to pysmt, which is
  strange and can be slow...
"""
from pysmt.shortcuts import BV, BVULT, BVUGT, Solver, Symbol
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
                                minimize: bool, solver:str):
    """Linear Search based OMT using PySMT with bit-vectors."""

    obj, fml = convert_to_pysmt(z3_fml, z3_obj)
    print(obj)
    print(fml)

    with Solver(name=solver) as solver:
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


def optimize_with_binary_search(z3_fml: z3.ExprRef, z3_obj: z3.ExprRef,
                                minimize: bool, solver:str):
    """Binary Search based OMT using PySMT with bit-vectors."""
    # FIXME: generate by LLM.. (there are bugs..)

    obj, fml = convert_to_pysmt(z3_fml, z3_obj)
    print(obj)
    print(fml)

    with Solver(name=solver) as solver:
        solver.add_assertion(fml)

        if solver.solve():
            low = BV(0, obj.bv_width())
            high = None

            model = solver.get_model()
            if minimize:
                high = model.get_value(obj)
                while BVULT(low, high):
                    mid = low.BVAdd(high).BVLShiftRight(BV(1, obj.bv_width()))
                    solver.push()
                    solver.add_assertion(BVULT(obj, mid))
                    if solver.solve():
                        high = solver.get_model().get_value(obj)
                    else:
                        solver.pop()
                        low = mid.BVAdd(BV(1, obj.bv_width()))
            else:
                low = model.get_value(obj)
                high = BV(2 ** obj.bv_width() - 1, obj.bv_width())
                while BVULT(low, high):
                    mid = low.BVAdd(high).BVLShiftRight(BV(1, obj.bv_width()))
                    solver.push()
                    solver.add_assertion(BVUGT(obj, mid))
                    if solver.solve():
                        low = solver.get_model().get_value(obj)
                    else:
                        solver.pop()
                        high = mid.BVSub(BV(1, obj.bv_width()))

            return str(high if minimize else low)
        else:
            return "error"


def demo_iterative():
    import time
    x, y, z = z3.BitVecs("x y z", 16)
    fml = z3.And(z3.UGT(y, 0), z3.ULT(y, 10))
    print("start solving")
    res = optimize_with_linear_search(fml, y, minimize=True, solver="z3")
    # res = optimize_with_binary_search(fml, y, minimize=True, solver="z3")
    print(res)
    start = time.time()
    print("solving time: ", time.time() - start)


if __name__ == '__main__':
    demo_iterative()

