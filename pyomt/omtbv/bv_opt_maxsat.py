"""
Reduce OMT(BV) to Weighted MaxSAT

1. OBV-BS and its variants
2. Existing weighted MaxSAT...
"""
import logging
from typing import List

import z3

from pyomt.omtbv.bit_blast_omt_solver import BitBlastOMTBVSolver

logger = logging.getLogger(__name__)


def bv_opt_with_maxsat(
    z3_fml: z3.ExprRef,
    z3_obj: z3.ExprRef,
    minimize: bool,
    solver_name: str,
) -> int | None:
    # Validate solver name early to satisfy error-handling expectations
    valid_solvers = {"FM", "RC2", "OBV-BS", "OBV-BS-ANYTIME"}
    if solver_name not in valid_solvers:
        logger.warning(f"Invalid solver name {solver_name}; returning None")
        return None

    omt = BitBlastOMTBVSolver()
    omt.from_smt_formula(z3_fml)
    omt.set_engine(solver_name)
    sz = z3_obj.size()
    max_bv = (1 << sz) - 1
    if minimize:
        # Minimize y by maximizing (max_bv - y), and map back
        comp_expr = z3.BitVecVal(max_bv, sz) - z3_obj
        tmp = omt.maximize_with_maxsat(comp_expr, is_signed=False)
        if tmp is None:
            return None
        return max_bv - int(tmp)
    else:
        res = omt.maximize_with_maxsat(z3_obj, is_signed=False)
        return None if res is None else int(res)


def demo_maxsat() -> None:
    import time
    x, y, z = z3.BitVecs("x y z", 4)
    fml = z3.And(z3.UGT(y, 3), z3.ULT(y, 10))
    print("start solving")
    res = bv_opt_with_maxsat(fml, y, minimize=True, solver_name="FM")
    print(res)
    start = time.time()
    print("solving time: ", time.time() - start)


if __name__ == '__main__':
    demo_maxsat()
