"""
Reduce OMT(BV) to Weighted MaxSAT

1. OBV-BS and its variants
2. Existing weighted MaxSAT...
"""
import logging
from typing import List

import z3

from omt.omtbv.bv_blast import BitBlastOMTBVSolver

logger = logging.getLogger(__name__)


def optimize_with_maxsat(z3_fml: z3.ExprRef, z3_obj: z3.ExprRef,
                                minimize: bool, solver_name: str):
    omt = BitBlastOMTBVSolver()
    omt.from_smt_formula(z3_fml)
    if minimize:
        return omt.minimize_with_maxsat(z3_obj, is_signed=False)
    else:
        return omt.maximize_with_maxsat(z3_obj, is_signed=False)


def demo_maxsat():
    import time
    x, y, z = z3.BitVecs("x y z", 16)
    fml = z3.And(z3.UGT(y, 3), z3.ULT(y, 10))
    print("start solving")
    res = optimize_with_maxsat(fml, y, minimize=False, solver_name="z3")
    print(res)
    start = time.time()
    print("solving time: ", time.time() - start)


if __name__ == '__main__':
    demo_maxsat()
