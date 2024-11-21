"""
Reduce OMT(BV) to Weighted MaxSAT

1. OBV-BS and its variants
2. Existing weighted MaxSAT...
"""
import logging
from typing import List

import z3

from pyomt.omtbv.bv_blast import BitBlastOMTBVSolver

logger = logging.getLogger(__name__)


def bv_opt_with_maxsat(z3_fml: z3.ExprRef, z3_obj: z3.ExprRef,
                       minimize: bool, solver_name: str):
    omt = BitBlastOMTBVSolver()
    omt.from_smt_formula(z3_fml)
    omt.set_engine(solver_name)
    sz = z3_obj.size()
    max_bv = (1 << sz) - 1
    if minimize:
        # TODO: add the API minimize_with_maxsat?
        # return omt.minimize_with_maxsat(z3_obj, is_signed=False)
        # is the following right?
        tmp = omt.maximize_with_maxsat(-z3_obj, is_signed=False)
        print(tmp)
        return max_bv - tmp
    else:
        return omt.maximize_with_maxsat(z3_obj, is_signed=False)


def demo_maxsat():
    import time
    x, y, z = z3.BitVecs("x y z", 4)
    fml = z3.And(z3.UGT(y, 3), z3.ULT(y, 10))
    print("start solving")
    res = bv_opt_with_maxsat(fml, y, minimize=True, solver_name="fm")
    print(res)
    start = time.time()
    print("solving time: ", time.time() - start)


if __name__ == '__main__':
    demo_maxsat()
