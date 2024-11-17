"""Parse an OMT instance"""

import z3
from z3.z3consts import *

from omt.omtbv.opt_with_iterative_search import optimize_with_linear_search, \
    optimize_with_binary_search
from omt.omtbv.omt_with_maxsat import optimize_with_maxsat
from omt.omtbv.opt_with_qsmt import opt_with_qsmt


class OMTParser:
    """Currently, we focus on two modes
    1. Single-objective optimization
    2. Multi-objective optimization under the boxed mode (each obj is independent)"""

    def __init__(self):
        """
        For multi-objective optimization,
        """
        self.assertions = None
        self.objectives = []
        self.to_max_obj = True  # convert all objectives to max
        self.to_min_obj = False  # convert all objectives to min
        self.debug = True

    def parse_with_pysmt(self):
        # pysmt does not support
        raise NotImplementedError

    def parse_with_z3(self, fml: str, is_file=False):
        """FIXME: Should we convert all the objectives/goals as all "minimize goals" (as Z3 does)?
            (or should we convert them to "maximize goals"?)
            However, the queries can be of the form "max x; min x; max y; min y; ...."
        """
        s = z3.Optimize()
        if is_file:
            s.from_file(fml)
        else:
            s.from_string(fml)
        self.assertions = s.assertions()
        # We cannot set both self.to_min_obj and self.to_max_obj to True
        assert not (self.to_min_obj and self.to_max_obj)
        if self.to_min_obj:
            # It sees that Z3 will convert each goal of the form "max f"  to "-f".
            # So, we just assign s.objectives() to self.objectives
            self.objectives = s.objectives()
        elif self.to_max_obj:
            # https://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml
            # TODO: the semantics of bvneg: [[(bvneg s)]] := nat2bv[m](2^m - bv2nat([[s]]))
            # Z3 will convert each goal of the form "max f"  to "-f".
            # So, we need to "convert them back"?
            for obj in s.objectives():
                # if calling z3.simplify(-obj), the obj may look a bit strange
                if obj.decl().kind() == Z3_OP_BNEG:
                    # self.objectives.append(-obj)
                    # If the obj is of the form "-expr", we can just add "expr" instead of "--expr"?
                    self.objectives.append(obj.children()[0])
                else:
                    self.objectives.append(-obj)
        if self.debug:
            for obj in self.objectives:
                print("obj: ", obj)


# (set-option :opt.priority box)

def demo_omt_parser():
    from omt.omtbv.omt_with_maxsat import BitBlastOMTBVSolver
    from omt.utils.z3opt_utils import optimize_as_long
    fml_two = """
    (declare-const x (_ BitVec 4)) \n (declare-const y (_ BitVec 4)) \n
    (assert (bvult x (_ bv5 4))) \n (assert (bvuge y (_ bv3 4))) \n
    (maximize x) \n (check-sat)
    """

    # print(optimize_as_long(fml=fml, obj=-x, minimize=False))  # 15?
    s = OMTParser()
    s.parse_with_z3(fml_two)
    # print(s.objectives)
    fml = z3.And(s.assertions)
    obj = s.objectives[0]
    print(fml, obj)
    # 1. use z3 OPT
    z3_res = optimize_as_long(fml, obj)
    print("z3 res: ", z3_res)
    print("----------------------------------")

    # 2. use SMT-based linear search
    lin_res = optimize_with_linear_search(fml, obj, minimize=False, solver_name="z3")
    print("lin res: ", lin_res)
    print("----------------------------------")

    # 2. use SMT-based binary search
    bin_res = optimize_with_binary_search(fml, obj, minimize=False, solver_name="z3")
    print("bin res: ", bin_res)
    print("----------------------------------")

    # 3. use MaxSAT
    maxsat_res = optimize_with_maxsat(fml, obj, minimize=False, solver_name="z3")
    print("maxsat res: ", maxsat_res)
    print("----------------------------------")

    # 4. use QSMT
    qsmt_res = opt_with_qsmt(fml, obj, minimize=False, solver_name="z3")
    print("qsmt res: ", qsmt_res)
    print("----------------------------------")


if __name__ == "__main__":
    # a, b, c, d = z3.Ints('a b c d')
    # fml = z3.Or(z3.And(a == 3, b == 3), z3.And(a == 1, b == 1, c == 1, d == 1))
    demo_omt_parser()