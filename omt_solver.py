import logging
import argparse
import z3

from pyomt.utils.opt_parser import OMTParser
from pyomt.omtbv.bv_opt_iterative_search import bv_opt_with_linear_search, \
    bv_opt_with_binary_search
from pyomt.omtbv.bv_opt_maxsat import bv_opt_with_maxsat
from pyomt.omtbv.bv_opt_qsmt import bv_opt_with_qsmt
from pyomt.utils.z3opt_utils import optimize_as_long

logger = logging.getLogger(__name__)


def solve_opt_file(filename: str, solver_name: str):
    """Interface for solving single-objective
    Currently, the OMTParser will convert all objectives to the "maximal objecives"
    """
    s = OMTParser()
    s.parse_with_z3(filename, is_file=True)
    # print(s.objectives)
    fml = z3.And(s.assertions)
    obj = s.objective
    # print(fml, obj)
    # 1. use z3 OPT
    z3_res = optimize_as_long(fml, obj)
    print("z3 res: ", z3_res)
    print("----------------------------------")

    # 2. use SMT-based linear search
    lin_res = bv_opt_with_linear_search(fml, obj, minimize=False, solver_name="z3")
    print("lin res: ", lin_res)
    print("----------------------------------")

    # 2. use SMT-based binary search
    bin_res = bv_opt_with_binary_search(fml, obj, minimize=False, solver_name="z3")
    print("bin res: ", bin_res)
    print("----------------------------------")

    # 3. use MaxSAT
    maxsat_res = bv_opt_with_maxsat(fml, obj, minimize=False, solver_name="fm")
    print("maxsat res: ", maxsat_res)
    print("----------------------------------")

    # 4. use QSMT
    qsmt_res = bv_opt_with_qsmt(fml, obj, minimize=False, solver_name="z3")
    print("qsmt res: ", qsmt_res)
    print("----------------------------------")


def main():
    def main():
        parser = argparse.ArgumentParser(description="Solve OMT(BV) problems with different solvers.")
        parser.add_argument("filename", type=str, help="The filename of the problem to solve.")
        parser.add_argument("--engine", type=str, default="qsmt",
                            choices=["qsmt", "maxsat", "iter"],
                            help="Choose the engine to use")

        # Create argument groups for each engine
        qsmt_group = parser.add_argument_group('qsmt', 'Arguments for the QSMT-based engine')
        qsmt_group.add_argument("--solver-qsmt", type=str, default="z3",
                                choices=["z3", "cvc5", "yices2", "mathsat", "bitwuzla"],
                                help="Choose the quantified SMT solver to use.")

        maxsat_group = parser.add_argument_group('maxsat', 'Arguments for the MaxSAT-based engine')
        maxsat_group.add_argument("--solver-maxsat", type=str, default="fm",
                                  choices=["fm", "rc2", "obv-bs"],
                                  help="Choose the weighted MaxSAT solver to use")

        iter_group = parser.add_argument_group('iter', 'Arguments for the iter-based engine')
        iter_group.add_argument("--solver-iter", type=str, default="z3",
                                choices=["z3", "cvc5", "yices2", "mathsat"],
                                help="Choose the quantifier-free SMT solver to use.")

        parser.add_argument("--seed", type=int, default=1, help="Random seed.")
        parser.add_argument("--log-level", type=str, default="INFO",
                            choices=["DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"],
                            help="Set the logging level.")

        args = parser.parse_args()

        logging.basicConfig(level=getattr(logging, args.log_level.upper(), None))

        # Ensure the correct solver is used based on the selected engine
        if args.engine == "qsmt":
            solver = args.solver_qsmt
        elif args.engine == "maxsat":
            solver = args.solver_maxsat
        elif args.engine == "iter":
            solver = args.solver_iter
        else:
            raise ValueError("Invalid engine specified")

        solve_opt_file(args.filename, solver)


if __name__ == "__main__":
    main()
