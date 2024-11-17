import logging
import argparse
import z3

from omt.utils.opt_parser import OMTParser
from omt.omtbv.opt_with_iterative_search import optimize_with_linear_search, \
    optimize_with_binary_search
from omt.omtbv.omt_with_maxsat import optimize_with_maxsat
from omt.omtbv.opt_with_qsmt import opt_with_qsmt
from omt.utils.z3opt_utils import optimize_as_long

logger = logging.getLogger(__name__)


def solve_opt_file(filename: str, solver_name: str):
    s = OMTParser()
    s.parse_with_z3(filename, is_file=True)
    # print(s.objectives)
    fml = z3.And(s.assertions)
    obj = s.objectives[0]
    # print(fml, obj)
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


def main():
    parser = argparse.ArgumentParser(description="Solve OMT(BV) problems with different solvers.")
    parser.add_argument("filename", type=str, help="The filename of the problem to solve.")
    parser.add_argument("--solver", type=str, default="z3",
                        choices=["z3", "cvc5", "btor", "yices2", "mathsat", "bitwuzla", "obv-bs"],
                        help="Choose the solver to use.")
    parser.add_argument("--seed", type=int, default=1, help="Random seed.")
    parser.add_argument("--log-level", type=str, default="INFO",
                        choices=["DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"],
                        help="Set the logging level.")

    args = parser.parse_args()

    logging.basicConfig(level=getattr(logging, args.log_level.upper(), None))

    solve_opt_file(args.filename, args.solver)


if __name__ == "__main__":
    main()
