# coding: utf-8
"""
The uniformed interface for solving OMT(BV) problems
"""
import logging
# from enum import Enum
# from typing import List

import z3

from omt.qsmt.qsmt_bin_solvers import solve_with_bin_smt

logger = logging.getLogger(__name__)


class QSMTSolver:

    def __init__(self, logic: str, **kwargs):
        self.phi = None
        self.exists_vars = None
        self.forall_vars = None

        self.logic = logic

        self.seed = kwargs.get("seed", 1)  # random seed
        self.solver = kwargs.get("solver", "z3")

        self.initialized = False
        self.pysmt_solver = kwargs.get("pysmt_solver", "z3")

    def set_tactic(self, name: str):
        raise NotImplementedError

    def init(self, exist_vars, forall_vars, phi: z3.ExprRef):
        self.exists_vars = exist_vars
        self.forall_vars = forall_vars
        self.phi = phi
        self.initialized = True

    def dump_ef_smt_file(self, smt2_file_name: str):
        """Dump the constraint from the ef engine
        """
        fml_str = "(set-logic {})\n".format(self.logic)

        dump_strategy = 1
        if dump_strategy == 1:
            # there are duplicates in self.exists_vars???
            exits_vars_names = set()
            for v in self.exists_vars:
                name = str(v)
                if name not in exits_vars_names:
                    exits_vars_names.add(name)
                    fml_str += "(declare-const {0} {1})\n".format(v.sexpr(), v.sort().sexpr())

            quant_vars = "("
            for v in self.forall_vars:
                quant_vars += "({0} {1}) ".format(v.sexpr(), v.sort().sexpr())
            quant_vars += ")\n"

            quant_fml_body = "(and \n"
            s = z3.Solver()
            s.add(self.phi)
            # self.phi is in the form of
            #  and (Init, Trans, Post)
            assert (z3.is_app(self.phi))
            for fml in self.phi.children():
                quant_fml_body += "  {}\n".format(fml.sexpr())
            quant_fml_body += ")"

            fml_body = "(assert (forall {0} {1}))\n".format(quant_vars, quant_fml_body)
            fml_str += fml_body
            fml_str += "(check-sat)\n"
        else:
            # Another more direct strategy
            # But we cannot see the definition of the VC clearly
            sol = z3.Solver()
            sol.add(z3.ForAll(self.forall_vars, self.phi))
            fml_str += sol.to_smt2()

        tmp = open(smt2_file_name, "w")
        tmp.write(fml_str)
        tmp.close()

    def dump_qbf_file(self, qdimacs_file_name: str):
        """Dump to QBF formula"""
        assert self.logic == "BV" or self.logic == "UFBV"
        fml_manager = EFBVFormulaTranslator()
        qdimacs_str = fml_manager.to_qdimacs_str(self.phi, existential_vars=self.exists_vars,
                                                 universal_vars=self.forall_vars)
        tmp = open(qdimacs_file_name, "w")
        tmp.write(qdimacs_str)
        tmp.close()

    def dump_sat_file(self, dimacs_file_name: str):
        raise NotImplementedError

    def solve(self):
        """
        Solve formulas via different strategies
        """
        assert self.initialized
        print("EFSMT solver: {}".format(self.solver))
        # 1. Quantifier instantiation approach
        if self.solver == "z3":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "z3")
        elif self.solver == "cvc5":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "cvc5")
        elif self.solver == "btor":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "boolector2")
        elif self.solver == "yices2":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "yices2")
        elif self.solver == "mathsat":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "mathsat")
        elif self.solver == "bitwuzla":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "bitwuzla")

        # 2. Bit-blasting approach
        elif self.solver == "z3qbf":
            return self.solve_with_z3_qbf()
        elif self.solver == "caqe":
            return self.solve_with_third_party_qbf("caqe")
        # TODO: q3b (BDD-based), z3-based QE+SAT
        elif self.solver == "q3b":
            return solve_with_bin_smt(self.logic, self.exists_vars, self.forall_vars, self.phi, "q3b")
        elif self.solver == "z3sat":
            return self.solve_with_z3_sat()
        # third-party SAT solves (using pySAT)
        elif self.solver in ['cd', 'cd15', 'gc3', 'gc4', 'g3',
                             'g4', 'lgl', 'mcb', 'mpl', 'mg3',
                             'mc', 'm22', 'mgh']:
            return self.solve_with_third_party_sat(solver_name=self.solver)

        # 3. Simple cegis-based approach
        elif self.solver == "cegis":
            # TODO: other engines in pysmt
            print("solving via cegis_solver")
            return self.solve_with_simple_cegis()

        else:
            raise NotImplementedError

    def solve_with_simple_cegis(self) -> str:
        raise NotImplementedError


def demo_qsmt():
    import time
    x, y, z = z3.BitVecs("x y z", 16)
    # x, y, z = z3.Reals("x y z")
    fmla = z3.Implies(z3.And(y > 0, y < 10), y - 2 * x < 7)

    start = time.time()
    solver = QSMTSolver(logic="BV", solver="cegis")
    solver.init(exist_vars=[x], forall_vars=[y], phi=fmla)
    # solver.dump_cegis_smt_files()
    # print(solver.solve_with_z3_sat())
    print(solver.solve_with_third_party_sat(solver_name="cd"))
    print("time: ", time.time() - start)


if __name__ == '__main__':
    demo_qsmt()
