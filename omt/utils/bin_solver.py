"""
For calling bin solvers
"""
import os
from typing import List
import subprocess
from threading import Timer
import logging
import uuid

import z3

from omt.config import \
    z3_exec, cvc5_exec, g_bin_solver_timeout, \
    btor_exec, bitwuzla_exec, yices_exec, math_exec, q3b_exec

logger = logging.getLogger(__name__)


def terminate(process, is_timeout: List):
    """
    Terminates a process and sets the timeout flag to True.
    process : subprocess.Popen
        The process to be terminated.
         is_timeout : List
    A list containing a single boolean item. If the process exceeds the timeout limit, the boolean item will be
    set to True.
    """
    if process.poll() is None:
        try:
            process.terminate()
            is_timeout[0] = True
        except Exception as ex:
            print("error for interrupting")
            print(ex)


def solve_with_bin_smt(logic: str, qfml: z3.ExprRef, solver_name: str):
    """Call bin SMT solvers to solve exists forall
    In this version, we create a temp file, and ...
    """
    logger.debug("Solving QSMT via {}".format(solver_name))
    fml_str = "(set-logic {})\n".format(logic)
    s = z3.Solver()
    s.add(qfml)
    fml_str += s.to_smt2()
    print(fml_str)
    tmp_filename = "/tmp/{}_temp.smt2".format(str(uuid.uuid1()))
    tmp = open(tmp_filename, "w")
    try:
        tmp.write(fml_str)
        tmp.close()
        if solver_name == "z3":
            cmd = [z3_exec, tmp_filename]
        elif solver_name == "cvc5":
            cmd = [cvc5_exec, "-q", "--produce-models", tmp_filename]
        elif solver_name == "btor" or solver_name == "boolector":
            cmd = [btor_exec, tmp_filename]
        elif solver_name == "yices2":
            cmd = [yices_exec, tmp_filename]
        elif solver_name == "mathsat":
            cmd = [math_exec, tmp_filename]
        elif solver_name == "bitwuzla":
            cmd = [bitwuzla_exec, tmp_filename]
        elif solver_name == "q3b":
            cmd = [q3b_exec, tmp_filename]
        else:
            print("Can not find corresponding solver")
            cmd = [z3_exec, tmp_filename]
        print(cmd)
        p_gene = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        is_timeout_gene = [False]
        timer_gene = Timer(g_bin_solver_timeout, terminate, args=[p_gene, is_timeout_gene])
        timer_gene.start()
        out_gene = p_gene.stdout.readlines()
        out_gene = ' '.join([str(element.decode('UTF-8')) for element in out_gene])
        p_gene.stdout.close()  # close?
        timer_gene.cancel()

        if p_gene.poll() is None:
            p_gene.terminate()  # TODO: need this?

        if is_timeout_gene[0]:
            return "unknown"
        elif "unsat" in out_gene:
            return "unsat"
        elif "sat" in out_gene:
            return "sat"
        else:
            return "unknown"
    finally:
        tmp.close()

    if os.path.isfile(tmp_filename):
        os.remove(tmp_filename)


def demo_solver():
    cmd = [cvc5_exec, "-q", "--produce-models", 'tmp.smt2']
    p_gene = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    is_timeout_gene = [False]
    timer_gene = Timer(g_bin_solver_timeout, terminate, args=[p_gene, is_timeout_gene])
    timer_gene.start()
    out_gene = p_gene.stdout.readlines()
    out_gene = ' '.join([str(element.decode('UTF-8')) for element in out_gene])
    p_gene.stdout.close()  # close?
    timer_gene.cancel()
    if p_gene.poll() is None:
        p_gene.terminate()  # TODO: need this?

    print(out_gene)


if __name__ == "__main__":
    demo_solver()
