"""
For calling binary solvers (SMT/MaxSAT) via subprocess.
"""
import os
import subprocess
import logging
import uuid
import tempfile
from typing import List

import z3

from pyomt.utils.config import (
    z3_exec, cvc5_exec, g_bin_solver_timeout,
    btor_exec, bitwuzla_exec, yices_exec, math_exec, q3b_exec
)

logger = logging.getLogger(__name__)


# Legacy terminate helper removed; we use subprocess.run(..., timeout=...).


def get_smt_solver_command(solver_name: str, tmp_filename: str) -> List[str]:
    """
    Get the command to run the specified solver.
    Args:
        solver_name (str): The name of the solver.
        tmp_filename (str): The temporary file name containing the SMT problem.

    Returns:
        List[str]: The command to execute the solver.
    """
    solvers = {
        "z3": [z3_exec, tmp_filename],
        "cvc5": [cvc5_exec, "-q", "--produce-models", tmp_filename],
        "btor": [btor_exec, tmp_filename],
        "yices": [yices_exec, tmp_filename],
        "mathsat": [math_exec, tmp_filename],
        "bitwuzla": [bitwuzla_exec, tmp_filename],
        "q3b": [q3b_exec, tmp_filename],
    }
    return solvers.get(solver_name, [z3_exec, tmp_filename])


def get_maxsat_solver_command(solver_name: str, tmp_filename: str) -> List[str]:
    """
    Get the command to run the specified solver.
    Args:
        solver_name (str): The name of the solver.
        tmp_filename (str): The temporary file name containing the SMT problem.

    Returns:
        List[str]: The command to execute the solver.
    """
    solvers = {
        "z3": [z3_exec, tmp_filename],
    }
    return solvers.get(solver_name, [z3_exec, tmp_filename])


def solve_with_bin_smt(logic: str, qfml: z3.ExprRef, obj_name: str, solver_name: str) -> str:
    """
    Call a binary SMT solver to solve quantified SMT problems.

    Args:
        logic: SMT-LIB logic to be used (e.g., "LIA", "LRA", "BV").
        qfml: The quantified formula to be solved.
        obj_name: The name/sexpr of the objective term to query via get-value.
        solver_name: Which solver to use (e.g., "z3", "cvc5").

    Returns:
        The solver's stdout if it contains "sat" or "unsat"; otherwise "unknown".
    """
    logger.debug("Solving QSMT via %s", solver_name)

    fml_str = "(set-option :produce-models true)\n"
    fml_str += f"(set-logic {logic})\n"
    solver = z3.Solver()
    solver.add(qfml)
    fml_str += solver.to_smt2()
    fml_str += f"(get-value ({obj_name}))\n"

    tmp_filename = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", suffix=".smt2", delete=False) as tmp:
            tmp.write(fml_str)
            tmp_filename = tmp.name

        cmd = get_smt_solver_command(solver_name, tmp_filename)
        logger.debug("Command: %s", cmd)

        try:
            run_result = subprocess.run(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=g_bin_solver_timeout,
                text=True,
            )
            out_gene = (run_result.stdout or "").strip()
        except subprocess.TimeoutExpired:
            logger.warning("SMT solver timed out after %ss: %s", g_bin_solver_timeout, cmd)
            return "unknown"

        if "unsat" in out_gene:
            return out_gene
        if "sat" in out_gene:
            return out_gene
        return "unknown"
    finally:
        if tmp_filename and os.path.isfile(tmp_filename):
            try:
                os.remove(tmp_filename)
            except OSError as ex:
                logger.warning("Failed to remove temp file %s: %s", tmp_filename, ex)


def solve_with_bin_maxsat(wcnf: str, solver_name: str) -> str:
    """
    Solve weighted MaxSAT via a binary solver.

    Args:
        wcnf: The problem instance in WCNF format as a string.
        solver_name: Which solver to invoke.

    Returns:
        The solver's stdout, or "unknown" on timeout/error.
    """
    logger.debug("Solving MaxSAT via %s", solver_name)

    tmp_filename = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", suffix=".wcnf", delete=False) as tmp:
            tmp.write(wcnf)
            tmp_filename = tmp.name

        cmd = get_maxsat_solver_command(solver_name, tmp_filename)
        logger.debug("Command: %s", cmd)

        try:
            run_result = subprocess.run(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=g_bin_solver_timeout,
                text=True,
            )
            return (run_result.stdout or "").strip()
        except subprocess.TimeoutExpired:
            logger.warning("MaxSAT solver timed out after %ss: %s", g_bin_solver_timeout, cmd)
            return "unknown"
    finally:
        if tmp_filename and os.path.isfile(tmp_filename):
            try:
                os.remove(tmp_filename)
            except OSError as ex:
                logger.warning("Failed to remove temp file %s: %s", tmp_filename, ex)


def demo_solver() -> None:
    cmd = [z3_exec, 'tmp.smt2']
    try:
        res = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=g_bin_solver_timeout,
            text=True,
        )
        print((res.stdout or "").strip())
    except subprocess.TimeoutExpired:
        print("unknown")


if __name__ == "__main__":
    demo_solver()
