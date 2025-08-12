#!/usr/bin/env python3
"""
OMT (Optimization Modulo Theory) Command Line Interface
Supports multiple optimization engines and solvers for OMT(BV) problems.
"""
import logging
import click
import z3

from pyomt.omtbv.bv_opt_iterative_search import (
    bv_opt_with_linear_search,
    bv_opt_with_binary_search,
)
from pyomt.omtbv.bv_opt_maxsat import bv_opt_with_maxsat
from pyomt.omtbv.bv_opt_qsmt import bv_opt_with_qsmt
from pyomt.utils.opt_parser import OMTParser


logger = logging.getLogger("pyomt.cli")


def setup_logging(log_level: str) -> None:
    logging.basicConfig(
        level=getattr(logging, log_level.upper()),
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    )


def solve_opt_file(filename: str, engine: str, solver_name: str) -> None:
    """Solve a single-objective OMT(BV) problem from a file using the selected engine.

    The parser normalizes all objectives to maximization.
    """
    s = OMTParser()
    s.parse_with_z3(filename, is_file=True)

    fml = z3.And(s.assertions)
    obj = s.objective

    if engine == "iter":
        solver_type = solver_name.split('-')[0]
        search_type = solver_name.split('-')[-1]
        if search_type == 'ls':
            lin_res = bv_opt_with_linear_search(fml, obj, minimize=False, solver_name=solver_type)
            logger.info("Linear search result: %s", lin_res)
        elif search_type == 'bs':
            bin_res = bv_opt_with_binary_search(fml, obj, minimize=False, solver_name=solver_type)
            logger.info("Binary search result: %s", bin_res)
        else:
            logger.warning("Unknown iterative search type: %s", search_type)
    elif engine == 'maxsat':
        maxsat_res = bv_opt_with_maxsat(fml, obj, minimize=False, solver_name=solver_name)
        logger.info("MaxSAT result: %s", maxsat_res)
    elif engine == 'qsmt':
        qsmt_res = bv_opt_with_qsmt(fml, obj, minimize=False, solver_name=solver_name)
        logger.info("QSMT result: %s", qsmt_res)
    elif engine == "z3py":
        opt = z3.Optimize()
        opt.from_file(filename=filename)
        if opt.check() == z3.sat:
            print("Solution found:")
            model = opt.model()
            for decl in model:
                print(f"{decl} = {model[decl]}")
        else:
            print("No solution")
    else:
        logger.warning("No result - invalid engine specified: %s", engine)


@click.group(name="omt")
@click.option(
    '--log-level',
    type=click.Choice(['DEBUG', 'INFO', 'WARNING', 'ERROR', 'CRITICAL'], case_sensitive=False),
    default='INFO',
    help='Set logging level',
)
def omt_cli(log_level: str) -> None:
    """PyOMT Solver - Command line interface for Optimization Modulo Theory"""
    setup_logging(log_level)


@omt_cli.command(name="solve")
@click.argument('filename', type=click.Path(exists=True))
@click.option('--engine', type=click.Choice(['qsmt', 'maxsat', 'iter', 'z3py']), default='qsmt',
              help='Choose the solving engine')
@click.option('--solver-qsmt', type=click.Choice(['z3', 'cvc5', 'yices', 'msat', 'bitwuzla', 'q3b']),
              default='z3', help='QSMT solver selection')
@click.option('--solver-maxsat', type=click.Choice(['FM', 'RC2', 'OBV-BS']),
              default='FM', help='MaxSAT solver selection')
@click.option('--solver-iter',
              type=click.Choice([i + '-ls' for i in ["z3", "cvc5", "yices", "msat", "btor"]] +
                                [i + '-bs' for i in ["z3", "cvc5", "yices", "msat", "btor"]]),
              default='z3-ls', help='Iterative solver selection (ls=linear, bs=binary)')
# Optimization General Options (parsed for parity; not applied here)
@click.option('--opt-priority', type=click.Choice(['box', 'lex', 'par']), default='box',
              help='Multi-objective priority: box (default), lex, par')
# Boxed-Search Options
@click.option('--opt-box-engine', type=click.Choice(['seq', 'compact', 'par']), default='seq',
              help='Boxed optimization engine: seq (default), compact, par')
@click.option('--opt-box-shuffle', is_flag=True, default=False,
              help='Optimize objectives in random order (default: false)')
# Theory Options
@click.option('--opt-theory-bv-engine', type=click.Choice(['qsmt', 'maxsat', 'iter']), default='qsmt')
@click.option('--opt-theory-int-engine', type=click.Choice(['qsmt', 'iter']), default='qsmt')
@click.option('--seed', type=int, default=1, help='Random seed')
def solve(
    filename: str,
    engine: str,
    solver_qsmt: str,
    solver_maxsat: str,
    solver_iter: str,
    opt_priority: str,
    opt_box_engine: str,
    opt_box_shuffle: bool,
    opt_theory_bv_engine: str,
    opt_theory_int_engine: str,
    seed: int,
) -> None:
    """Solve an OMT problem from a file."""
    # Select the solver according to the engine
    if engine == "qsmt":
        solver = solver_qsmt
    elif engine == "maxsat":
        solver = solver_maxsat
    elif engine == "iter":
        solver = solver_iter
    elif engine == "z3py":
        solver = "z3py"
    else:
        raise click.BadParameter("Invalid engine specified")

    # Currently, ancillary options are parsed for parity but not yet wired.
    logger.debug(
        "Options: priority=%s, box_engine=%s, box_shuffle=%s, bv_engine=%s, int_engine=%s, seed=%d",
        opt_priority, opt_box_engine, opt_box_shuffle, opt_theory_bv_engine, opt_theory_int_engine, seed,
    )

    solve_opt_file(filename, engine, solver)


if __name__ == '__main__':
    omt_cli()