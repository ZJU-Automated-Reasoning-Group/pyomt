#!/usr/bin/env python3
import click
import logging
import z3

from pyomt.omtbv.bv_opt_iterative_search import bv_opt_with_linear_search, bv_opt_with_binary_search
from pyomt.omtbv.bv_opt_maxsat import bv_opt_with_maxsat
from pyomt.omtbv.bv_opt_qsmt import bv_opt_with_qsmt
from pyomt.utils.opt_parser import OMTParser

# Configure logging
logger = logging.getLogger(__name__)

def setup_logging(log_level):
    """Configure logging with the specified level"""
    logging.basicConfig(
        level=getattr(logging, log_level.upper()),
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    )

@click.group()
@click.option('--log-level', type=click.Choice(['DEBUG', 'INFO', 'WARNING', 'ERROR', 'CRITICAL'], 
              case_sensitive=False), default='INFO', help='Set logging level')
def cli(log_level):
    """OMT(BV) Solver CLI - Solve optimization problems with different engines"""
    setup_logging(log_level)

@cli.command()
@click.argument('filename', type=click.Path(exists=True))
@click.option('--engine', type=click.Choice(['qsmt', 'maxsat', 'iter', 'z3py']), default='qsmt',
              help='Choose the solving engine')
@click.option('--solver-qsmt', type=click.Choice(['z3', 'cvc5', 'yices', 'msat', 'bitwuzla', 'q3b']),
              default='z3', help='QSMT solver selection')
@click.option('--solver-maxsat', type=click.Choice(['FM', 'RC2', 'OBV-BS']),
              default='FM', help='MaxSAT solver selection')
@click.option('--solver-iter', type=click.Choice([i + '-ls' for i in ["z3", "cvc5", "yices", "msat", "btor"]] +
                                                [i + '-bs' for i in ["z3", "cvc5", "yices", "msat", "btor"]]),
              default='z3-ls', help='Iterative solver selection')
def solve(filename, engine, solver_qsmt, solver_maxsat, solver_iter):
    """Solve an OMT problem from a file"""
    # Select appropriate solver based on engine
    solver = {
        'qsmt': solver_qsmt,
        'maxsat': solver_maxsat,
        'iter': solver_iter,
        'z3py': 'z3py'
    }.get(engine)
    
    if not solver:
        raise click.BadParameter(f"Invalid engine: {engine}")

    try:
        s = OMTParser()
        s.parse_with_z3(filename, is_file=True)
        fml = z3.And(s.assertions)
        obj = s.objective

        if engine == "iter":
            solver_type = solver.split('-')[0]
            search_type = solver.split('-')[-1]
            if search_type == 'ls':
                result = bv_opt_with_linear_search(fml, obj, minimize=False, solver_name=solver_type)
                logger.info(f"Linear search result: {result}")
            elif search_type == 'bs':
                result = bv_opt_with_binary_search(fml, obj, minimize=False, solver_name=solver_type)
                logger.info(f"Binary search result: {result}")
        
        elif engine == 'maxsat':
            result = bv_opt_with_maxsat(fml, obj, minimize=False, solver_name=solver)
            logger.info(f"MaxSAT result: {result}")
        
        elif engine == 'qsmt':
            result = bv_opt_with_qsmt(fml, obj, minimize=False, solver_name=solver)
            logger.info(f"QSMT result: {result}")
        
        elif engine == "z3py":
            opt = z3.Optimize()
            opt.from_file(filename=filename)
            if opt.check() == z3.sat:
                click.echo("Solution found:")
                model = opt.model()
                for decl in model:
                    click.echo(f"{decl} = {model[decl]}")
            else:
                click.echo("No solution")

    except Exception as e:
        logger.error(f"Error solving problem: {str(e)}")
        raise click.ClickException(str(e))

if __name__ == '__main__':
    cli()
    