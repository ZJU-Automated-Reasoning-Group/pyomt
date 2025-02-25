#!/usr/bin/env python3
"""
MaxSAT Command Line Interface
Provides access to various MaxSAT solving engines and algorithms
# TODO: by LLM, to be checked.
"""
import click
import logging
import time
from pathlib import Path

from pysat.formula import WCNF
from pyomt.maxsat.maxsat_solver import MaxSATSolver, MaxSATEngine

logger = logging.getLogger("pyomt.cli.maxsat")

def setup_logging(log_level):
    """Configure logging with the specified level"""
    logging.basicConfig(
        level=getattr(logging, log_level.upper()),
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    )

@click.group()
@click.option('--log-level', type=click.Choice(['DEBUG', 'INFO', 'WARNING', 'ERROR', 'CRITICAL'], 
              case_sensitive=False), default='INFO', help='Set logging level')
def maxsat_cli(log_level):
    """PyOMT MaxSAT Solver - Command line interface for MaxSAT solving"""
    setup_logging(log_level)

@maxsat_cli.command()
@click.argument('filename', type=click.Path(exists=True))
@click.option('--engine', type=click.Choice(['FM', 'RC2', 'OBV-BS', 'OBV-BS-ANYTIME']), 
              default='FM', help='Choose MaxSAT solving engine')
@click.option('--timeout', type=float, default=3600.0, 
              help='Solving timeout in seconds (default: 1 hour)')
@click.option('--output', type=click.Path(), default=None,
              help='Output file for the solution')
def solve(filename, engine, timeout, output):
    """Solve a MaxSAT problem from a WCNF file"""
    try:
        # Load WCNF formula
        wcnf = WCNF(from_file=filename)
        
        # Initialize solver
        solver = MaxSATSolver(wcnf, timeout=timeout)
        solver.set_maxsat_engine(engine)
        
        # Solve and measure time
        start_time = time.time()
        result = solver.solve()
        solve_time = time.time() - start_time
        
        # Process results
        if result.status == "optimal":
            click.echo(f"Optimal solution found!")
            click.echo(f"Cost: {result.cost}")
            if result.solution:
                click.echo(f"Solution: {result.solution}")
                if output:
                    with open(output, 'w') as f:
                        f.write(f"c PyOMT MaxSAT Solution\n")
                        f.write(f"c Status: {result.status}\n")
                        f.write(f"c Cost: {result.cost}\n")
                        f.write(f"c Time: {solve_time:.2f}s\n")
                        f.write(f"v {' '.join(map(str, result.solution))}\n")
        else:
            click.echo(f"Status: {result.status}")
            if result.statistics and "error" in result.statistics:
                click.echo(f"Error: {result.statistics['error']}")
        
        click.echo(f"Solving time: {solve_time:.2f}s")
        
    except Exception as e:
        logger.error(f"Error solving MaxSAT problem: {str(e)}")
        raise click.ClickException(str(e))

@maxsat_cli.command()
@click.argument('filename', type=click.Path(exists=True))
def info(filename):
    """Display information about a WCNF file"""
    try:
        wcnf = WCNF(from_file=filename)
        click.echo(f"WCNF Formula Statistics:")
        click.echo(f"  Number of variables: {wcnf.nv}")
        click.echo(f"  Number of hard clauses: {len(wcnf.hard)}")
        click.echo(f"  Number of soft clauses: {len(wcnf.soft)}")
        if wcnf.wght:
            click.echo(f"  Weight range: [{min(wcnf.wght)}, {max(wcnf.wght)}]")
            click.echo(f"  Total weight: {sum(wcnf.wght)}")
    except Exception as e:
        logger.error(f"Error reading WCNF file: {str(e)}")
        raise click.ClickException(str(e))

@maxsat_cli.command()
def engines():
    """List available MaxSAT solving engines"""
    click.echo("Available MaxSAT Engines:")
    for engine in MaxSATEngine:
        click.echo(f"  {engine.value}")

if __name__ == '__main__':
    maxsat_cli()