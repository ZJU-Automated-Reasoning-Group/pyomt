"""
Solve then in sequential (one-by-one)

FIXME: to check (this file is generated by LLM)
"""
import logging
import time
from typing import List, Optional, Union
import z3

from pyomt.omtarith.arith_opt_qsmt import arith_opt_with_qsmt

logger = logging.getLogger(__name__)

def solve_arith_boxed_sequential(formula: z3.BoolRef,
                               objectives: List[z3.ExprRef],
                               minimize: bool = False,
                               solver_name: str = "z3") -> List[Optional[Union[int, float]]]:
    """
    Solve multiple arithmetic objectives sequentially using boxed optimization strategy.
    
    Args:
        formula: The base formula (constraints)
        objectives: List of objectives to optimize
        minimize: Whether to minimize (True) or maximize (False) objectives
        solver_name: SMT solver to use
    
    Returns:
        List of optimal values for each objective
    """
    results = []
    current_formula = formula
    
    for i, obj in enumerate(objectives):
        logger.info(f"Optimizing objective {i+1}/{len(objectives)}: {obj}")
        start_time = time.time()
        
        # Check if objective is integer or real
        is_int = z3.is_int(obj)
        logger.debug(f"Objective {i+1} type: {'integer' if is_int else 'real'}")
        
        try:
            result = arith_opt_with_qsmt(current_formula, obj, minimize, solver_name)
            
            logger.info(f"Objective {i+1} optimization completed in {time.time() - start_time:.2f}s")
            
            if result is None or result == "unknown":
                logger.warning(f"Could not optimize objective {i+1}")
                results.append(None)
                continue
                
            # Parse result
            if isinstance(result, str):
                try:
                    if is_int:
                        value = int(float(result))
                    else:
                        value = float(result)
                    results.append(value)
                    # Add constraint to maintain this objective's value
                    current_formula = z3.And(current_formula, obj == value)
                except (ValueError, IndexError):
                    logger.error(f"Could not parse result: {result}")
                    results.append(None)
            else:
                # Numeric result
                results.append(result)
                # Add constraint to maintain this objective's value
                current_formula = z3.And(current_formula, obj == result)
                
        except Exception as e:
            logger.error(f"Error optimizing objective {i+1}: {str(e)}")
            results.append(None)
            
    return results

def demo():
    """Demo usage of sequential arithmetic optimization"""
    # Create variables
    x = z3.Real('x')
    y = z3.Real('y')
    z = z3.Int('z')
    
    # Create a mixed integer-real formula with multiple objectives
    formula = z3.And(x >= 0, y >= 0, z >= 0,
                    x + y <= 10,
                    z <= 5,
                    x + z <= 7)
    
    # Define objectives (mix of real and integer)
    objectives = [x, y, z]
    
    print("\nSolving mixed arithmetic optimization problem:")
    print(f"Formula: {formula}")
    print(f"Objectives: {objectives}")
    
    try:
        results = solve_arith_boxed_sequential(formula, objectives, minimize=True)
        print(f"Results: {results}")
    except Exception as e:
        print(f"Error: {e}")

if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    demo()

