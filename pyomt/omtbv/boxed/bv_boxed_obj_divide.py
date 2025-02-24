"""
Objective-level divide-and-conquer for solving for boxed optimization over bit-vectors
1. Solve each objective in parallel
2. Combine the results

Possible improvements:
- Use different solver configurations for different objectives.
   - Linear search, binary search, QSMT, MaxSAT
   - Each of the above can be run with different configurations

FIXME: by LLM, to check if this is correct
"""

import multiprocessing as mp
from multiprocessing import Process, Queue, Value
from dataclasses import dataclass
from enum import Enum
import ctypes
import signal
from typing import Optional, Tuple, List, Dict, Any
import time
import logging
import os
import z3

from pyomt.omtbv.bv_opt_iterative_search import bv_opt_with_binary_search, bv_opt_with_linear_search
from pyomt.omtbv.bv_opt_qsmt import bv_opt_with_qsmt
from pyomt.omtbv.bv_opt_maxsat import bv_opt_with_maxsat

logger = logging.getLogger(__name__)

class SolverStatus(Enum):
    RUNNING = "running"
    COMPLETED = "completed"
    ERROR = "error"
    TIMEOUT = "timeout"

@dataclass
class ObjectiveResult:
    objective_id: int
    value: Optional[int]
    status: SolverStatus
    solve_time: float

def solve_objective(formula: z3.BoolRef, 
                   obj: z3.ExprRef,
                   obj_id: int,
                   minimize: bool,
                   engine: str,
                   solver_name: str,
                   result_queue: Queue,
                   error_queue: Queue):
    """Worker function to solve a single objective"""
    try:
        start_time = time.time()
        result = None

        if engine == "qsmt":
            result = bv_opt_with_qsmt(formula, obj, minimize, solver_name)
        elif engine == "maxsat":
            result = bv_opt_with_maxsat(formula, obj, minimize, solver_name)
        elif engine == "iter":
            solver_type = solver_name.split('-')[0]
            if solver_name.endswith("-ls"):
                result = bv_opt_with_linear_search(formula, obj, minimize, solver_type)
            elif solver_name.endswith("-bs"):
                result = bv_opt_with_binary_search(formula, obj, minimize, solver_type)

        solve_time = time.time() - start_time
        
        if result is None or result == "unknown":
            status = SolverStatus.ERROR
            value = None
        else:
            status = SolverStatus.COMPLETED
            value = int(result) if isinstance(result, (int, str)) else None
            
        obj_result = ObjectiveResult(obj_id, value, status, solve_time)
        result_queue.put(obj_result)
        
    except Exception as e:
        error_queue.put((obj_id, str(e)))

def solve_boxed_parallel(formula: z3.BoolRef,
                        objectives: List[z3.ExprRef],
                        minimize: bool = False,
                        engine: str = "qsmt",
                        solver_name: str = "z3",
                        timeout: float = 3600) -> List[Optional[int]]:
    """
    Solve multiple objectives in parallel using divide-and-conquer strategy
    
    Args:
        formula: The base formula (constraints)
        objectives: List of objectives to optimize
        minimize: Whether to minimize (True) or maximize (False)
        engine: Optimization engine ("qsmt", "maxsat", "iter")
        solver_name: Specific solver to use
        timeout: Maximum time in seconds for each objective
    
    Returns:
        List of optimal values (None for failed objectives)
    """
    result_queue = mp.Queue()
    error_queue = mp.Queue()
    processes = []
    results = [None] * len(objectives)

    # Start a process for each objective
    for i, obj in enumerate(objectives):
        p = Process(target=solve_objective,
                   args=(formula, obj, i, minimize, engine, solver_name, 
                         result_queue, error_queue))
        processes.append(p)
        p.start()

    # Collect results with timeout
    completed = 0
    start_time = time.time()
    
    try:
        while completed < len(objectives):
            if time.time() - start_time > timeout:
                logger.warning("Global timeout reached")
                break
                
            # Check for results
            try:
                result = result_queue.get_nowait()
                results[result.objective_id] = result.value
                completed += 1
                logger.info(f"Objective {result.objective_id} completed in {result.solve_time:.2f}s "
                          f"with value {result.value}")
            except mp.queues.Empty:
                pass

            # Check for errors
            try:
                obj_id, error_msg = error_queue.get_nowait()
                logger.error(f"Error in objective {obj_id}: {error_msg}")
                completed += 1
            except mp.queues.Empty:
                pass

            time.sleep(0.1)

    finally:
        # Clean up processes
        for p in processes:
            if p.is_alive():
                p.terminate()
                p.join(timeout=1)
                if p.is_alive():
                    os.kill(p.pid, signal.SIGKILL)

    return results

def demo():
    """Demo usage of parallel boxed optimization"""
    x = z3.BitVec('x', 8)
    y = z3.BitVec('y', 8)
    
    # Create a simple formula with two objectives
    formula = z3.And(x >= 0, y >= 0, x + y <= 10)
    objectives = [x, y]
    
    # Try different engines
    engines = [
        ("qsmt", "z3"),
        ("maxsat", "FM"),
        ("iter", "z3-ls")
    ]
    
    for engine, solver in engines:
        print(f"\nTrying {engine} engine with {solver} solver:")
        try:
            results = solve_boxed_parallel(formula, objectives, False, engine, solver)
            print(f"Results: {results}")
        except Exception as e:
            print(f"Error: {e}")

if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    demo()

