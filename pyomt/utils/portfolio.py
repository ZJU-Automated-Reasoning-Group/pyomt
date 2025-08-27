"""
General utilities for portfolio solving

Basic Features:
 1. Run N processes in parallel for the same given input, with a timeout.
 2. Use the results from the first worker process that finishes and terminate all other workers.
    Also terminate all the processes (recursively) created by the worker processes.

3. If a worker process timeouts, terminate it and all processes (recursively) created by the worker.
4. If a worker process raises an exception, terminate it and all processes (recursively) created by the worker.

"""

import multiprocessing as mp
from multiprocessing import Process, Queue
import psutil
import time
from typing import Any, Callable, List
import sys


class PortfolioException(Exception):
    """Base exception for portfolio solver errors"""
    pass


class TimeoutException(PortfolioException):
    """Raised when portfolio solver times out"""
    pass


def terminate_process_tree(pid: int) -> None:
    """Recursively terminate a process and all its children"""
    try:
        parent = psutil.Process(pid)
        children = parent.children(recursive=True)
        
        # Terminate all processes
        for proc in children + [parent]:
            try:
                proc.terminate()
            except psutil.NoSuchProcess:
                pass
        
        # Wait and force kill if necessary
        gone, alive = psutil.wait_procs(children + [parent], timeout=3)
        for proc in alive:
            try:
                proc.kill()
            except psutil.NoSuchProcess:
                pass
    except psutil.NoSuchProcess:
        pass


def worker_wrapper(func: Callable, args: tuple, result_queue: Queue,
                   error_queue: Queue) -> None:
    """Wrapper for worker processes to handle exceptions"""
    try:
        result = func(*args)
        result_queue.put(result)
    except Exception as e:
        error_queue.put((type(e), str(e), sys.exc_info()[2]))


class Portfolio:
    def __init__(self, timeout: float = 60):
        self.timeout = timeout
        self._processes: List[Process] = []

    def _cleanup_processes(self):
        """Clean up all running processes"""
        for p in self._processes:
            if p.is_alive():
                terminate_process_tree(p.pid)
        self._processes.clear()

    def solve(self, solvers: List[Callable], args: tuple) -> Any:
        """
        Run multiple solvers in parallel and return first successful result

        Args:
            solvers: List of solver functions to run
            args: Arguments to pass to each solver

        Returns:
            Result from first successful solver

        Raises:
            TimeoutException: If no solver completes within timeout
            PortfolioException: If all solvers fail
        """
        result_queue = Queue()
        error_queue = Queue()

        # Start all worker processes
        for solver in solvers:
            p = Process(target=worker_wrapper,
                        args=(solver, args, result_queue, error_queue))
            self._processes.append(p)
            p.start()

        try:
            start_time = time.time()
            while True:
                # Check for results
                try:
                    return result_queue.get_nowait()
                except mp.queues.Empty:
                    pass

                # Check for errors
                try:
                    exc_type, exc_msg, exc_tb = error_queue.get_nowait()
                    raise exc_type(exc_msg)
                except mp.queues.Empty:
                    pass

                # Check timeout
                if time.time() - start_time > self.timeout:
                    raise TimeoutException("Portfolio solver timed out")

                time.sleep(0.01)  # Prevent busy waiting

        finally:
            self._cleanup_processes()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self._cleanup_processes()


# Module-level protection
if __name__ == '__main__':
    mp.freeze_support()
