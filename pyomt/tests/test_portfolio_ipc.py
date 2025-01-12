import time
import multiprocessing as mp
from pyomt.utils.portfolio_ipc import Portfolio, TimeoutException, ControlCommand


def solver_with_progress(x: int) -> int:
    # Simulated solver that reports progress
    for i in range(10):
        time.sleep(0.5)
        intermediate = x * (i + 1)
        yield intermediate
    return x * 10


if __name__ == '__main__':
    # Proper module-level protection
    mp.freeze_support()  # Needed for Windows

    with Portfolio(timeout=10.0, status_interval=0.5) as portfolio:
        try:
            # Your solver code here...
            result = portfolio.solve([solver_with_progress], args=(10,))
            print(f"Final result: {result}")
        except TimeoutException:
            print("Solver timed out")
        except Exception as e:
            print(f"Error: {e}")
