import time
from pyomt.utils.portfolio import Portfolio


def solver1(x: int) -> int:
    time.sleep(2)
    return x * 2


def solver2(x: int) -> int:
    time.sleep(1)
    return x * 3


def solver3(x: int) -> int:
    time.sleep(3)
    return x * 4


if __name__ == '__main__':
    # Optional: explicitly set start method
    # mp.set_start_method('spawn')  # Use 'spawn' on all platforms

    with Portfolio(timeout=5.0) as portfolio:
        result = portfolio.solve([solver1, solver2, solver3], args=(10,))
        print(f"Result: {result}")