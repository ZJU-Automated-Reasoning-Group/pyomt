"""
For quickly comparing the performance of different APIs
e.g., get_expr_vars_z3default, get_expr_vars
"""

import os
import statistics
import time
from typing import Callable, Any, Tuple, List
from z3 import *

from pyomt.utils.z3expr_utils import get_expr_vars_z3default, get_expr_vars

def calculate_stats(numbers):
    """Calculate basic statistics for a list of numbers"""
    if not numbers:
        return "No data available"
    filtered_numbers = [n for n in numbers if n >= 0]  # Remove error cases (-1)
    if not filtered_numbers:
        return "No valid data points"
    return {
        "count": len(filtered_numbers),
        "mean": statistics.mean(filtered_numbers),
        "median": statistics.median(filtered_numbers),
        "std_dev": statistics.stdev(filtered_numbers) if len(filtered_numbers) > 1 else 0
    }

def are_lists_identical(list1, list2):
    """Compare two lists for identical contents regardless of order"""
    if len(list1) != len(list2):
        return False
    return sorted(list1) == sorted(list2)


class APITester:
    def __init__(self, name: str, func: Callable):
        self.name = name
        self.func = func

    def run(self, fml) -> Tuple[float, List[str]]:
        try:
            start_time = time.time()
            result = self.func(fml)
            elapsed_time = time.time() - start_time
            return elapsed_time, [str(v) for v in result]
        except Exception as e:
            print(f"Error in {self.name}: {e}")
            return -1, []

def process_smt_files(directory: str, apis: List[APITester]):
    """
    Process SMT files using multiple APIs
    :param directory: Directory containing SMT2 files
    :param apis: List of APITesters to evaluate
    """
    results = {api.name: [] for api in apis}

    for filename in os.listdir(directory):
        if filename.endswith(".smt2"):
            filepath = os.path.join(directory, filename)
            print(f"Processing {filepath}...")

            try:
                with open(filepath, 'r') as file:
                    smt_content = file.read()
                solver = Solver()
                solver.from_string(smt_content)
                fml = And(solver.assertions())

                # Run each API and collect results
                api_results = []
                for api in apis:
                    time_taken, res = api.run(fml)
                    results[api.name].append(time_taken)
                    print(f"{api.name} time: {time_taken}")
                    api_results.append((api.name, res))

                # Compare results between APIs
                for i in range(len(api_results)):
                    for j in range(i + 1, len(api_results)):
                        if not are_lists_identical(api_results[i][1], api_results[j][1]):
                            print(f"Results not identical between {api_results[i][0]} and {api_results[j][0]}!")
                            print(f"{api_results[i][0]}: {api_results[i][1]}")
                            print(f"{api_results[j][0]}: {api_results[j][1]}")

            except Exception as e:
                print(f"Error processing {filename}: {e}")

    # Print statistics for each API
    print("\nPerformance Statistics:")
    print("-" * 50)
    for api_name, data in results.items():
        stats = calculate_stats(data)
        if isinstance(stats, dict):
            print(f"\n{api_name}:")
            print(f"  Total runs: {stats['count']}")
            print(f"  Mean time:  {stats['mean']:.6f} seconds")
            print(f"  Median:     {stats['median']:.6f} seconds")
            print(f"  Std dev:    {stats['std_dev']:.6f} seconds")
        else:
            print(f"\n{api_name}: {stats}")
    print("-" * 50)

# Example usage:
apis_to_test = [
    APITester("default", get_expr_vars_z3default),
    APITester("new", get_expr_vars),
    # Add more APIs here as needed
]

if __name__ == "__main__":
    process_smt_files("regress", apis_to_test)
    # process_smt_files("smt-bench-qsym/strip", apis_to_test)
