import statistics
import time

from z3 import *

from omt.utils.z3expr_utils import get_expr_vars_z3default, get_expr_vars


def are_lists_identical(list1, list2):
    return sorted(list1) == sorted(list2)


def calculate_stats(numbers):
    # Filter out -1 values
    filtered_numbers = [num for num in numbers if num != -1]

    if not filtered_numbers:
        return {
            'average': None,
            'median': None,
            'variance': None
        }

    average = sum(filtered_numbers) / len(filtered_numbers)
    median = statistics.median(filtered_numbers)
    variance = statistics.variance(filtered_numbers) if len(filtered_numbers) > 1 else 0

    return {
        'average': average,
        'median': median,
        'variance': variance
    }


def default_fun(fml):
    try:
        start_time = time.time()
        vars = get_expr_vars_z3default(fml)
        elapsed_time = time.time() - start_time
        return elapsed_time, [str(v) for v in vars]
    except Exception as e:
        return -1, []


def new_fun(fml):
    try:
        start_time = time.time()
        vars = get_expr_vars(fml)
        elapsed_time = time.time() - start_time
        return elapsed_time, [str(v) for v in vars]
    except Exception as e:
        return -1, []


def process_smt_files(directory):
    default_data = []
    new_data = []

    for filename in os.listdir(directory):
        if filename.endswith(".smt2"):
            filepath = os.path.join(directory, filename)
            print(f"Processing {filepath}...")

            try:
                with open(filepath, 'r') as file:
                    smt_content = file.read()
                solver = Solver()
                solver.from_string(smt_content)

                fml = z3.And(solver.assertions())

                time_new, res_new = new_fun(fml)
                new_data.append(time_new)
                print("new api time: ", time_new)

                time_default, res_default = default_fun(fml)
                default_data.append(time_default)
                print("default api time:", time_default)
                if not are_lists_identical(res_new, res_default):
                    print("not identical!!!")
                    print(res_new, res_default)

            except Exception as e:
                print(f"Error processing {filename}: {e}")

    print("Default: ")
    print(calculate_stats(default_data))
    print("New: ")
    print(calculate_stats(new_data))

# process_smt_files("smt-bench-qsym/strip")
