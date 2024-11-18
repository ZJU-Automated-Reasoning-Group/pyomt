"""Script for evaluating
    [f1, f2, ..., fn]
   TODO: 1. automatically load a config file that describes the different configurations
     of the solver omt_solver.py
     2. Run each of the configuration on a file and record all the results
"""
import os
import subprocess
import csv
import argparse
from tqdm import tqdm
from concurrent.futures import ThreadPoolExecutor, as_completed


def find_smt_files(directory):
    """Recursively find all SMT-LIB2 files in the given directory."""
    smt_files = []
    for root, _, files in os.walk(directory):
        for file in files:
            if file.endswith('.c'):
                smt_files.append(os.path.join(root, file))
    # print("total files: ", len(smt_files))
    return smt_files


def solve_file_with_omt_solver(file_path, args, timeout):
    result = {'file': file_path, 'stdout': '', 'stderr': '', 'status': 'UNKNOWN'}
    try:
        process = subprocess.run(
            ['python', file_path] + args,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            text=True
        )
        result['stdout'] = process.stdout
        result['stderr'] = process.stderr
    except subprocess.TimeoutExpired:
        result['stderr'] = 'Timeout expired'
    return result


def process_output(output):
    """Process the output (stdout + stderr) after running each instance?"""
    result = {'status': 'UNKNOWN', 'time': 0, 'optimal_val': 0}

    if 'Assertion' in output:
        result['status'] = 'FAILED'
    elif 'sat' in output:
        result['status'] = 'SUCCESSFUL'
    else:
        result['status'] = 'UNKNOWN'

    return result


def save_results_to_csv(results, csv_filename):
    """Save the processed results to a CSV file."""
    with open(csv_filename, mode='w', newline='') as csvfile:
        fieldnames = ['file', 'status', 'failed', 'unknown']
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)

        writer.writeheader()
        for result in results:
            writer.writerow({
                'file': result['file'],
                'status': result['status'],
                'time': result['time'],
                'optimal_val': result['optimal_val']
            })


def main_parallel(directory, args, timeout, csv_filename, parallel):
    smt_files = find_smt_files(directory)
    results = []

    if parallel:
        print("solving parallel")
        with ThreadPoolExecutor() as executor:
            futures = {executor.submit(solve_file_with_omt_solver, smt_file, args, timeout):
                           smt_file for smt_file in smt_files}
            for future in tqdm(as_completed(futures), total=len(smt_files),
                               desc="Processing files"):
                run_result = future.result()
                processed_result = process_output(run_result['stdout'] + run_result['stderr'])
                processed_result['file'] = run_result['file']
                results.append(processed_result)
    else:
        for smt_file in tqdm(smt_files, desc="Processing files"):
            run_result = solve_file_with_omt_solver(smt_file, args, timeout)
            processed_result = process_output(run_result['stdout'] + run_result['stderr'])
            processed_result['file'] = smt_file
            results.append(processed_result)

    save_results_to_csv(results, csv_filename)


def main(directory, args, timeout, csv_filename):
    smt_files = find_smt_files(directory)
    results = []

    for smt_file in tqdm(smt_files, desc="processing files"):
        run_result = solve_file_with_omt_solver(smt_file, args, timeout)
        processed_result = process_output(run_result['stdout'] + run_result['stderr'])
        processed_result['file'] = smt_file
        results.append(processed_result)

    save_results_to_csv(results, csv_filename)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Run 2ls on C files and save results.')
    parser.add_argument('directory', type=str, help='Directory to search for C files.')
    parser.add_argument('csv_filename', type=str, help='CSV file to save the results.')
    parser.add_argument('--timeout', type=int, default=10, help='Timeout for each  run in seconds.')
    parser.add_argument('--args', nargs=argparse.REMAINDER, default=[], help='Arguments for 2ls tool.')
    parser.add_argument('--parallel', action='store_true', help='Process files in parallel.')

    args = parser.parse_args()

    main(args.directory, args.args, args.timeout, args.csv_filename)
    # main_parallel(args.directory, args.args, args.timeout, args.csv_filename, args.parallel)

# Example usage:
# python3 tmp.py dir xx.csv --args --k-induction
