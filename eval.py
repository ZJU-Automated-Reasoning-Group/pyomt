"""Script for evaluating
    [f1, f2, ..., fn]
   TODO: 1. automatically load a config file that describes the different configurations
     of the solver omt_solver.py
     2. Run each of the configuration on a file and record all the results
"""
import os
import subprocess
import csv
import time
import argparse
from tqdm import tqdm
from concurrent.futures import ThreadPoolExecutor, as_completed


def find_smt_files(directory):
    """Recursively find all SMT-LIB2 files in the given directory."""
    smt_files = []
    for root, _, files in os.walk(directory):
        for file in files:
            if file.endswith('.smt2'):
                smt_files.append(os.path.join(root, file))
    # print("total files: ", len(smt_files))
    return smt_files


def solve_file_with_omt_solver(file_path, args, timeout):
    result = {'file': file_path, 'stdout': '', 'stderr': ''}
    try:
        process = subprocess.run(
            ['python3', 'omt_solver.py', file_path] + args,
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


def save_results_to_csv(results, csv_filename):
    """Save the processed results to a CSV file."""
    with open(csv_filename, mode='w', newline='') as csvfile:
        fieldnames = ['file', 'engine', 'solver', 'time', 'stdout', 'stderr']
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)

        writer.writeheader()
        for result in results:
            writer.writerow({
                'file': result['file'],
                'engine': result['engine'],
                'solver': result['solver'],
                'time': result['time'], 
                'stdout': result['stdout'],
                'stderr': result['stderr']
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


def main(directory, config, csv_filename, timeout):
    smt_files = find_smt_files(directory)
    results = []

    with open(config) as f:
        args_list = f.read().strip().split('\n')

    for smt_file in tqdm(smt_files, desc="processing files"):
        for args in args_list:
            processed_result = {'file': smt_file, 
                                'engine': args.split()[0], 
                                'solver': args.split()[-1], 
                                'time': 0, 
                                'stdout': '',
                                'stderr': ''
                                }
            if processed_result['engine'] == 'z3py':
                solve_args = ['--engine=z3py']
            else:
                solve_args = ['--engine=' + processed_result['engine'], 
                            '--solver-'+ processed_result['engine'] + '=' + processed_result['solver']]
            start = time.time()
            run_result = solve_file_with_omt_solver(smt_file, solve_args, timeout)
            processed_result['time'] = time.time() - start
            processed_result['stdout'] = run_result['stdout']
            processed_result['stderr'] = run_result['stderr']
            results.append(processed_result)

    save_results_to_csv(results, csv_filename)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Perform Evaluation on OMT solvers and save results.')
    parser.add_argument('directory', type=str, help='Directory to search for SMT-LIB2 files.')
    parser.add_argument('config', type=str, help='Configuration for OMT solvers Evaluation.')
    parser.add_argument('csv_filename', type=str, help='CSV file to save the results.')
    parser.add_argument('--timeout', type=int, default=10, help='Timeout for each run in seconds.')
    parser.add_argument('--args', nargs=argparse.REMAINDER, default=[], help='Arguments for OMT solvers.')
    parser.add_argument('--parallel', action='store_true', help='Process files in parallel.')

    args = parser.parse_args()

    main(args.directory, args.config, args.csv_filename, args.timeout)
    # main_parallel(args.directory, args.args, args.timeout, args.csv_filename, args.parallel)

# Example usage:
# python3 eval.py regress eval_config result.csv --timeout=5