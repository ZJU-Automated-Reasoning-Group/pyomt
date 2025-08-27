"""OMT solver evaluation script."""
import os
import subprocess
import csv
import time
import argparse
from tqdm import tqdm
from concurrent.futures import ThreadPoolExecutor, as_completed


def find_smt_files(directory):
    """Find all .smt2 files recursively."""
    return [os.path.join(root, f) for root, _, files in os.walk(directory)
            for f in files if f.endswith('.smt2')]


def solve_file(file_path, args, timeout):
    """Run solver on file and return result."""
    try:
        result = subprocess.run(
            ['python3', '-m', 'pyomt.cli.pyomt', 'solve', file_path] + args,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout, text=True
        )
        return {'file': file_path, 'stdout': result.stdout, 'stderr': result.stderr}
    except subprocess.TimeoutExpired:
        return {'file': file_path, 'stdout': '', 'stderr': 'Timeout expired'}


def process_output(output):
    """Extract engine and solver info from output."""
    result = {'engine': '', 'solver': '', 'time': 0, 'stdout': output, 'stderr': ''}
    for line in output.split('\n'):
        if 'Linear search result:' in line:
            result.update({'engine': 'iter', 'solver': 'linear_search'})
        elif 'Binary search result:' in line:
            result.update({'engine': 'iter', 'solver': 'binary_search'})
        elif 'MaxSAT result:' in line:
            result['engine'] = 'maxsat'
        elif 'QSMT result:' in line:
            result['engine'] = 'qsmt'
    return result


def save_results_to_csv(results, csv_filename):
    """Save results to CSV."""
    with open(csv_filename, 'w', newline='') as f:
        writer = csv.DictWriter(f, ['file', 'engine', 'solver', 'time', 'stdout', 'stderr'])
        writer.writeheader()
        writer.writerows(results)


def run_evaluation(directory, args, timeout, parallel=False):
    """Run evaluation on all SMT files."""
    smt_files = find_smt_files(directory)
    results = []

    def process_file(smt_file):
        run_result = solve_file(smt_file, args, timeout)
        processed_result = process_output(run_result['stdout'] + run_result['stderr'])
        processed_result['file'] = smt_file
        return processed_result

    if parallel:
        print("Running parallel evaluation")
        with ThreadPoolExecutor() as executor:
            futures = [executor.submit(process_file, f) for f in smt_files]
            results = [f.result() for f in tqdm(as_completed(futures), total=len(smt_files), desc="Processing")]
    else:
        results = [process_file(f) for f in tqdm(smt_files, desc="Processing")]

    return results


def main(directory, config, csv_filename, timeout):
    """Main evaluation function using config file."""
    with open(config) as f:
        configs = [line.strip().split() for line in f if line.strip()]

    results = []
    for smt_file in tqdm(find_smt_files(directory), desc="Processing files"):
        for config_line in configs:
            engine, solver = config_line[0], config_line[-1]
            solve_args = ['--engine=z3py'] if engine == 'z3py' else \
                        [f'--engine={engine}', f'--solver-{engine}={solver}']

            start = time.time()
            run_result = solve_file(smt_file, solve_args, timeout)
            elapsed = time.time() - start

            results.append({
                'file': smt_file, 'engine': engine, 'solver': solver, 'time': elapsed,
                'stdout': run_result['stdout'], 'stderr': run_result['stderr']
            })

    save_results_to_csv(results, csv_filename)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='OMT solver evaluation')
    parser.add_argument('directory', help='Directory with SMT-LIB2 files')
    parser.add_argument('config', help='Configuration file')
    parser.add_argument('csv_filename', help='Output CSV file')
    parser.add_argument('--timeout', type=int, default=10, help='Timeout in seconds (default: 10)')

    args = parser.parse_args()
    main(args.directory, args.config, args.csv_filename, args.timeout)