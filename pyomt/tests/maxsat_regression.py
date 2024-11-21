#!/usr/bin/env python3

import argparse
import contextlib
import lzma
import os
import random
import subprocess
import sys
import time

import psutil

DEBUG = True  # Set to False to disable debug output

vars = 0
nb_hard_clauses = 0
nb_soft_clauses = 0
maximum_weight = 0
sum_of_weights = 0
wcnf_input_format = ""
clauses = []
model = []
optimum = -99999
solution = ""
solution_of_model_string = ""
model_cost_calculated = -99999
hard_clause_solution_string = ""
error_dict = {}
issue_dict = {}
additional_timeout_after_SIGTERM_before_sending_SIGKILL = 0  # is set by argparse


def prind(*args, **kwargs):
    """
    Print the given arguments if DEBUG is True.

    Args:
        *args: Variable length argument list.
        **kwargs: Arbitrary keyword arguments.

    Returns:
        None
    """
    if DEBUG:
        print(*args, **kwargs)


def reset_values():
    """
    Reset all global variables to their initial values.
    """
    global vars, nb_hard_clauses, nb_soft_clauses, maximum_weight, sum_of_weights, wcnf_input_format, clauses, model, optimum, solution, solution_of_model_string, model_cost_calculated, hard_clause_solution_string, error_dict, issue_dict
    vars = 0
    nb_hard_clauses = 0
    nb_soft_clauses = 0
    maximum_weight = 0
    sum_of_weights = 0
    wcnf_input_format = ""
    clauses = []
    model = ""
    optimum = -99999
    solution = ""
    solution_of_model_string = ""
    model_cost_calculated = -99999
    hard_clause_solution_string = ""
    error_dict = {}
    issue_dict = {}


def is_valid_file(arg):
    """
    Check if the given file path exists.

    Args:
        arg (str): The file path to check.

    Returns:
        None
    """
    if not os.path.exists(arg):
        print("The file %s does not exist." % arg)
        exit(1)


def parse_wcnf(filename):
    """
    Parses a WCNF file and extracts the clauses and weights.

    Args:
        filename (str): The path to the WCNF file.

    Returns:
        None
    """
    global sum_of_weights, clauses, wcnf_input_format, nb_hard_clauses, nb_soft_clauses, vars, maximum_weight
    hard_clause_indicator = "h"
    top = 0

    # Determine if the file is compressed based on the extension
    is_compressed = filename.endswith(".xz")

    # Open the file accordingly
    open_func = lzma.open if is_compressed else open

    with open_func(filename, "rt") as file:
        for line in file:
            line = line.strip()

            # Ignore comments
            if line.startswith("c") or line == "":
                continue

            if line.startswith("p"):
                temp_list = list(map(str, line.split()))
                if temp_list[1] == "wcnf" and len(temp_list) == 5:
                    top = int(temp_list[4])
                else:
                    print(
                        f"ERROR: Expected exactly three values to unpack but got: {len(temp_list)}",
                        file=sys.stderr,
                    )
                    exit(0)
                hard_clause_indicator = str(top)
                wcnf_input_format = "old"
                continue

            if line.startswith(hard_clause_indicator):
                # Parse hard clause
                clause = list(
                    map(int, line[len(hard_clause_indicator) + 1: -2].split())
                )
                nb_hard_clauses += 1
                weight = -1
            elif line[0].isdigit():
                # Parse soft clause (weighted)
                weight, *clause = map(int, line[:-2].split())
                sum_of_weights += weight
                if weight > maximum_weight:
                    maximum_weight = weight
                nb_soft_clauses += 1
            else:
                print("c WARNING: read in line (ignored): " + line)
                continue

            # maxVar = max(abs(lit) for lit in clause)
            maxVar = 0 if not clause else max(abs(lit) for lit in clause)
            if maxVar > vars:
                vars = maxVar
            clauses.append((weight, clause))
    if hard_clause_indicator == "h":
        wcnf_input_format = "new"


def parse_solution_MSE_format(solver_output):
    """
    Parse the solver output in MSE format and extract the solution, optimum, and model.

    Args:
        solver_output (str): The solver output in MSE format.

    Returns:
        None
    """
    global model, solution, optimum, error_dict, issue_dict
    # Reset Values
    model = "v"
    solution = "s"
    optimum = -99999

    lines = solver_output.split("\n")
    for line in lines:
        line = line.strip()
        # print(line)

        # Ignore comments
        if line.startswith("c") or line == "":
            continue

        # solution line
        if line.startswith("s "):
            sol = line[2:]
            if solution != "s":
                issue_dict["Multiple lines starting with s"] = 1
            if sol == "OPTIMUM FOUND":
                solution = "OPTIMUM FOUND"
            elif "optimum" in sol.lower():
                solution = "OPTIMUM FOUND"
                error_dict["{line} instead of s OPTIMUM FOUND."] = 1
            elif sol == "UNSATISFIABLE":
                solution = "UNSATISFIABLE"
            elif "unsat" in sol.lower():
                solution = "UNSATISFIABLE"
                error_dict["{line} instead of s UNSATISFIABLE."] = 1
            elif sol == "SATISFIABLE":
                solution = "SATISFIABLE"
            elif "satisfiable" in sol.lower():
                solution = "SATISFIABLE"
                error_dict["{line} instead of s SATISFIABLE."] = 1
            elif sol == "UNKNOWN":
                solution = "UNKNOWN"
            elif "unkn" in sol.lower():
                solution = "UNKNOWN"
                error_dict["{line} instead of s UNKNOWN."] = 1
            else:
                error_dict[
                    "'{line}' should be one of the following 's [OPTIMUM FOUND, UNSATISFIABLE, SATISFIABLE, UNKNOWN]'."
                ] = 1
            continue

        if line.startswith("o"):
            try:
                optimum = int(line[2:])

            except ValueError:
                error_dict[f"Invalid value for o: {line[2:]}"] = 1
                optimum = -1
            continue

        if line.startswith("v"):
            model = line[2:]
            continue
        issue_dict[f"Line doesn't start with c, s, o, v: {line[:15]} ... "] = 1
    # print("")
    # print(f"optimum: {optimum}")
    # print(f"solution: {solution}")
    if solution == "s":
        error_dict["No line starting with s"] = 1
        solution = ""
    if solution == "OPTIMUM FOUND" or solution == "SATISFIABLE":
        if optimum == -99999:
            error_dict["No line starting with o"] = 1
        elif optimum == "":
            error_dict["No optimum value given"] = 1
        if model == "v":
            error_dict["No line starting with v"] = 1
            model = ""
        elif model == "" and vars > 0:
            error_dict["No model given, but variables are in the formula."] = 1


def check_model(given_model=""):
    """
    Check if the given model satisfies the clauses.

    Args:
        given_model (str): The model to check. If not provided, the global model will be used.

    Returns:
        None
    """
    global solution_of_model_string, model_cost_calculated, error_dict, issue_dict, clauses
    if given_model == "":
        given_model = model

    if len(given_model) < vars:
        # print("Model: " + str(model) + " nbVars: " + str(vars))
        error_dict["Model with less variables than WCNF."] = 1
        solution_of_model_string = "MODEL ERROR"
        model_cost_calculated = ""
        return
    if len(given_model) > 2 * vars:
        issue_dict["Model with more than 2x variables than WCNF."] = 1

    index = -1
    model_cost_calculated = 0
    solution_of_model_string = "SATISFIABLE"
    # print(f"no clauses: {len(clauses)}")
    for weight, clause in clauses:
        index = index + 1
        sat = False
        for lit in clause:
            # print(str(weight) + " (" + str(int(model[abs(lit) - 1])) + " == " + str(lit > 0) + ") " + str(int(model[abs(lit) - 1]) == (lit > 0)))
            if int(given_model[abs(lit) - 1]) == int(lit > 0):
                sat = True
                break
        if sat is False:
            if weight == -1:
                # weight == -1 means hard clause
                # hard clause is not satisfiable
                # print("At least one HC is unsatisfiable" + str(clause) + " model: " + str(model))
                solution_of_model_string = "UNSATISFIABLE"
                model_cost_calculated = ""
                break
            # this soft clause is not satisfiable
            model_cost_calculated += weight
    # print(f"model_cost_calculated: {model_cost_calculated}, solution_of_model_string: {solution_of_model_string}")


def dump_wcnf(format):
    """
    Dump the clauses and weights in WCNF format.

    Args:
        format (str): The format of the WCNF file. Can be "old", "new", or "cnf".

    Returns:
        None
    """
    global sum_of_weights, vars, clauses, nb_hard_clauses
    if format == "old":
        print(
            "p wcnf "
            + str(vars)
            + " "
            + str(len(clauses))
            + " "
            + str(sum_of_weights + 1)
        )
        hard_clause_indicator = str(sum_of_weights + 1) + " "
    elif format == "new":
        hard_clause_indicator = "h "
    elif format == "cnf":
        print("p cnf " + str(vars) + " " + str(nb_hard_clauses))
        hard_clause_indicator = ""
    else:
        assert False, "ERROR: Wrong format: " + format

    for weight, clause in clauses:
        if weight == -1:
            print(hard_clause_indicator + " ".join(map(str, clause)) + " 0")
        elif format != "cnf":
            print(str(weight) + " " + " ".join(map(str, clause)) + " 0")


def write_to_file(filename, format, compress=True):
    """
    Write the clauses and weights to a file in the specified format.

    Args:
        filename (str): The path to the output file.
        format (str): The format of the output file. Can be "old", "new", or "cnf".
        compress (bool): Whether to compress the output file using LZMA compression. Default is True.

    Returns:
        None
    """
    open_func = lzma.open if compress else open
    if not filename.endswith(".xz"):
        filename = f"{filename}.xz" if compress else filename
    with open_func(filename, "wt") as file:
        with contextlib.redirect_stdout(file):
            dump_wcnf(format)


def check_if_hard_clauses_are_SAT(sat_solver, seed=None):
    """
    Check if the hard clauses are satisfiable using a SAT solver.

    Args:
        sat_solver (str): The path to the SAT solver executable.
        seed (int): The seed value for random number generation. If not provided, a random seed will be used.

    Returns:
        None
    """
    global nb_hard_clauses, hard_clause_solution_string
    if nb_hard_clauses == 0:
        hard_clause_solution_string = "SATISFIABLE"
        return
    if seed is None:
        seed = random.getrandbits(64)
    filename = "/tmp/" + str(seed) + ".cnf"
    write_to_file(filename, "cnf", False)
    solver_out = subprocess.run(
        sat_solver + " " + filename, shell=True, capture_output=True
    )
    os.remove(filename)
    if solver_out.returncode == 10:
        hard_clause_solution_string = "SATISFIABLE"
    elif solver_out.returncode == 20:
        hard_clause_solution_string = "UNSATISFIABLE"
    else:
        hard_clause_solution_string = "UNKNOWN"


def process_csv_file(file_path):
    """
    Process a CSV file.

    Args:
        file_path (str): The path to the CSV file.

    Returns:
        None
    """
    with open(file_path, "r") as file:
        input_text = file.read()

    lines = input_text.split("\n")
    headers = ""
    # Initialize a list to hold each row as a dictionary
    data_rows = []

    for line in lines:
        if line:
            if line.startswith("c "):
                continue
            if line.startswith("WCNFFile"):
                headers = line.split(", ")
                continue

            row_data = line.split(", ")

            # Create a dictionary for the row, pairing each header with its corresponding data point
            row_dict = dict(zip(headers, row_data))
            data_rows.append(row_dict)

    return data_rows


def create_wcnf_list(folder):
    """
    Creates a list of dictionaries containing WCNF file information from the given folder.

    Args:
        folder (str): The path to the folder containing the WCNF files.

    Returns:
        list: A list of dictionaries, where each dictionary contains the WCNF file information.

    """
    wcnf_list = []
    for file in os.listdir(folder):
        if file.endswith(".wcnf"):
            wcnf_list.append({"WCNFFile": file})
    return wcnf_list


def clear_terminal():
    """Clears the terminal screen."""
    # For Windows
    if os.name == "nt":
        _ = os.system("cls")
    # For Mac and Linux (here, os.name is 'posix')
    else:
        _ = os.system("clear")


def terminate_process_and_children(process):
    """
    Terminate a process and all its child processes.

    Args:
        process (psutil.Process): The process to terminate.

    Returns:
        tuple: A tuple containing the output of the process and a boolean indicating if any processes were killed.
    """
    killed = False
    try:
        parent = psutil.Process(process.pid)
    except psutil.NoSuchProcess:
        # The process does not exist anymore
        return (process.communicate(), killed)

    # Get child processes recursively
    children = parent.children(recursive=True)

    # Try to terminate all child processes (SIGTERM)
    for child in children:
        try:
            child.terminate()
        except psutil.NoSuchProcess:
            pass  # The process does not exist anymore

    process.terminate()
    # wait one additional second after sending SIGTERM before killing the process SIGKILL and all it's children
    # it sometimes didn't work sending SIGTERM / SIGKILL only to the parent process!!
    gone, alive = psutil.wait_procs(
        [parent] + children,
        timeout=additional_timeout_after_SIGTERM_before_sending_SIGKILL,
    )
    for p in alive:
        try:
            killed = True
            # os.kill(p.pid, signal.SIGKILL)
            p.kill()
        except ProcessLookupError:
            pass  # The process does not exist anymore

    return ((process.stdout.read(), process.stderr.read()), killed)


def run_solver_with_timeout(command, timeout):
    """
    Runs a solver command with a specified timeout.

    Args:
        command (str): The command to run.
        timeout (float): The maximum time (in seconds) to wait for the command to complete.

    Returns:
        tuple: A tuple containing the stdout, stderr, return code and information about the termination of the process.

    Raises:
        Exception: If the process exceeds the overall timeout.

    """
    # Start the solver process
    start_time = time.time()
    with subprocess.Popen(
            command, stdout=subprocess.PIPE, stderr=subprocess.PIPE
    ) as process:
        try:
            # Monitor the process to enforce the timeout
            while True:
                elapsed_time = time.time() - start_time
                return_code = process.poll()
                if return_code is not None:  # Process has terminated
                    stdout, stderr = process.communicate()  # Collect final outputs
                    break  # Exit the loop as process has terminated
                if (
                        elapsed_time > timeout
                ):  # Overall timeout, change it to your desired timeout
                    # print("Exception due to elapsed time:")
                    raise Exception("Overall Timeout Occured")
                time.sleep(0.01)
                stdout, stderr = process.communicate(timeout=timeout)
        except Exception:
            (stdout, stderr), killed = terminate_process_and_children(process)
            if killed:
                return stdout, stderr, process.returncode, -2
            return stdout, stderr, process.returncode, -1

    return stdout, stderr, process.returncode, 0


def update_dict(msg, dict):
    """
    Update the error/issue dictionary with the given message.

    Args:
    - msg: The error message string.
    - dict: The dictionary to update, where key is the error message and value is the count.
    """
    if msg in dict:
        dict[msg] += 1
    else:
        dict[msg] = 1
    return f"\t\t{msg}\n"


def run_solver_on_wcnfs(
        solver,
        wcnf_list,
        folder,
        timeout,
        upper_bound,
        max_weight,
        sat_solver,
        verbose,
        anytime,
):
    """
    Run the solver on a list of wcnf instances.

    Args:
        solver (list): List of solver commands.
        wcnf_list (list): List of wcnf instances.
        folder (str): Path to the folder containing the wcnf files.
        timeout (int): Timeout value in seconds.
        upper_bound (int): Upper bound value.
        max_weight (int): Maximum weight value.
        sat_solver (str): Path to the SAT solver.
        verbose (bool): Flag indicating whether to print verbose output.
        anytime (bool): Flag indicating whether to run anytime solvers.

    Returns:
        None
    """
    counter = 0
    error_counter = 0
    issue_counter = 0
    overall_instances = len(wcnf_list)
    skip_counter = {
        "path_non_existend": 0,
        "upper_bound_violation": 0,
        "max_weight_violation": 0,
        "hard_to_solve": 0,
    }
    global_error_dict = {}
    global_issue_dict = {}
    skip_string = ""

    # print(wcnf_list)

    for wcnf in wcnf_list[:]:
        # getting the absolute path and saving it:
        folder = os.path.abspath(folder) + "/"
        if not os.path.exists(folder + wcnf["WCNFFile"]):
            skip_counter["path_non_existend"] += 1
            print(f"ERROR: File {folder + wcnf['WCNFFile']} does not exist.")
            overall_instances -= 1
            wcnf_list.remove(wcnf)
            continue
        reset_values()
        parse_wcnf(folder + wcnf["WCNFFile"])
        if sum_of_weights > upper_bound:
            skip_counter["upper_bound_violation"] += 1
            overall_instances -= 1
            wcnf_list.remove(wcnf)
            continue
        if maximum_weight > max_weight:
            skip_counter["max_weight_violation"] += 1
            overall_instances -= 1
            wcnf_list.remove(wcnf)
            continue
        # if wcnf.get("HardToSolve", "") == "YES":
        #     skip_counter["hard_to_solve"] += 1
        #     overall_instances -= 1
        #     wcnf_list.remove(wcnf)
        #     continue

    for key, value in skip_counter.items():
        if value > 0:
            if skip_string == "":
                skip_string = f"Skipping files due to: {key}: {value};"
            else:
                skip_string += f", {key}: {value};"
    if skip_string != "":
        print(skip_string)

    print(f"\nStart searching in {overall_instances} instances for issues.\n")
    for wcnf in wcnf_list:
        if anytime:
            timeout = round(random.uniform(0.1, 1), 4)

        error_string = ""
        issue_string = ""
        certified_csv_result = False
        if wcnf.get("CertifiedResult", "") == "YES":
            certified_csv_result = True
        reset_values()
        parse_wcnf(folder + wcnf["WCNFFile"])
        if os.path.exists(sat_solver):
            check_if_hard_clauses_are_SAT(sat_solver)
        counter += 1
        sys.stdout.write(
            f"\rCOUNTER: [{counter}/{overall_instances}], next: {wcnf['WCNFFile']}        "
        )
        if '{}' in solver:
            command = []
            for arg in solver:
                command.append(arg.replace('{}', folder + wcnf["WCNFFile"]))
        else:
            command = solver + [folder + wcnf["WCNFFile"]]

        stdout, stderr, return_code, termination = run_solver_with_timeout(
            command, timeout
        )

        # termination: -1 == timeout, -2 == killed after an additional second
        if termination < 0 and not anytime:
            if (
                    int(wcnf.get("Variables", 50)) < 100
                    and int(wcnf.get("HardClauses", 50)) < 100
                    and int(wcnf.get("SoftClauses", 50)) < 50
            ) or os.path.getsize(folder + wcnf["WCNFFile"]) < 1024:
                update_dict("Solver timeout for a small instance", global_error_dict)
                error_string += f"\t\tSolver timeout after {timeout}s. WCNF with {vars} variables, {nb_hard_clauses} hard clauses and {nb_soft_clauses} soft clauses and file size {os.path.getsize(folder + wcnf['WCNFFile'])} Bytes.\n"
            elif termination == -1:
                update_dict(f"Solver timeout after {timeout}s", global_issue_dict)
                issue_string += f"\t\tSolver timeout after {timeout}s. WCNF with {vars} variables, {nb_hard_clauses} hard clauses and {nb_soft_clauses} soft clauses and file size {os.path.getsize(folder + wcnf['WCNFFile'])} Bytes.\n"
            elif termination == -2:
                update_dict(
                    f"Solver didn't react to SIGTERM (send after {timeout}s) so we had to send SIGKILL after {additional_timeout_after_SIGTERM_before_sending_SIGKILL} additional second(s)",
                    global_issue_dict,
                )
                issue_string += f"\t\tSolver didn't react to SIGTERM (send after {timeout}s) so we had to send SIGKILL after {additional_timeout_after_SIGTERM_before_sending_SIGKILL} additional second(s). WCNF with {vars} variables, {nb_hard_clauses} hard clauses and {nb_soft_clauses} soft clauses and file size {os.path.getsize(folder + wcnf['WCNFFile'])} Bytes.\n"
        elif termination == -2:
            update_dict(
                f"Solver didn't react to SIGTERM so we had to send SIGKILL after {additional_timeout_after_SIGTERM_before_sending_SIGKILL} additional second(s)",
                global_error_dict,
            )
            error_string += f"\t\tSolver didn't react to SIGTERM (send after {timeout}s) so we had to send SIGKILL after {additional_timeout_after_SIGTERM_before_sending_SIGKILL} additional second(s). WCNF with {vars} variables, {nb_hard_clauses} hard clauses and {nb_soft_clauses} soft clauses and file size {os.path.getsize(folder + wcnf['WCNFFile'])} Bytes.\n"

        if termination == 0 and return_code not in [0, 10, 20, 30]:
            if return_code > 0:
                error_string += update_dict(
                    f"Invalid solver exit code {return_code}", global_error_dict
                )
            else:
                update_dict(
                    f"Terminated by signal {-return_code}", global_error_dict
                )
                error_string += f"\t\tTerminated by signal {-return_code} -- e.g. 11 means segfault (SIGSEGV), list them with 'kill -l'.\n"
        elif termination != -2 and stderr and not stderr.isspace():
            stderr = stderr.decode("utf-8")
            issue_string += update_dict(
                f"Non empty stderr: {stderr[:15]} ...", global_issue_dict
            )

        ### TODO: could be added to make the rule strict! But then return_code in [0, 20, 30] the 0 should be removed
        # if return_code == 0:
        #     issue_string += update_dict(
        #         "exit code 0 --> (new MSE24 rules) should be that solver cannot find a solution.",
        #         issue_dict,
        #     )
        if not anytime and return_code == 10:
            issue_string += update_dict(
                "exit code 10 --> (new MSE24 rules) this means that the solver only found a non-optimal solution.",
                global_issue_dict,
            )

        if (
                (termination == 0 or (termination in [0, -1] and anytime))
                and return_code in [0, 20, 30]
        ) and (stdout is None or stdout == ""):
            error_string += update_dict(
                f"No stdout after terminating properly with return code {return_code}",
                global_error_dict,
            )
        elif (
                termination == 0 or (termination in [0, -1] and anytime)
        ) and return_code in [0, 20, 30]:
            stdout = stdout.decode("utf-8")
            parse_solution_MSE_format(stdout)

            # comparing return code with solution (s ...) string
            if (solution == "UNKNOWN") and return_code != 0:
                issue_string += update_dict(
                    f"exit code {return_code} --> should be 0 (new MSE24 rules), as solver claims UNKNOWN.",
                    global_issue_dict,
                )
            elif (solution == "SATISFIABLE") and return_code != 10:
                issue_string += update_dict(
                    f"exit code {return_code} --> should be 10 (new MSE24 rules), as solver claims SATISFIABLE.",
                    global_issue_dict,
                )
            elif (solution == "OPTIMUM FOUND") and return_code != 30:
                issue_string += update_dict(
                    f"exit code {return_code} --> should be 30 (new MSE24 rules), as solver claims OPTIMUM FOUND.",
                    global_issue_dict,
                )
            elif (solution == "UNSATISFIABLE") and return_code != 20:
                issue_string += update_dict(
                    f"exit code {return_code} --> should be 20 (new MSE24 rules), as solver claims UNSATISFIABLE.",
                    global_issue_dict,
                )

            # comparing the result from the SAT solver with solution (s ...) string
            if (
                    solution == "UNSATISFIABLE"
                    and hard_clause_solution_string == "SATISFIABLE"
            ):
                error_string += update_dict(
                    "Hard clauses are SATISFIABLE but the solver returned 's UNSATISFIABLE'.",
                    global_error_dict,
                )
            elif (
                    solution == "OPTIMUM FOUND" or solution == "SATISFIABLE"
            ) and hard_clause_solution_string == "UNSATISFIABLE":
                if anytime:
                    issue_string += update_dict(
                        f"Hard clauses are UNSATISFIABLE but the solver returned 's {solution}.",
                        global_issue_dict,
                    )
                else:
                    error_string += update_dict(
                        f"Hard clauses are UNSATISFIABLE but the solver returned 's {solution}'.",
                        global_error_dict,
                    )

            # handling the case in which we have a satisfiable modle line (v ...)
            if (
                    solution
                    and solution != ""
                    and solution != "UNSATISFIABLE"
                    and solution != "UNKNOWN"
                    and hard_clause_solution_string != "UNSATISFIABLE"
            ):
                check_model()
                cert_string = "certified" if certified_csv_result else "best found"
                if (
                        solution_of_model_string == "UNSATISFIABLE"
                ):  # the model is unsatisfiable
                    error_string += update_dict(
                        f"Provided model is UNSATISFIABLE but the solver returned '{solution}'.",
                        global_error_dict,
                    )
                elif (
                        solution_of_model_string == "SATISFIABLE"
                ):  # the model is satisfiable
                    if model_cost_calculated != optimum:
                        update_dict(
                            f"Solver claims {solution} but model-value and o-value represent different values.",
                            global_error_dict,
                        )
                        error_string += f"\t\tSolver claims {solution} but model-value={model_cost_calculated} and o-value={optimum} represent different values ({cert_string} solution {wcnf['BestOValue']}).\n"
                    elif (
                            certified_csv_result
                            and solution == "OPTIMUM FOUND"
                            and (
                                    int(wcnf.get("BestOValue", optimum)) != optimum
                                    or int(wcnf.get("BestOValue", model_cost_calculated))
                                    != model_cost_calculated
                            )
                    ):
                        update_dict(
                            "Solver claims OPTIMUM FOUND but model-value and o-value represent a different value than the certified optimum.",
                            global_error_dict,
                        )
                        error_string += f"\t\tSolver claims OPTIMUM FOUND but model-value==o-value={model_cost_calculated} represent a different value than the certified solution {wcnf['BestOValue']}.\n"
                    elif solution == "OPTIMUM FOUND" and (
                            int(wcnf.get("BestOValue", optimum)) < optimum
                            or int(wcnf.get("BestOValue", model_cost_calculated))
                            < model_cost_calculated
                    ):
                        update_dict(
                            "Solver claims OPTIMUM FOUND but model-value and o-value represent a higher value than the best found solution.",
                            global_error_dict,
                        )
                        if (
                                len(wcnf.get("Model", "")) > 30
                                and len(wcnf.get("Model", "")) != ""
                        ):
                            error_string += f"\t\tSolver claims OPTIMUM FOUND but model-value==o-value={model_cost_calculated} represent a higher value than the best found solution {wcnf['BestOValue']}.\n"
                        else:
                            error_string += f"\t\tSolver claims OPTIMUM FOUND but model-value==o-value={model_cost_calculated} represents a higher value than the best found solution {wcnf['BestOValue']} with corresponding model {wcnf['Model']}.\n"

            for key, value in error_dict.items():
                error_string += f"\t\t{key}\n"
                if key in global_error_dict:
                    global_error_dict[key] += value
                else:
                    global_error_dict[key] = value
            # check for issues
            # print("")
            # print(wcnfTool.issue_dict)
            for key, value in issue_dict.items():
                issue_string += f"\t\t{key}\n"
                if key in global_issue_dict:
                    global_issue_dict[key] += value
                else:
                    global_issue_dict[key] = value
        if error_string != "" or (verbose and issue_string != ""):
            print("\n")  # due to the carriage return
        if error_string != "":
            error_counter += 1
            print(f"\tERROR DETECTED:\n{error_string}")
        if issue_string != "":
            issue_counter += 1
            if verbose:
                print(f"\tISSUE DETECTED:\n{issue_string}")
        if error_string != "" or (verbose and issue_string != ""):
            solver_call = ""
            for item in solver:
                solver_call += item + " "
            if anytime:
                print(
                    f"\tSolver call to reproduce error (SIGTERM should've been / was send after {timeout}): "
                )
            else:
                print(f"\tSolver call to reproduce error: ")

            print(f"\t\t{' '.join(command)}\n\n")
        # solver_call = ""
        # for item in solver:
        #     solver_call += item + " "
        # print(f"\t\t{solver_call}{folder}{wcnf['WCNFFile']}\n\n")
    sys.stdout.write(
        f"\rOverall Evaluation:                                                                                             \n"
    )
    if not global_error_dict and not global_issue_dict:
        print("\tCongratulations, no errors/issues found in the given solver.")
        return
    if global_error_dict:
        print(f"\tFound Errors in {error_counter}/{overall_instances} instances:")
        for key, value in global_error_dict.items():
            print(f"\t\t{key}: {value}")
    if global_issue_dict:
        print(f"\tFound Issues in {issue_counter}/{overall_instances} instances:")
        for key, value in global_issue_dict.items():
            print(f"\t\t{key}: {value}")


def main():
    """
    Check a list of wcnfs (with the expected o-value) if the solver runs without errors.

    Args:
        solver (str): Solver to run on the wcnfs. If you want to add arguments to the solver, put them in quotes.
        csv (str, optional): Path to csv file. Comma separated, must contain the columns "WCNFFile", "BestOValue" and if it contains unsatisfiable hard clauses it needs additionally the column "Satisfiable".
        folder (str, optional): Instead of a csv file you can also provide a folder. But then the o-value is not checked. But still crushing solver and the consistency of the model can be detected.
        timeout (int, optional): Solver timeout in seconds (default: 50).
        upperBound (int, optional): Run only wcnfs with a sum of weights smaller than this value (default: 2**60).
        maxWeight (int, optional): Run only wcnfs with that maximum weight (default: 2**63 - 1).
        satSolver (str, optional): Run a given SAT solver to check if the hard clauses are satisfiable (default location: "./kissat/build/kissat").
        verbose (bool, optional): Print issues after each instance.

    Returns:
        None
    """
    global additional_timeout_after_SIGTERM_before_sending_SIGKILL

    parser = argparse.ArgumentParser(
        description="Check a list of wcnfs (with the expected o-value) if the solver runs without errors."
    )
    parser.add_argument(
        "solver",
        type=str,
        help="Solver to run on the wcnfs. If you want to add arguments to the solver, put them in quotes. \
              If the wcnf instance should not be placed at the end use '{}' as a placeholder for the instance position.",
    )
    parser.add_argument(
        "--csv",
        type=str,
        # default="MSE22+23Unique.csv",
        default=None,
        help='csv file.\
                Comma separated, must contain the columns "WCNFFile". The other columns like \
                BestOValue, Satisfiable, CertifiedResult and Model are optional but can be used to check the solver output.',
    )
    parser.add_argument(
        "--folder",
        type=str,
        default=None,
        help="Instead of a csv file you can also provide a folder.\
                But then the o-value is not checked.\
                But still crushing solver and the consistency of the model can be detected.",
    )
    parser.add_argument(
        "--unweighted",
        action="store_true",
        help="Solve only instances with a maximal weight 1. (It overrides --maxweight and --csv)",
    )
    parser.add_argument(
        "--anytime",
        action="store_true",
        help="Solve all unique and anytime instances (doesn't use --timeout). Anytime solvers have (all) a short timeout between 0.1 and 1 seconds.",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=50,
        help="Solver timeout in seconds for exact solvers (default: %(default)s). Anytime solvers have (all) a short timeout between 0.1 and 1 seconds.",
    )
    parser.add_argument(
        "--upperBound",
        type=int,
        default=2 ** 60,
        help="Run only wcnfs with a sum of weights smaller than this value (default: %(default)s).",
    )
    parser.add_argument(
        "--maxWeight",
        type=int,
        default=2 ** 63 - 1,
        help="Run only wcnfs with that maximum weight (default: %(default)s).",
    )
    parser.add_argument(
        "--satSolver",
        type=str,
        default="./kissat/build/kissat",
        help="Run a given SAT solver to check if the hard clauses are satisfiable (default location: %(default)s).",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Print issues after each instance.",
    )
    parser.add_argument(
        "--SIGKILLTO",
        type=int,
        default=1,
        help="Additional timeout to wait after SIGTERM before SIGKILL is send.",
    )

    start_time = time.time()
    args = parser.parse_args()
    clear_terminal()
    print(f"{sys.argv[0]} 2024 by Tobias Paxian; run with --help for more information.")
    print(
        "Checks a list of wcnfs (with the expected o-value) if the solver runs without errors."
    )

    exit_code_description = (
        "\nSTARTING IN MSE 2024 --> the solver must return one of the following exit codes:\n"
        "\t0 \tif it cannot find a solution satisfying the hard clauses or prove unsatisfiability.\n"
        "\t10\tif the solver finds a solution satisfying the hard clauses but does not prove it to be unsatisfiabe.\n"
        "\t20\tif it finds that the hard clauses are unsatisfiable.\n"
        "\t30\tif it finds an optimal solution.\n"
    )
    print(exit_code_description)

    if not (os.path.isfile(args.satSolver) and os.access(args.satSolver, os.X_OK)):
        print(
            f"ERROR: The script needs a SAT solver to work properly. The given SAT solver '{args.satSolver}' does not exist."
        )
        print("Please provide a valid SAT solver with --satSolver.")
        print("You can install kissat (https://github.com/arminbiere/kissat) with: ")
        print(
            "\tgit clone https://github.com/arminbiere/kissat.git   or:  git clone git@github.com:arminbiere/kissat.git"
        )
        print("\tcd kissat")
        print("\t./configure && make test")
        exit(1)

    if args.csv is None and args.folder is None:
        args.csv = "MSE22+23Unique.csv"
        if args.anytime:
            args.csv = "MSE23Anytime.csv"
        if args.unweighted:
            args.maxWeight = 1
            args.csv = "allIssues.csv"

    additional_timeout_after_SIGTERM_before_sending_SIGKILL = args.SIGKILLTO

    # solver = shlex.split(args.solver)
    solver = args.solver.split()
    if args.folder and not args.folder.endswith("/"):
        args.folder += "/"

    is_valid_file(solver[0])
    if args.folder is None and not os.path.isfile(args.csv):
        print("Please provide either a csv file or a folder.")
        exit(1)

    if args.folder is None:
        is_valid_file(args.csv)
        wcnf_list = process_csv_file(args.csv)
        # for wcnf in wcnf_list:
        #     folder, wcnf["WCNFFile"] = os.path.split(wcnf["WCNFFile"])
        folder = ""
    else:
        wcnf_list = create_wcnf_list(args.folder)
        folder = args.folder

    run_solver_on_wcnfs(
        solver,
        wcnf_list,
        folder,
        args.timeout,
        args.upperBound,
        args.maxWeight,
        args.satSolver,
        args.verbose,
        args.anytime,
    )
    # print(wcnf_list)
    end_time = time.time()
    timing = end_time - start_time
    print(f"\nTotal runtime of script: {round(timing, 2)}s\n")


if __name__ == "__main__":
    main()
