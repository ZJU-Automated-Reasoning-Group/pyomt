"""
NOTICE: not used for now
"""

import shutil
from pathlib import Path

# list of solver names to check for executability
solver_names = {
    "z3": "z3",
    "cvc5": "cvc5",
    "yices2": "yices-smt2",
}


# https://stackoverflow.com/questions/6760685/creating-a-singleton-in-python
class Singleton(type):
    _instances = {}

    def __call__(cls, *args, **kwargs):
        if cls not in cls._instances:
            cls._instances[cls] = super(Singleton, cls).__call__(*args, **kwargs)
        return cls._instances[cls]


# Python3
class GlobalConfig(metaclass=Singleton):
    # loop through the solvers and find their executable paths using shutil.which()
    z3_exec, cvc5_exec, yices2_exec, sharp_sat_exec = None, None, None, None
    for name, exec_name in solver_names.items():
        # first, try to find the solvers in arlib/bin_solvers
        exec_path = str(Path(__file__).parent.parent.parent / "bin_solvers" / exec_name)
        if not shutil.which(exec_path):
            # in case the first step fails, try to find the solver in the system path.
            exec_path = shutil.which(exec_name)
        if name == "z3":
            z3_exec = exec_path
        elif name == "cvc5":
            cvc5_exec = exec_path
        elif name == "yices2":
            yices2_exec = exec_path
        elif name == "sharp_sat":
            sharp_sat_exec = exec_path
        else:
            continue


global_config = GlobalConfig()
