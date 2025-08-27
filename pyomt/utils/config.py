from pathlib import Path

project_root_dir = str(Path(__file__).parent.parent.parent)
z3_exec = project_root_dir + "/bin_solvers/z3"
cvc5_exec = project_root_dir + "/bin_solvers/cvc5"
btor_exec = project_root_dir + "/bin_solvers/boolector"
bitwuzla_exec = project_root_dir + "/bin_solvers/bitwuzla"
yices_exec = project_root_dir + "/bin_solvers/yices-smt2"
math_exec = project_root_dir + "/bin_solvers/mathsat"

q3b_exec = project_root_dir + "/bin_solvers/q3b"

g_bin_solver_timeout = 30
g_enable_debug = False

g_omt_args = None
