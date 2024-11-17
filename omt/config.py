from pathlib import Path

project_root_dir = str(Path(__file__).parent.parent)
z3_exec = project_root_dir + "/bin_solvers/bin/z3"
cvc5_exec = project_root_dir + "/bin_solvers/bin/cvc5-Linux"
btor_exec = project_root_dir + "/bin_solvers/bin/boolector"
bitwuzla_exec = project_root_dir + "/bin_solvers/bin/bitwuzla"
yices_exec = project_root_dir + "/bin_solvers/bin/yices-smt2"
math_exec = project_root_dir + "/bin_solvers/bin/mathsat"

q3b_exec = project_root_dir + "/bin_solvers/bin/q3b"

g_bin_solver_timeout = 30
g_enable_debug = False

g_omt_args = None
