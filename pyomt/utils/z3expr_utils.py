from z3 import *
from z3.z3util import get_vars


def get_expr_vars_z3default(exp):
    return get_vars(exp)


def get_expr_vars(exp):
    try:
        syms = set()
        stack = [exp]

        while stack:
            e = stack.pop()
            if is_app(e):
                if e.num_args() == 0 and e.decl().kind() == Z3_OP_UNINTERPRETED:
                    syms.add(e)
                else:
                    stack.extend(e.children())

        return list(syms)
    except Z3Exception as ex:
        print(ex)
        return False


