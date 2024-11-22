"""Utils for manipulating values"""
import re


# Regular expressions used by the solver
RE_GET_EXPR_VALUE_ALL = re.compile(
    r"\(([a-zA-Z0-9_]*)[ \n\s]*(#b[0-1]*|#x[0-9a-fA-F]*|[(]?_ bv[0-9]* [0-9]*|true|false)\)"
)
RE_GET_EXPR_VALUE_FMT_BIN = re.compile(r"\(\((?P<expr>(.*))[ \n\s]*#b(?P<value>([0-1]*))\)\)")
RE_GET_EXPR_VALUE_FMT_DEC = re.compile(r"\(\((?P<expr>(.*))\ \(_\ bv(?P<value>(\d*))\ \d*\)\)\)")
RE_GET_EXPR_VALUE_FMT_HEX = re.compile(r"\(\((?P<expr>(.*))\ #x(?P<value>([0-9a-fA-F]*))\)\)")
RE_OBJECTIVES_EXPR_VALUE = re.compile(
    r"\(objectives.*\((?P<expr>.*) (?P<value>\d*)\).*\).*", re.MULTILINE | re.DOTALL
)


def convert_smtlib_models_to_python_value(v):
    """
    For converting SMT-LIB models to Python values
    TODO: we may need to deal with other types of variables,
       e.g., int, real, string, etc.
    """
    r = None
    if v == "true":
        r = True
    elif v == "false":
        r = False
    elif v.startswith("#b"):
        r = int(v[2:], 2)
    elif v.startswith("#x"):
        r = int(v[2:], 16)
    elif v.startswith("_ bv"):
        r = int(v[len("_ bv"): -len(" 256")], 10)
    elif v.startswith("(_ bv"):
        v = v[len("(_ bv"):]
        r = int(v[: v.find(" ")], 10)

    assert r is not None
    return r


def getvalue_bv(t):
    base = 2
    m = RE_GET_EXPR_VALUE_FMT_BIN.match(t)
    if m is None:
        m = RE_GET_EXPR_VALUE_FMT_DEC.match(t)
        base = 10
    if m is None:
        m = RE_GET_EXPR_VALUE_FMT_HEX.match(t)
        base = 16
    if m is None:
        raise Exception(f"I don't know how to parse the value {str(t)}")

    expr, value = m.group("expr"), m.group("value")  # type: ignore
    return int(value, base)


def getvalue_bool(t):
    return {"true": True, "false": False, "#b0": False, "#b1": True}[t[2:-2].split(" ")[1]]
