import z3

from pyomt.utils.opt_parser import OMTParser


def test_opt_parser_parse_with_z3_minimize_bv_and_extract():
    smt = """
    (set-logic QF_BV)
    (declare-const x (_ BitVec 4))
    (assert (bvult x (_ bv5 4)))
    (minimize x)
    (check-sat)
    """
    p = OMTParser()
    p.to_max_obj = True
    p.to_min_obj = False
    p.parse_with_z3(smt, is_file=False)
    # Depending on z3 version, assertions() may return a list-like object; accept either
    assert isinstance(p.assertions, (list, tuple))
    assert p.objective is not None
    # Build back a formula and objective for sanity
    fml = z3.And(p.assertions)
    assert isinstance(fml, z3.BoolRef)

