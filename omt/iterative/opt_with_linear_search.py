import z3


def maximize_with_linear_search(self, obj: z3.ExprRef):
    """
    Linear Search based OMT (FIXME: change to use PySMT)
    """
    s = z3.Solver()
    s.add(self.formula)
    maximum = None
    if s.check() == z3.sat:
        maximum = s.model().eval(obj)
    while True:
        assumption = obj > maximum
        if s.check(assumption) == z3.unsat:
            break
        maximum = s.model().eval(obj)
        # print("current: ", maximum)
    return maximum
