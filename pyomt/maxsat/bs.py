"""
Implement Nadel's algorithm for OMT(BV) "Bit-Vector Optimization (TACAS'16)"

Key idea: OMT on unsigned BV can be seen as lexicographic optimization over the bits in the
bitwise representation of the objective, ordered from the most-significant bit (MSB)
to the least-significant bit (LSB).

Notice that, in this domain, this corresponds to a binary search over the space of the values of the objective

NOTE: we assume that each element in self.soft is a unary clause, i.e., self.soft is [[l1], [l2], ...]
"""
from typing import List
from pysat.solvers import Solver


def obv_bs(clauses, literals):
    """
    This is a binary search algorithm of bit-vector optimization.
    Args:
        clauses: the given constraints
        literals: literals listed in priority

    Returns: the maximum assignment of literals

    """
    result = []
    # sat_oracle = Solver(name=sat_engine_name, bootstrap_with=clauses, use_timer=True)
    s = Solver(bootstrap_with=clauses)
    if s.solve():
        m = s.get_model()
        # print(m)
    else:
        print('UNSAT')
        return result
    l = len(m)
    for lit in literals:
        if lit > l:
            '''If 'lit' is not in m, 'lit' can be assigned 0 or 1, to maximum the result, 'lit' is assigned 1.'''
            result.append(lit)
        else:
            if m[lit - 1] > 0:
                result.append(lit)
            else:
                result.append(lit)
                if s.solve(assumptions=result):
                    m = s.get_model()
                else:
                    result.pop()
                    result.append(-lit)
    # print(result)
    return result



def obv_bs_anytime(clauses, literals):
    """
    An anytime version of the binary search algorithm of bit-vector optimization.

    The algorithm will return the best solution found so far when it is interrupted.
    Args:
        clauses: the given constraints
        literals: literals listed in priority
    
    Strategies
    1. Set a time limit for the algorithm, and return the best solution found so far when the time is up.
    2. Set a limit of the number of conflicts in each SAT call (when deciding a bit, say, b3); set the bit b3 to 0 if the limit is reached and continue the search for b2, b1, etc.
    """
    # FIXME: IMPLEMENT THIS FUNCTION following the strategies above
    result = []
    s = Solver(bootstrap_with=clauses)
    if s.solve():
        m = s.get_model()
    else:
        print('UNSAT')
        return result
    l = len(m)
    for lit in literals:
        if lit > l:
            result.append(lit)
        else:
            if m[lit - 1] > 0:
                result.append(lit)
            else:
                result.append(lit)
                if s.solve(assumptions=result):
                    m = s.get_model()
                else:
                    result.pop()
                    result.append(-lit)
    return result

