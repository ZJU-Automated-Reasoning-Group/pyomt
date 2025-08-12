# RC2 algorithm implemented via Z3's Python API
# basic version with some optimizations
# - process soft constraints in order of highest values first.
# - extract multiple cores, not just one
# - use built-in cardinality constraints, cheap core minimization.
#
# See also https://github.com/pysathq/pysat and papers in CP 2014, JSAT 2015.

import sys
from typing import List, Dict, Tuple, Iterable, Set

import z3


def tt(s: z3.Solver, f: z3.ExprRef) -> bool:
    return z3.is_true(s.model().eval(f))


def add(Ws: Dict[z3.ExprRef, int], f: z3.ExprRef, w: int) -> None:
    Ws[f] = w + (Ws[f] if f in Ws else 0)


def sub(Ws: Dict[z3.ExprRef, int], f: z3.ExprRef, w: int) -> None:
    w1 = Ws[f]
    if w1 > w:
        Ws[f] = w1 - w
    else:
        del (Ws[f])


class RC2:

    def __init__(self, s: z3.Solver):
        self.bounds = {}
        self.names = {}
        self.solver = s
        self.solver.set("sat.cardinality.solver", True)
        self.solver.set("sat.core.minimize", True)
        self.solver.set("sat.core.minimize_partial", True)

    def at_most(self, S: List[z3.ExprRef], k: int) -> z3.ExprRef:
        fml = z3.simplify(z3.AtMost(S + [k]))
        if fml in self.names:
            return self.names[fml]
        name = z3.Bool("%s" % fml)
        self.solver.add(z3.Implies(name, fml))
        self.bounds[name] = (S, k)
        self.names[fml] = name
        return name

    def print_cost(self) -> None:
        print("cost [", self.min_cost, ":", self.max_cost, "]")

    def update_max_cost(self) -> None:
        self.max_cost = min(self.max_cost, self.get_cost())
        self.print_cost()

    # sort W, and incrementally add elements of W
    # in sorted order to prefer cores with high weight.
    def check(self, Ws: Dict[z3.ExprRef, int]) -> z3.CheckSatResult:
        def compare(fw):
            f, w = fw
            return -w

        ws = sorted([(k, Ws[k]) for k in Ws], key=compare)
        i = 0
        while i < len(ws):
            j = i
            # increment j until making 5% progress or exhausting equal weight entries
            while (j < len(ws) and ws[j][1] == ws[i][1]) or (i > 0 and (j - i) * 20 < len(ws)):
                j += 1
            i = j
            r = self.solver.check([ws[j][0] for j in range(i)])
            if r == z3.sat:
                self.update_max_cost()
            else:
                return r
        return z3.sat

    def get_cost(self) -> int:
        return int(sum(self.Ws0[c] for c in self.Ws0 if not tt(self.solver, c)))

    # Retrieve independent cores from Ws
    def get_cores(self, Ws: Dict[z3.ExprRef, int]):
        cores = []
        while z3.unsat == self.check(Ws):
            core = list(self.solver.unsat_core())
            print(self.solver.statistics())
            if not core:
                return z3.unsat
            w = min([Ws[c] for c in core])
            for f in core:
                sub(Ws, f, w)
            cores += [(core, w)]
        self.update_max_cost()
        return cores

    # Add new soft constraints to replace core
    # with weight w. Allow to weaken at most
    # one element of core. Elements that are
    # cardinality constraints are weakened by
    # increasing their bounds. Non-cardinality
    # constraints are weakened to "true". They
    # correspond to the constraint Not(s) <= 0,
    # so weakening produces Not(s) <= 1, which
    # is a tautology.
    def update_bounds(self, Ws: Dict[z3.ExprRef, int], core: Iterable[z3.ExprRef], w: int) -> None:
        for f in core:
            if f in self.bounds:
                S, k = self.bounds[f]
                if k + 1 < len(S):
                    add(Ws, self.at_most(S, k + 1), w)
        add(Ws, self.at_most([z3.mk_not(f) for f in core], 1), w)

    # Ws are weighted soft constraints
    # Whenever there is an unsatisfiable core over ws
    # increase the limit of each soft constraint from a bound
    # and create a soft constraint that limits the number of
    # increased bounds to be at most one.
    def maxsat(self, Ws: Dict[z3.ExprRef, int]):
        self.min_cost = 0
        self.max_cost = sum(Ws[c] for c in Ws)
        self.Ws0 = Ws.copy()
        while True:
            cores = self.get_cores(Ws)
            if not cores:
                break
            if cores == z3.unsat:
                return z3.unsat
            for (core, w) in cores:
                self.min_cost += w
                self.print_cost()
                self.update_bounds(Ws, core, w)
        return self.min_cost, {f for f in self.Ws0 if not tt(self.solver, f)}

    def from_file(self, file: str):
        opt = z3.Optimize()
        opt.from_file(file)
        self.solver.add(opt.assertions())
        obj = opt.objectives()[0]
        Ws = {}
        for f in obj.children():
            assert (f.arg(1).as_long() == 0)
            add(Ws, f.arg(0), f.arg(2).as_long())
        return self.maxsat(Ws)

    def from_formulas(self, hard: Iterable[z3.ExprRef], soft: Iterable[Tuple[z3.ExprRef, int]]):
        self.solver.add(hard)
        Ws = {}
        for f, cost in soft:
            add(Ws, f, cost)
        return self.maxsat(Ws)

    def from_int_clauses(self, hard: List[List[int]], soft: List[List[int]], weight: List[int]) -> None:
        return None


def main(file: str) -> None:
    s = z3.SolverFor("QF_FD")
    rc2 = RC2(s)
    z3.set_param(verbose=0)
    cost, falses = rc2.from_file(file)
    print(cost)
    print(s.statistics())


if len(sys.argv) > 1:
    main(sys.argv[1])
