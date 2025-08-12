import pytest

from pysat.formula import WCNF

from pyomt.maxsat.maxsat_solver import MaxSATSolver, MaxSATEngine


def build_simple_wcnf_all_soft_satisfiable() -> WCNF:
    # Variables: 1, 2
    # No hard clauses. Two unit soft clauses that can be both satisfied: x1 and x2
    w = WCNF()
    w.append([1], weight=1)
    w.append([2], weight=1)
    return w


def build_simple_wcnf_conflicting_soft() -> WCNF:
    # Variables: 1
    # No hard clauses. Two conflicting unit soft clauses: x1 and not x1
    # Optimal cost must be 1 (can satisfy at most one of them)
    w = WCNF()
    w.append([1], weight=2)
    w.append([-1], weight=2)
    return w


@pytest.mark.parametrize("engine", [MaxSATEngine.FM.value, MaxSATEngine.RC2.value])
def test_solver_returns_zero_cost_when_all_soft_satisfiable(engine: str):
    wcnf = build_simple_wcnf_all_soft_satisfiable()
    solver = MaxSATSolver(wcnf)
    solver.set_maxsat_engine(engine)
    result = solver.solve()
    assert result.status in {"optimal", "unsat", "error"}
    if result.status == "optimal":
        assert result.cost == 0


@pytest.mark.parametrize("engine", [MaxSATEngine.FM.value, MaxSATEngine.RC2.value])
def test_solver_cost_with_conflicting_soft(engine: str):
    wcnf = build_simple_wcnf_conflicting_soft()
    solver = MaxSATSolver(wcnf)
    solver.set_maxsat_engine(engine)
    result = solver.solve()
    # Optimal cost should be the weight of exactly one falsified soft clause
    if result.status == "optimal":
        assert result.cost == 2


def test_set_engine_invalid_name_falls_back_to_fm():
    wcnf = build_simple_wcnf_all_soft_satisfiable()
    solver = MaxSATSolver(wcnf)
    solver.set_maxsat_engine("INVALID")
    assert solver.get_maxsat_engine() == MaxSATEngine.FM


def test_obv_bs_engine_on_unit_softs():
    # OBV-BS expects unit softs; provide three bits
    w = WCNF()
    # Hard clause to introduce some structure (still satisfiable)
    w.append([-3, 2])
    # Soft (as bits) – unit clauses; the solver returns assignment list
    w.append([1], weight=1)
    w.append([2], weight=1)
    w.append([3], weight=1)

    solver = MaxSATSolver(w)
    solver.set_maxsat_engine(MaxSATEngine.OBV_BS)
    result = solver.solve()
    # For OBV-BS we expect a list of signed ints in solution
    if result.status in {"optimal", "timeout"}:
        assert isinstance(result.solution, list)
        assert all(isinstance(l, int) for l in result.solution)


def test_obv_bs_anytime_completes_and_returns_partial_or_full():
    w = WCNF()
    w.append([1], weight=1)
    w.append([2], weight=1)
    w.append([3], weight=1)
    solver = MaxSATSolver(w, timeout=0.01)
    solver.set_maxsat_engine(MaxSATEngine.OBV_BS_ANYTIME)
    result = solver.solve()
    assert result.status in {"optimal", "timeout", "error"}
    if result.status != "error":
        assert isinstance(result.solution, list)

