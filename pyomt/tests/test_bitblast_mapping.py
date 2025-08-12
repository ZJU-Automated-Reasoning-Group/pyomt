import z3

from pyomt.utils.mapped_blast import bitblast, to_dimacs_numeric


def test_bitblast_returns_mapping_and_dimacs_like_clauses():
    x = z3.BitVec("x", 4)
    f = z3.UGT(x, 3)
    blasted, id_table, bv2bool = bitblast(f)
    assert isinstance(id_table, dict)
    assert isinstance(bv2bool, dict)
    assert "x" in bv2bool
    # Each bit of x should be represented
    assert len(bv2bool["x"]) == 4


def test_to_dimacs_numeric_produces_integer_clauses():
    x, y = z3.BitVecs("x y", 2)
    f = z3.And(z3.UGE(x, 1), z3.ULE(y, 2))
    blasted, id_table, bv2bool = bitblast(f)
    header, clauses = to_dimacs_numeric(blasted, id_table, proj_last=False)
    assert isinstance(header, list)
    assert isinstance(clauses, list)
    # Clauses are lists of ints, possibly empty if simplified heavily
    for cls in clauses:
        assert all(isinstance(l, int) for l in cls)

