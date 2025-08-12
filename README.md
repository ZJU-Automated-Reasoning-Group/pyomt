# PyOMT — Optimization Modulo Theories

PyOMT provides engines for solving Optimization Modulo Theories (OMT) problems, focusing on bit-vector objectives.

## Features

- **QSMT**: Delegates to external SMT solvers (Z3, CVC5, Yices, MathSAT5, Bitwuzla, Q3B)
- **MaxSAT**: Built-in algorithms (OBV-BS, FM, RC2) and PySAT ecosystem
- **Iterative**: SMT-based linear/binary search

## Installation

```bash
git clone https://github.com/ZJU-Automated-Reasoning-Group/pyomt.git
cd pyomt
pip install -e .
```

**External solvers** (optional): Run `bin_solvers/download.sh` or use `pysmt-install --z3 --msat --yices --cvc5 --btor --confirm-agreement`

## Usage

### OMT(BV) CLI

```bash
# QSMT with Z3
pyomt solve regress/case1.smt2 --engine qsmt --solver-qsmt z3

# MaxSAT-based
pyomt solve regress/case2.smt2 --engine maxsat --solver-maxsat FM

# Iterative search
pyomt solve regress/case3.smt2 --engine iter --solver-iter z3-bs
```

### MaxSAT CLI

```bash
maxsat solve problem.wcnf --engine FM --timeout 600
```

## Engines

- `--engine`: `qsmt`, `maxsat`, `iter`, `z3py`
- `--solver-qsmt`: `z3`, `cvc5`, `yices`, `msat`, `bitwuzla`, `q3b`
- `--solver-maxsat`: `FM`, `RC2`, `OBV-BS`
- `--solver-iter`: `z3-ls`, `z3-bs`, `cvc5-ls`, `cvc5-bs`, etc.

## Development

```bash
pytest -q                    # Run tests
make -C docs html           # Build docs
```

## License

MIT