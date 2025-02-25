MaxSAT Module
============

The MaxSAT module provides implementations of various MaxSAT-based optimization algorithms.

Classes
-------

MaxSATSolver
~~~~~~~~~~~~

Base class for MaxSAT solvers.

.. code-block:: python

    from pyomt.maxsat import MaxSATSolver

Methods:

* ``add_hard(formula)``: Add a hard constraint
* ``add_soft(formula, weight=1)``: Add a soft constraint with an optional weight
* ``solve()``: Solve the MaxSAT problem

RC2Solver
~~~~~~~~~

Implements the RC2 (RELAXABLE CARDINALITY CONSTRAINTS) algorithm.

.. code-block:: python

    from pyomt.maxsat import RC2Solver


FuMalikSolver
~~~~~~~~~~~~

Implements the Fu & Malik algorithm for MaxSAT solving.

.. code-block:: python

    from pyomt.maxsat import FuMalikSolver


LSUSolver
~~~~~~~~~

Implements the LSU algorithm.

.. code-block:: python

    from pyomt.maxsat import LSUSolver
