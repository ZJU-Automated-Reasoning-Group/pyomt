Bit-Vector Optimization Module
==========================

The bit-vector optimization module provides specialized solvers for bit-vector optimization problems in SMT.

Classes
-------

BVOptimizer
~~~~~~~~~~

Main class for bit-vector optimization.

.. code-block:: python

    from pyomt.omtbv import BVOptimizer

Methods:

* ``add_assertion(formula)``: Add a constraint to the optimization problem
* ``maximize(term)``: Set the objective function to maximize
* ``minimize(term)``: Set the objective function to minimize
* ``solve()``: Solve the optimization problem


BitBlastOMTSolver
~~~~~~~~~~~~~~~~

Implements bit-blasting based optimization techniques.

.. code-block:: python

    from pyomt.omtbv import BitBlastOMTSolver


BVOptMaxSAT
~~~~~~~~~~

MaxSAT-based approach for bit-vector optimization.

.. code-block:: python

    from pyomt.omtbv import BVOptMaxSAT
