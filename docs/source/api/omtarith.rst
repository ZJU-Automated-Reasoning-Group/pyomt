Arithmetic Optimization Module
==========================

The arithmetic optimization module provides solvers for linear and non-linear arithmetic optimization problems in SMT.

Classes
-------

ArithOptimizer
~~~~~~~~~~~~

Main class for arithmetic optimization.

.. code-block:: python

    from pyomt.omtarith import ArithOptimizer

Methods:

* ``add_assertion(formula)``: Add a constraint to the optimization problem
* ``maximize(term)``: Set the objective function to maximize
* ``minimize(term)``: Set the objective function to minimize
* ``solve()``: Solve the optimization problem

Features:

* Support for both linear and non-linear optimization
* Efficient handling of real and integer arithmetic

ArithOptLP
~~~~~~~~~

Implements Linear Programming (LP) based optimization.

.. code-block:: python

    from pyomt.omtarith import ArithOptLP

Features:

* Specialized for linear arithmetic problems
* Efficient LP solving techniques
* Support for mixed integer linear programming

ArithOptQSMT
~~~~~~~~~~~

Quantifier-based approach for arithmetic optimization.

.. code-block:: python

    from pyomt.omtarith import ArithOptQSMT

Features:

* Handles complex arithmetic constraints
* Uses quantifier elimination techniques
* Suitable for non-linear optimization problems