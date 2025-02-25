Welcome to pyomt's Documentation!
=================================

pyomt is an Optimization Modulo Theory (OMT) Solver that extends SMT solving with optimization capabilities.

Installation
------------

You can install pyomt using pip:

.. code-block:: bash

    pip install pyomt

Requirements:

* Python >= 3.6.0
* PySMT == 0.9.6
* z3-solver == 4.8.10
* Other dependencies will be installed automatically

Quick Start
-----------

Here's a simple example of using pyomt:

.. code-block:: python

    from pysmt.shortcuts import Symbol, And, BV
    from pyomt.omtbv import BVOptimizer

    # Create variables and constraints
    x = Symbol('x', BVType(8))
    y = Symbol('y', BVType(8))
    constraints = And(BVULT(x, BV(100, 8)), BVUGT(y, BV(50, 8)))

    # Create optimizer and solve
    optimizer = BVOptimizer()
    optimizer.add_assertion(constraints)
    optimizer.maximize(x)

Features
--------

* Support for various optimization problems in SMT
* Built on top of PySMT for maximum flexibility
* Multiple optimization strategies:
    - MaxSAT-based optimization
    - Bit-blasting for BV optimization
    - Arithmetic optimization
* Portfolio solving capabilities

Modules
-------

* **pyomt.maxsat**: MaxSAT-based optimization algorithms
* **pyomt.omtbv**: Bit-vector optimization
* **pyomt.omtarith**: Arithmetic optimization
* **pyomt.utils**: Utility functions and helpers

License
-------

pyomt is released under the MIT License.

Contributing
------------

Contributions are welcome! Please feel free to submit a Pull Request.

API Reference
-------------

.. toctree::
   :maxdepth: 2
   :caption: Contents:

   api/maxsat
   api/omtbv
   api/omtarith
   api/utils


