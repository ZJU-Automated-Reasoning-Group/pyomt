Welcome to pyomt's Documentation!
=================================

pyomt is an Optimization Modulo Theory (OMT) Solver that extends SMT solving with optimization capabilities.

Installation
------------

You can install pyomt using pip:

.. code-block:: bash

    pip install pyomt

Requirements:

* Python >= 3.9
* See `requirements.txt` in the repository root

Quick Start
-----------

Here's a simple example of using pyomt:

.. code-block:: python

    from pysmt.shortcuts import Symbol, And, BV, BVUGT, BVULT
    from pysmt.typing import BVType
    from pyomt.omtbv.bv_opt_maxsat import BVOptMaxSAT

    x = Symbol('x', BVType(8))
    y = Symbol('y', BVType(8))
    constraints = And(BVULT(x, BV(100, 8)), BVUGT(y, BV(50, 8)))

    optimizer = BVOptMaxSAT()
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
* **pyomt.maxsmt**: MaxSMT optimization
* **pyomt.omtbv**: Bit-vector optimization
* **pyomt.omtarith**: Arithmetic optimization
* **pyomt.utils**: Utilities and helpers

License
-------

pyomt is released under the MIT License.

Contributing
------------

Contributions are welcome! Please feel free to submit a Pull Request.



