"""
Objective-level divide-and-conquer for solving for boxed optimization over bit-vectors
1. Solve each objective in parallel
2. Combine the results

Possible improvements:
- Use different solver configurations for different objectives.
   - Linear search, binary search, QSMT, MaxSAT
   - Each of the above can be run with different configurations
"""

import multiprocessing as mp
from multiprocessing import Process, Queue, Value
from dataclasses import dataclass
from enum import Enum
import ctypes
import signal
from typing import Optional, Tuple, List, Dict, Any
import time
import logging
from typing import List, Tuple, Dict, Any
import os
import time
import z3
from pyomt.omtbv.bv_opt_iterative_search import bv_opt_with_binary_search, bv_opt_with_linear_search
from pyomt.omtbv.bv_opt_qsmt import bv_opt_with_qsmt
from pyomt.omtbv.bv_opt_maxsat import bv_opt_with_maxsat

