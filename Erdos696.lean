/-
# Erdős Problem #696 — top-level import file

This module imports every component of the blueprint formalization of
Erdős Problem #696 (normal orders of `h(n)` and `H(n)`, disproof of the
`H(n)/h(n) → ∞` conjecture).

The paper is in `../erdos_696_paper.pdf`.  Each Lean file mirrors a
section of the paper; see the docstrings inside each module for the
correspondence.
-/

import Erdos696.Defs
import Erdos696.AnalyticInputs
import Erdos696.Tower
import Erdos696.SubsetProduct
import Erdos696.CompositeSuccessor
import Erdos696.UpperBoundH
import Erdos696.UpperBoundLittleH
import Erdos696.LowerBoundLittleH
import Erdos696.LowerBoundH
import Erdos696.Main
