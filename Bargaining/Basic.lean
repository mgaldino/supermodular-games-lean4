/-
  Formal Proofs — Formalizing Bargaining Theory in Lean 4

  This module contains the formalizations of bargaining models,
  starting with Rubinstein (1982) and progressing to Baron-Ferejohn (1989).

  Structure:
  - Rubinstein/     : Two-player alternating-offers bargaining
  - BaronFerejohn/  : N-player legislative bargaining with random proposer
  - Screening/      : Private types and screening extensions

  References:
  - Rubinstein, A. (1982). "Perfect Equilibrium in a Bargaining Model." Econometrica.
  - Baron, D. & Ferejohn, J. (1989). "Bargaining in Legislatures." APSR.
  - Osborne & Rubinstein (1990). Bargaining and Markets, Ch. 3.
-/

import Mathlib

-- ===========================================================================
-- Setup verification
-- ===========================================================================

theorem setup_test : 1 + 1 = 2 := by norm_num
