import Mathlib

/- Compute $35^{1723} - 16^{1723}$ modulo 6. -/
theorem number_theory_14336 : (35^1723 - 16^1723) % 6 = 1 := by
  native_decide
