import Mathlib

/- Evaluate $i^{11} + i^{111}$. -/
theorem algebra_13340 : Complex.I^11 + Complex.I^111 = -2 * Complex.I := by
  simp only [pow_succ, Complex.I_mul_I]
  simp
  ring