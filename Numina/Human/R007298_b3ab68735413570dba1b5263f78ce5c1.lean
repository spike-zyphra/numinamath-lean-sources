import Mathlib

/- Simplify: $\sqrt{50} + \sqrt{18}$ . Express your answer in simplest radical form. -/
theorem algebra_11271 : Real.sqrt 50 + Real.sqrt 18 = 8 * Real.sqrt 2 := by
  rw [show Real.sqrt 50 = 5 * Real.sqrt 2 by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num <;>
      ring_nf <;> norm_num]
  rw [show Real.sqrt 18 = 3 * Real.sqrt 2 by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num <;>
      ring_nf <;> norm_num]
  ring