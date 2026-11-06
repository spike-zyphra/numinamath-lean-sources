import Mathlib

/- Simplify $$\sqrt{6+4\sqrt2}+\sqrt{6-4\sqrt2}.$$ -/
theorem algebra_10496 : Real.sqrt (6 + 4 * Real.sqrt 2) + Real.sqrt (6 - 4 * Real.sqrt 2) = 4 := by
  have h₁ : Real.sqrt (6 + 4 * Real.sqrt 2) = 2 + Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
  have h₂ : Real.sqrt (6 - 4 * Real.sqrt 2) = 2 - Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
  rw [h₁, h₂]
  ring