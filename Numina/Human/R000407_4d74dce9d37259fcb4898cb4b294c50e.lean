import Mathlib

/- What is the value of $\sqrt{15 - 6\sqrt{6}} + \sqrt{15 + 6\sqrt{6}}$? -/
theorem algebra_10346 : Real.sqrt (15 - 6 * Real.sqrt 6) + Real.sqrt (15 + 6 * Real.sqrt 6) = 6 := by
  have h₁ : Real.sqrt (15 - 6 * Real.sqrt 6) = 3 - Real.sqrt 6 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;>
    nlinarith [Real.sq_sqrt (show 0 ≤ 6 by norm_num)]
  have h₂ : Real.sqrt (15 + 6 * Real.sqrt 6) = 3 + Real.sqrt 6 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;>
    nlinarith [Real.sq_sqrt (show 0 ≤ 6 by norm_num)]
  rw [h₁, h₂]
  ring