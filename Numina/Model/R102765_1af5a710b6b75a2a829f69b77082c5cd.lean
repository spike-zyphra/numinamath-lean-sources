import Mathlib

theorem algebra_2717 (α β : ℝ) : Real.sin (α - β) + Real.cos (α + β) = (Real.sin α + Real.cos α) * (Real.cos β - Real.sin β) := by
  rw [Real.sin_sub, Real.cos_add]
  ring