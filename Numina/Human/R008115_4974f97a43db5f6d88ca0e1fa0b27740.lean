import Mathlib
/-Solve the equation: $x^{2}-4x-7=0$.-/
theorem algebra_9425 {x : ℝ} (hx : x^2 - 4 * x - 7 = 0) :
    x = 2 + Real.sqrt 11 ∨ x = 2 - Real.sqrt 11 := by 
  -- Rearrange the given equation to standard quadratic form
  have h₁ := hx
  rw [eq_comm] at h₁
  -- Apply the quadratic formula to solve for x
  apply or_iff_not_imp_right.mpr
  intro h
  -- Use the fact that the square root of 11 is non-negative to solve for x
  apply mul_left_cancel₀ (sub_ne_zero.mpr h)
  nlinarith [Real.sq_sqrt (show 0 ≤ 11 from (by norm_num))]