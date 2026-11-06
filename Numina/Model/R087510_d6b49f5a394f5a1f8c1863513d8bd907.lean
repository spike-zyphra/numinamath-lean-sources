import Mathlib

theorem algebra_1315 {x : ℝ} (hx : x > 2) :
    Real.sqrt (x + 2 * Real.sqrt (x - 1)) + Real.sqrt (x - 2 * Real.sqrt (x - 1)) =
    2 * Real.sqrt (x - 1) := by 
  have h1 : x - 1 > 1 := by linarith
  have h2 : Real.sqrt (x - 1) > 1 := by 
    have h3 : Real.sqrt (x - 1) > Real.sqrt 1 := by
      apply Real.sqrt_lt_sqrt 
      all_goals linarith 
    have h4 : Real.sqrt 1 = 1 := Real.sqrt_one
    linarith 
  have h5 : (Real.sqrt (x - 1) + 1) ^ 2 = x + 2 * Real.sqrt (x - 1) := by 
    nlinarith [Real.sq_sqrt (show 0 ≤ x - 1 by linarith)]
  have h7 : Real.sqrt (x + 2 * Real.sqrt (x - 1)) = Real.sqrt (x - 1) + 1 := by
    rw [← h5]
    have h8 : 0 ≤ Real.sqrt (x - 1) + 1 := by positivity
    rw [Real.sqrt_sq (by linarith [Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x - 1 + 1)])]
  have h6 : (Real.sqrt (x - 1) - 1) ^ 2 = x - 2 * Real.sqrt (x - 1) := by 
    nlinarith [Real.sq_sqrt (show 0 ≤ x - 1 by linarith)]
  have h8 : Real.sqrt (x - 2 * Real.sqrt (x - 1)) = Real.sqrt (x - 1) - 1 := by 
    rw [← h6]
    have h9 : 0 ≤ Real.sqrt (x - 1) - 1 := by
      have h10 : Real.sqrt (x - 1) > 1 := h2
      nlinarith
    have h10 : Real.sqrt ((Real.sqrt (x - 1) - 1) ^ 2) = Real.sqrt (x - 1) - 1 := by
      rw [Real.sqrt_sq (by linarith [Real.sqrt_nonneg (x - 1), h9])]
    linarith [h10, Real.sqrt_nonneg ((Real.sqrt (x - 1) - 1) ^ 2), Real.sqrt_nonneg (x - 2 * Real.sqrt (x - 1))]
  rw [h7, h8]
  ring