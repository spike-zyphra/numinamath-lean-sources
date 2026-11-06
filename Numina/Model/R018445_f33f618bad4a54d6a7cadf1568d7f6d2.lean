import Mathlib

theorem inequalities_598099 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x + y + z = 1) :
    0 ≤ x * y + y * z + z * x - 2 * x * y * z ∧
    x * y + y * z + z * x - 2 * x * y * z ≤ 7 / 27 := by
  -- Since all variables are non-negative and sum to 1, we can express z = 1 - x - y
  have h1 : 0 ≤ x * y + y * z + z * x - 2 * x * y * z := by
    have h2 : z = 1 - x - y := by linarith
    rw [h2]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y)), 
      mul_nonneg hx hy, mul_nonneg hx (show 0 ≤ (1 - x - y : ℝ) by nlinarith), 
      mul_nonneg hy (show 0 ≤ (1 - x - y : ℝ) by nlinarith)]
  have h2 : x * y + y * z + z * x - 2 * x * y * z ≤ 7 / 27 := by
    have h2 : z = 1 - x - y := by linarith
    rw [h2]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y)), 
      sq_nonneg (x + y - (1 - x - y)), 
      mul_nonneg hx hy, 
      mul_nonneg hx (show 0 ≤ (1 - x - y : ℝ) by nlinarith), 
      mul_nonneg hy (show 0 ≤ (1 - x - y : ℝ) by nlinarith), 
      mul_nonneg (show 0 ≤ x * y by nlinarith) (show 0 ≤ (1 - x - y : ℝ) by nlinarith)]
  constructor
  · exact h1
  · exact h2