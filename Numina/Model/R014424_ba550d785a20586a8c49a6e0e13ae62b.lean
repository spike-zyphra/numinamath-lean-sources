import Mathlib

theorem algebra_277249 {x y : ℝ} (hx : x = 3.25) (hy : y = -2.5) :
    2 / (3 * Real.sqrt (2 * x + y)) - 1 / (2 * Real.sqrt (2 * x - y)) = 1 / 6 ∧
    15 * Real.sqrt (2 * x + y) + 6 * Real.sqrt (2 * x - y) = 8 * Real.sqrt (4 * x ^ 2 - y ^ 2) := by
  have h1 : 2 * x + y = 4 := by
    rw [hx, hy]
    norm_num
  have h2 : 2 * x - y = 9 := by
    rw [hx, hy]
    norm_num
  have h3 : Real.sqrt (2 * x + y) = 2 := by
    rw [h1]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h4 : Real.sqrt (2 * x - y) = 3 := by
    rw [h2]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h5 : 4 * x ^ 2 - y ^ 2 = 36 := by
    rw [hx, hy]
    norm_num
  have h6 : Real.sqrt (4 * x ^ 2 - y ^ 2) = 6 := by
    rw [h5]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  constructor
  · -- Verify the first equation
    rw [h3, h4]
    norm_num
  · -- Verify the second equation
    rw [h3, h4, h6]
    norm_num