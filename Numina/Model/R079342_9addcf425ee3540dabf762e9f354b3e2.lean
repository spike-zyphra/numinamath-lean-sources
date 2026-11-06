import Mathlib

theorem algebra_15510 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : Real.log (x * y ^ 3) = 1) (h2 : Real.log (x ^ 2 * y) = 1) :
    Real.log (x * y) = 3 / 5 := by
  have eq3 : Real.log (x * y ^ 3) = Real.log x + 3 * Real.log y := by
    rw [Real.log_mul (by positivity) (by positivity)]
    simp [Real.log_pow]
    all_goals linarith
  rw [eq3] at h1
  have eq4 : Real.log (x ^ 2 * y) = 2 * Real.log x + Real.log y := by
    rw [Real.log_mul (by positivity) (by positivity)]
    simp [Real.log_pow]
    all_goals linarith
  rw [eq4] at h2
  have eq5 : Real.log (x * y) = Real.log x + Real.log y := by
    rw [Real.log_mul (by positivity) (by positivity)]
  rw [eq5]
  linarith [h1, h2]