import Mathlib

theorem algebra_130165 {x y : ℝ} (hx : x > 2 * y) (hy : y > 0) (h : 2 * Real.log (x - 2 * y) = Real.log x + Real.log y) :
    x / y = 4 := by 
  have h1 : x > 0 := by nlinarith
  have h2 : x - 2 * y > 0 := by linarith
  have h3 : 2 * Real.log (x - 2 * y) = Real.log ((x - 2 * y) ^ 2) := by
    simp [Real.log_pow]
    all_goals linarith
  have h4 : Real.log x + Real.log y = Real.log (x * y) := by
    rw [Real.log_mul (by positivity) (by positivity)]
  rw [h3] at h
  rw [h4] at h
  have h5 : (x - 2 * y) ^ 2 = x * y := by
    have h6 : Real.log ((x - 2 * y) ^ 2) = Real.log (x * y) := by linarith
    have h7 : (x - 2 * y) ^ 2 > 0 := by positivity
    have h8 : x * y > 0 := by positivity
    have h9 : (x - 2 * y) ^ 2 = x * y := by
      apply Real.log_injOn_pos (by simp [h7]) (by simp [h8]) h6
    linarith
  have h11 : (x - 4 * y) * (x - y) = 0 := by
    nlinarith [h5]
  cases' (mul_eq_zero.mp h11) with h12 h13
  · -- Case x = 4y
    have h14 : x = 4 * y := by linarith
    field_simp [hy]
    nlinarith
  · -- Case x = y
    have h14 : x = y := by linarith
    nlinarith [h14, hx, hy]