import Mathlib

theorem algebra_3613 {x : ℝ} (hx : x^2 - 5 * x - 6 = 0) : x^4 - 10 * x^3 + 26 * x^2 - 5 * x - 6 = 36 := by 
  have h1 : (x - 6) * (x + 1) = 0 := by
    linarith 
  cases' (mul_eq_zero.mp h1) with h2 h3
  · -- Case where x = 6
    have hx6 : x = 6 := by linarith 
    rw [hx6]
    norm_num
  · -- Case where x = -1
    have hx1 : x = -1 := by linarith 
    rw [hx1]
    norm_num