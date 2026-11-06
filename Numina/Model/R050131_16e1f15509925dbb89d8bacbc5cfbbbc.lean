import Mathlib

theorem algebra_247954 {x y : ℝ} (h1 : x * y = 6) (h2 : x^2 * y + x * y^2 + x + y = 63) :
    x^2 + y^2 = 69 := by
  have eq1 : x^2 * y + x * y^2 + x + y = (x * y + 1) * (x + y) := by
    ring
  rw [eq1] at h2 
  have eq2 : (6 + 1 : ℝ) * (x + y) = 63 := by
    rw [h1] at h2 
    linarith 
  have eq3 : x + y = 9 := by 
    nlinarith 
  calc
    x^2 + y^2 = (x + y)^2 - 2 * (x * y) := by ring
    _ = 9^2 - 2 * (6) := by rw [eq3, h1]
    _ = 81 - 12 := by norm_num 
    _ = 69 := by norm_num