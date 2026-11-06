import Mathlib

theorem algebra_20864 {x y : ℝ} (h₀ : x - y = 4) (h₁ : x ^ 3 - y ^ 3 = 28) : x * y = -3 := by
  have h2 : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by 
    ring
  rw [h2, h₀] at h₁
  have h3 : x ^ 2 + x * y + y ^ 2 = 7 := by
    linarith
  
  have h4 : (x - y) ^ 2 = x ^ 2 - 2 * (x * y) + y ^ 2 := by 
    ring
  rw [h₀] at h4
  have h5 : 16 = x ^ 2 + y ^ 2 - 2 * (x * y) := by 
    linarith

  have eq1 : x ^ 2 + x * y + y ^ 2 = 7 := by linarith [h3]
  have eq2 : x ^ 2 + y ^ 2 - 2 * (x * y) = 16 := by linarith [h5]

  have eq3 : 3 * (x * y) = -9 := by
    linarith [eq1, eq2]

  linarith