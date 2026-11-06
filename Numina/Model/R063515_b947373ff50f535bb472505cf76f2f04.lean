import Mathlib

theorem algebra_171412 {x y z : ℝ} (h1 : x * y + x * z + y * z + x + y + z = -3) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 5) :
    x + y + z = -1 := by 
  have eq1 : (x + y + z) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + 2 * (x * y + x * z + y * z) := by 
    ring
  have h3 : (x + y + z) ^ 2 = 5 + 2 * (x * y + x * z + y * z) := by 
    have h2' : x ^ 2 + y ^ 2 + z ^ 2 = 5 := h2
    linarith [eq1, h2']
  have h4 : x * y + x * z + y * z = -3 - (x + y + z) := by 
    linarith 
  have h5 : (x + y + z) ^ 2 + 2 * (x + y + z) + 1 = 0 := by 
    rw [h4] at h3 
    nlinarith 
  have h6 : (x + y + z + 1) ^ 2 = 0 := by 
    nlinarith 
  have h7 : x + y + z + 1 = 0 := by 
    rw [sq_eq_zero_iff] at h6 
    linarith 
  linarith 
  all_goals nlinarith