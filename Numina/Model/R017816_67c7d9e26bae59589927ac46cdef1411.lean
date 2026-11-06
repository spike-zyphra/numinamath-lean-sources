import Mathlib

theorem algebra_13264 (x : ℝ) : (x^3 - 6)^3 = x + 6 ↔ x = 2 := by
  constructor
  · -- Assume (x ^ 3 - 6) ^ 3 = x + 6, prove x = 2
    intro h 
    have h1 : (x^3 - 6) ^ 3 = x + 6 := h 
    have eq1 : (x^3 - 6) ^ 3 - (x + 6) = 0 := by linarith [h1]

    have h2 : (x - 2) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (x ^ 3 - 6 - 2), sq_nonneg (x - 2), sq_nonneg ((x ^ 3 - 6) ^ 2 - 4), sq_nonneg ((x^3 - 6) + 2), sq_nonneg (x^2 - 4), sq_nonneg (x^3 - 2 * x), sq_nonneg ((x - 2) * (x^3 - 6 - 2)), sq_nonneg ((x - 2)^2), sq_nonneg ((x^3 - 6 - 2) ^ 2 - 4), sq_nonneg (x^2 - 2 * x), sq_nonneg (x * (x - 2)), sq_nonneg ((x^3 - 6) ^ 2 - 4)]
    
    have h3 : x - 2 = 0 := by 
      nlinarith

    linarith 
  · -- Assume x = 2, prove (x^3 - 6)^3 = x + 6 
    intro h 
    rw [h] 
    norm_num