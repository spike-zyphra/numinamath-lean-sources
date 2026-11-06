import Mathlib

theorem algebra_70765 {x y : ℝ} (h₀ : x ^ 2 + y ^ 2 - x * y = 2) (h₁ : x ^ 4 + y ^ 4 + x ^ 2 * y ^ 2 = 8) :
    x ^ 8 + y ^ 8 + x ^ 2014 * y ^ 2014 = 48 := by
  have h2 : x * y = 1 := by
    have eq1 : x ^ 2 + y ^ 2 = 2 + x * y := by
      linarith
    have eq2 : x ^ 4 + y ^ 4 = (x ^ 2 + y ^ 2) ^ 2 - 2 * (x * y) ^ 2 := by 
      ring
    rw [eq2] at h₁
    rw [eq1] at h₁
    nlinarith
  have h3 : x ^ 2 + y ^ 2 = 3 := by
    nlinarith [h2]
  have h4 : x ^ 4 + y ^ 4 = 7 := by 
    have eq2 : x ^ 4 + y ^ 4 = (x ^ 2 + y ^ 2) ^ 2 - 2 * (x * y) ^ 2 := by 
      ring
    rw [eq2]
    nlinarith [h3, h2]
  have h5 : x ^ 8 + y ^ 8 = 47 := by
    have eq3 : x ^ 8 + y ^ 8 = (x ^ 4 + y ^ 4) ^ 2 - 2 * (x * y) ^ 4 := by
      ring
    rw [eq3]
    nlinarith [h4, h2]
  have h6 : x ^ 2014 * y ^ 2014 = 1 := by
    have eq4 : x ^ 2014 * y ^ 2014 = (x * y) ^ 2014 := by
      ring
    rw [eq4]
    rw [h2]
    norm_num
  linarith [h5, h6]