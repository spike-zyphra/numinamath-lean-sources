import Mathlib

theorem algebra_304081 (α : ℝ) (h : Real.sin α + Real.cos α = Real.sqrt 2 / 2) :
    (Real.sin α)^4 + (Real.cos α)^4 = 7 / 8 := by
  have h1 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h2 : (Real.sin α + Real.cos α)^2 = 1 / 2 := by
    rw [h]
    have h2' : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
      calc
        (Real.sqrt 2 / 2) ^ 2 = (Real.sqrt 2 ^ 2) / 4 := by ring
        _ = (2 : ℝ) / 4 := by rw [Real.sq_sqrt]; positivity
        _ = (1 : ℝ) / 2 := by norm_num
    linarith
  have h3 : Real.sin α * Real.cos α = -1 / 4 := by
    have h2' : (Real.sin α + Real.cos α)^2 = Real.sin α ^ 2 + Real.cos α ^ 2 + 2 * (Real.sin α * Real.cos α) := by
      ring
    rw [h1] at h2'
    rw [h2] at h2'
    linarith
  have h4 : (Real.sin α) ^ 4 + (Real.cos α) ^ 4 = ((Real.sin α ^ 2 + Real.cos α ^ 2)^2 - 2 * (Real.sin α * Real.cos α) ^ 2) := by
    nlinarith [sq_nonneg (Real.sin α ^ 2 - Real.cos α ^ 2)]
  rw [h4]
  rw [h1, h3]
  norm_num