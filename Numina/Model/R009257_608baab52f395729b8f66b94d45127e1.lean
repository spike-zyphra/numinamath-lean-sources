import Mathlib

theorem algebra_14311 {x y : ℝ} (h₀ : (x + y) / 2 = 18) (h₁ : Real.sqrt (x * y) = Real.sqrt 92) :
    x^2 + y^2 = 1112 := by
  have h2 : x + y = 36 := by
    linarith

  have h2' : x * y ≥ 0 := by
    by_contra h
    push_neg at h
    have h3 : Real.sqrt (x * y) = 0 := by
      rw [Real.sqrt_eq_zero'.mpr]
      linarith
      all_goals nlinarith

    have h4 : Real.sqrt 92 = 0 := by 
      linarith [h₁, h3]

    have h5 : Real.sqrt 92 > 0 := by 
      positivity

    linarith [h4, h5]

  have h3 : x * y = 92 := by
    have h4 : Real.sqrt (x * y) = Real.sqrt 92 := h₁
    have h5 : Real.sqrt (x * y) ^ 2 = Real.sqrt 92 ^ 2 := by
      rw [h4]
    rw [Real.sq_sqrt (show x * y ≥ 0 by linarith), Real.sq_sqrt (show (92 : ℝ) ≥ 0 by norm_num)] at h5
    linarith

  have h6 : x^2 + y^2 = (x + y) ^ 2 - 2 * (x * y) := by
    nlinarith

  rw [h6]
  rw [h2, h3]
  norm_num