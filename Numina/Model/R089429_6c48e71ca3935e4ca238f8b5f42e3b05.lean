import Mathlib

theorem algebra_264369 (x y : ℝ) (hx : x^2 - 1 ≥ 0) (hy : 1 - x^2 ≥ 0)
    (h : Real.sqrt (x^2 - 1) - y * (x - 1) = Real.sqrt (1 - x^2) - 2) :
    x - y = 0 := by
  have h2 : x^2 = 1 := by 
    nlinarith
  have h3 : x = 1 ∨ x = -1 := by 
    rw [sq_eq_one_iff] at h2
    exact h2
  cases h3 with
  | inl h4 =>
    rw [show x = 1 by linarith] at h
    have h5 : Real.sqrt ( (1 : ℝ)^2 - 1 ) = (0 : ℝ) := by
      norm_num [Real.sqrt_eq_zero]
    have h6 : Real.sqrt (1 - (1 : ℝ)^2 ) = (0 : ℝ) := by
      norm_num [Real.sqrt_eq_zero]
    rw [h5, h6] at h
    all_goals linarith
  | inr h4 =>
    rw [show x = -1 by linarith] at h
    have h7 : Real.sqrt ( (-1 : ℝ)^2 - 1 ) = (0 : ℝ) := by
      norm_num [Real.sqrt_eq_zero]
    have h8 : Real.sqrt (1 - (-1 : ℝ)^2 ) = (0 : ℝ) := by
      norm_num [Real.sqrt_eq_zero]
    rw [h7, h8] at h
    have hy' : y = -1 := by
      linarith
    linarith [hy']