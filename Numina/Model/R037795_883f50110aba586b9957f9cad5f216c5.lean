import Mathlib

theorem algebra_193331 {x : ℝ} (hx : x > 0) (h : (1 + x / 100) * (1 + x / 100) = 2809 / 2500) :
    x = 6 := by
  have h1 : (1 + x / 100) ^ 2 = 2809 / 2500 := by
    nlinarith
  have h2 : (1 + x / 100) = 53 / 50 := by
    nlinarith [h1, sq_nonneg (1 + x / 100 - 53 / 50), sq_nonneg (1 + x / 100 + 53 / 50)]
  have h3 : x = 6 := by
    linarith
  exact h3