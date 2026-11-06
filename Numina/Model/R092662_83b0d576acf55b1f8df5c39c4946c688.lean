import Mathlib

theorem algebra_202120 {x : ℝ} (hx : 0 < x) (h : (1 + x / 100) * (1 - x / 100) = 84 / 100) :
    x = 40 := by
  have h1 : (x / 100) ^ 2 = 16 / 100 := by
    nlinarith 
  have h2 : x / 100 = 4 / 10 := by
    nlinarith [sq_nonneg (x / 100 - 4 / 10), sq_nonneg (x / 100 + 4 / 10), h1, hx]
  have h3 : x = 40 := by
    linarith
  exact h3