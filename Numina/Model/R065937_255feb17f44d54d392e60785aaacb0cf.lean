import Mathlib

theorem algebra_304739 {x : ℝ} (hx : x ≠ 0) (h : x + 2/x = 1) :
    x^2/(x^4 + 5*x^2 + 4) = 1/2 := by
  have h1 : x^2 + 2 = x := by 
    field_simp [hx] at h 
    linarith 
  have h2 : x^2 - x + 2 > 0 := by
    nlinarith [sq_nonneg (x - 0.5)]
  have h3 : x^2 - x + 2 = 0 := by 
    nlinarith 
  linarith