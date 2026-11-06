import Mathlib

theorem algebra_131822 {x : ℝ} (hx : x > 0) (h : 6 * x = 3 * (x + 7) + 14 * (x + 14)) :
    6 * x - 14 * (x + 14) = 70 := by 
  have h1 : x > 0 := hx
  have h2 : 6 * x = 3 * (x + 7) + 14 * (x + 14) := h
  have h3 : -11 * x = 217 := by
    nlinarith
  -- Now from h3, the value of x is negative
  have h4 : x < 0 := by
    nlinarith
  -- Now we have x > 0 and x < 0 contradiction
  linarith