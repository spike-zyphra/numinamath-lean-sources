import Mathlib

theorem algebra_221013 {x : ℤ} (hx : 5 * x = x ^ 2 + 4) :
    x = 4 ∨ x = 1 := by
  have h1 : x^2 - 5 * x + 4 = 0 := by 
    nlinarith
  have h2 : (x - 1) * (x - 4) = 0 := by 
    nlinarith [h1]
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case where x - 1 = 0 so x = 1
    right
    linarith
  · -- Case where x - 4 = 0 so x = 4
    left
    linarith