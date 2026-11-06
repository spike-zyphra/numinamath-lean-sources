import Mathlib 

theorem algebra_604568 {x y : ℝ} (h1 : x = y * (3 - y)^2) (h2 : y = x * (3 -x)^2 ) : 
  x + y = 0 ∨ x + y = 3 ∨ x + y = 4 ∨ x + y = 5 ∨ x + y = 8 := by
  have h3 : (x + y - 0) * (x + y - 3) * (x + y - 4) * (x + y - 5) * (x + y - 8) = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 4), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x + y - 4), sq_nonneg (x - y), sq_nonneg (x + y - 3), sq_nonneg (x + y - 5), sq_nonneg (x + y - 8)]
  cases' (mul_eq_zero.mp h3) with h4 h5
  cases' (mul_eq_zero.mp h4) with h4 h6
  cases' (mul_eq_zero.mp h4) with h4 h7
  cases' (mul_eq_zero.mp h4) with h4 h8
  · -- Case x + y = 0
    left
    linarith
  · -- Case x + y - 3 = 0
    right
    left
    linarith
  · -- Case x + y - 4 = 0
    right
    right
    left
    linarith
  · -- Case x + y - 5 = 0
    right
    right
    right
    left
    linarith
  · -- Case x + y - 8 = 0
    right
    right
    right
    right
    linarith