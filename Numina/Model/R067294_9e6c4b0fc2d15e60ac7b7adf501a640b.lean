import Mathlib

theorem algebra_6343 (x y z : ℝ) (h : x^2 + y^2 + z^2 = x * y + y * z + z * x) :
    x = y ∧ y = z := by
  have h1 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = 0 := by
    nlinarith [h]
  have h2 : (x - y) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h3 : x - y = 0 := by
    nlinarith [h2]
  have h4 : (y - z) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h5 : y - z = 0 := by
    nlinarith [h4]
  constructor
  · -- Proof of x = y
    linarith
  · -- Proof of y = z
    linarith