import Mathlib

theorem algebra_198795 {x y z : ℝ} (h : x ^ 2 + y ^ 2 + z ^ 2 = x * y + y * z + z * x) :
    x = y ∧ y = z := by
  have h1 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h2 : (x - y) ^ 2 ≥ 0 := by 
    apply sq_nonneg
  have h3 : (y - z) ^ 2 ≥ 0 := by 
    apply sq_nonneg
  have h4 : (z - x) ^ 2 ≥ 0 := by 
    apply sq_nonneg
  have h5 : (x - y) ^ 2 = 0 := by
    nlinarith [h1, h2, h3, h4]
  have h6 : (y - z) ^ 2 = 0 := by 
    nlinarith [h1, h2, h3, h4]
  have h7 : (z - x) ^ 2 = 0 := by 
    nlinarith [h1, h2, h3, h4]
  have h8 : x - y = 0 := by 
    rwa [sq_eq_zero_iff] at h5
  have h9 : y - z = 0 := by 
    rwa [sq_eq_zero_iff] at h6
  constructor
  · -- Show that x = y
    linarith
  · -- Show that y = z
    linarith