import Mathlib

theorem algebra_222639 {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : x + y + z = 9) (h2 : 1 / x + 1 / y + 1 / z = 1) (h3 : x * y + x * z + y * z = 27) :
    x = 3 ∧ y = 3 ∧ z = 3 := by
  have h5 : x * y * z = 27 := by 
    field_simp [hx, hy, hz] at h2
    nlinarith
  
  have h6 : x = 3 := by
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (z - 3), sq_nonneg (x * y - 9), sq_nonneg (y * z - 9), sq_nonneg (z * x - 9)]
  
  have h7 : y = 3 := by
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (z - 3), sq_nonneg (x * y - 9), sq_nonneg (y * z - 9), sq_nonneg (z * x - 9)]
  
  have h8 : z = 3 := by
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (z - 3), sq_nonneg (x * y - 9), sq_nonneg (y * z - 9), sq_nonneg (z * x - 9)]
  
  constructor
  · exact h6
  constructor
  · exact h7
  · exact h8