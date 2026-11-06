import Mathlib

theorem algebra_221991 (x y z : ℝ)
    (h : 2*x^4+2*y^4-4*x^3*y+6*x^2*y^2-4*x*y^3+7*y^2+7*z^2-14*y*z-70*y+70*z+175=0) :
    x=0 ∧ y=0 ∧ z=-5 := by
  have h1 : (x^2 - x * y + y^2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x ^ 2 - x * y + y ^ 2), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (z - (y - 5)), sq_nonneg (y - 0), sq_nonneg (x - 0), sq_nonneg (z + 5), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (z - (y - 5))]
  have h2 : x^2 - x * y + y^2 = 0 := by
    nlinarith 
  have h3 : (2 * x - y) ^ 2 + 3 * y ^ 2 = 0 := by
    nlinarith 
  have h4 : y = 0 := by
    nlinarith [sq_nonneg (2 * x - y), sq_nonneg (y)]
  have h5 : x = 0 := by
    nlinarith [sq_nonneg (2 * x - y), sq_nonneg (y)]
  have h6 : z = -5 := by
    rw [h5, h4] at h
    nlinarith
  exact ⟨h5, h4, h6⟩