import Mathlib

theorem algebra_202096 {x y z b : ℝ} (h1 : 3*x*y*z - x^3 - y^3 - z^3 = b^3) (h2 : x+y+z = 2*b) (h3 : x^2+y^2+z^2 = b^2) :
    (b = 0 ∧ (x = 0 ∧ y = 0 ∧ z = 0)) ∨ (b ≠ 0 ∧ False) := by
  have h4 : b = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y + z - 2 * b), sq_nonneg (x ^ 2 + y ^ 2 + z ^ 2 - b ^ 2), sq_nonneg (b), sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]
  have h5 : x = 0 := by 
    nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), h4, sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h6 : y = 0 := by
    nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), h4, sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h7 : z = 0 := by
    nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), h4, sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  left
  simp [h4, h5, h6, h7]