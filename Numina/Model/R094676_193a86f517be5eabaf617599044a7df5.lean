import Mathlib

theorem algebra_232313 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : x + y ^ 2 + z ^ 3 = 3) (h2 : y + z ^ 2 + x ^ 3 = 3) (h3 : z + x ^ 2 + y ^ 3 = 3) :
    x = 1 ∧ y = 1 ∧ z = 1 := by
  have h4 : x ≤ 3 := by nlinarith [sq_nonneg (y - 1), sq_nonneg (z - 1), sq_nonneg (x - 1), h1, h2, h3]
  have h5 : y ≤ 3 := by nlinarith [sq_nonneg (y - 1), sq_nonneg (z - 1), sq_nonneg (x - 1), h1, h2, h3]
  have h6 : z ≤ 3 := by nlinarith [sq_nonneg (y - 1), sq_nonneg (z - 1), sq_nonneg (x - 1), h1, h2, h3]
  have h7 : x ≥ 1 := by nlinarith [sq_nonneg (y - 1), sq_nonneg (z - 1), sq_nonneg (x - 1), h1, h2, h3]
  have h8 : y ≥ 1 := by nlinarith [sq_nonneg (y - 1), sq_nonneg (z - 1), sq_nonneg (x - 1), h1, h2, h3]
  have h9 : z ≥ 1 := by nlinarith [sq_nonneg (y - 1), sq_nonneg (z - 1), sq_nonneg (x - 1), h1, h2, h3]
  have h10 : x = 1 := by
    nlinarith [sq_nonneg (y - 1), sq_nonneg (z - 1), sq_nonneg (x - 1), h1, h2, h3, h4, h5, h6, h7, h8, h9]
  have h11 : y = 1 := by
    nlinarith [sq_nonneg (y - 1), sq_nonneg (z - 1), sq_nonneg (x - 1), h1, h2, h3, h10, h4, h5, h6, h7, h8, h9]
  have h12 : z = 1 := by
    nlinarith [sq_nonneg (y - 1), sq_nonneg (z - 1), sq_nonneg (x - 1), h1, h2, h3, h10, h11, h4, h5, h6, h7, h8, h9]
  exact ⟨h10, h11, h12⟩