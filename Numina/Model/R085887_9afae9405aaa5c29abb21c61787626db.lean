import Mathlib

theorem algebra_138539 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x + y^2 + z^3 = 3) (h2 : y + z^2 + x^3 = 3) (h3 : z + x^2 + y^3 = 3) :
    x = 1 ∧ y = 1 ∧ z = 1 := by
  have h4 : x ≤ 3 := by nlinarith [sq_nonneg (y - 1), sq_nonneg (z - 1), h1, h2, h3]
  have h5 : y ≤ 3 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (z - 1), h1, h2, h3]
  have h6 : z ≤ 3 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), h1, h2, h3]
  have h7 : x ≥ 1 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), h1, h2, h3]
  have h8 : y ≥ 1 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), h1, h2, h3]
  have h9 : z ≥ 1 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), h1, h2, h3]
  have hx1 : x = 1 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), h1, h2, h3]
  have hy1 : y = 1 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), h1, h2, h3]
  have hz1 : z = 1 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), h1, h2, h3]
  exact ⟨hx1, hy1, hz1⟩