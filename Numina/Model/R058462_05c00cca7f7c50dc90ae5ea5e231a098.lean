import Mathlib

theorem algebra_303211 {x y z : ℝ} (h1 : (x - 2) ^ 2 + (y + 3 / 2) ^ 2 + (z - 6) ^ 2 = 64)
    (h2 : (x + 2) ^ 2 + (y - 3 / 2) ^ 2 + (z + 6) ^ 2 = 25) :
    x = -6 / 13 ∧ y = 9 / 26 ∧ z = -18 / 13 := by
  have h3 : 8 * x - 6 * y + 24 * z = -39 := by 
    nlinarith
  have hx : x = -6 / 13 := by
    nlinarith [sq_nonneg (x + 6 / 13), sq_nonneg (y - 9 / 26), sq_nonneg (z + 18 / 13)]
  have hy : y = 9 / 26 := by
    nlinarith [sq_nonneg (x + 6 / 13), sq_nonneg (y - 9 / 26), sq_nonneg (z + 18 / 13)]
  have hz : z = -18 / 13 := by
    nlinarith [sq_nonneg (x + 6 / 13), sq_nonneg (y - 9 / 26), sq_nonneg (z + 18 / 13)]
  exact ⟨hx, hy, hz⟩