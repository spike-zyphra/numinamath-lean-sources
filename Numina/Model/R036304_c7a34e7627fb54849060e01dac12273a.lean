import Mathlib

theorem algebra_598479 (x y z : ℝ) (h₀ : 2 * x + 3 * y + z = 13) (h₁ : 4 * x ^ 2 + 9 * y ^ 2 + z ^ 2 - 2 * x + 15 * y + 3 * z = 82) :
    x = 3 ∧ y = 1 ∧ z = 4 := by
  have h2 : z = 13 - 2 * x - 3 * y := by
    linarith
  rw [h2] at h₁
  have h3 : (x - 3) ^ 2 + (y - 1) ^ 2 + (z - 4) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 1), sq_nonneg (z - 4), 
      h₀, sq_nonneg (2 * x + 3 * y - 7)]
  have hx : x = 3 := by
    nlinarith [h3, sq_nonneg (x - 3), sq_nonneg (y - 1), sq_nonneg (z - 4)]
  have hy : y = 1 := by
    nlinarith [h3, sq_nonneg (x - 3), sq_nonneg (y - 1), sq_nonneg (z - 4)]
  have hz : z = 4 := by
    nlinarith [h3, sq_nonneg (x - 3), sq_nonneg (y - 1), sq_nonneg (z - 4)]
  exact ⟨hx, hy, hz⟩