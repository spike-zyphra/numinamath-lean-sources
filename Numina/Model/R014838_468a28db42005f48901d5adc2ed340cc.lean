import Mathlib

theorem algebra_199214 {x y z : ℝ} (h₀ : x^3 - y = 6) (h₁ : y^3 - z = 6) (h₂ : z^3 - x = 6) :
    x = 2 ∧ y = 2 ∧ z = 2 := by

  have h3 : (x - 2) ^ 2 + (y - 2) ^ 2 + (z - 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2),
      sq_nonneg (x^2 - 4), sq_nonneg (y^2 - 4), sq_nonneg (z^2 - 4),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have hx1 : x - 2 = 0 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2)]
  have hy1 : y - 2 = 0 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2)]
  have hz1 : z - 2 = 0 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2)]
  have hx2 : x = 2 := by
    linarith
  have hy2 : y = 2 := by
    linarith
  have hz2 : z = 2 := by
    linarith
  exact ⟨hx2, hy2, hz2⟩