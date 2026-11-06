import Mathlib

theorem algebra_201931 {x y z : ℝ} (h1 : x^2 - 2 * y + 1 = 0) (h2 : y^2 - 4 * z + 7 = 0) (h3 : z^2 + 2 * x - 2 = 0) :
    x = -1 ∧ y = 1 ∧ z = 2 := by
  -- Now we need to manipulate the system.
  -- We will compute the sum of the equations to get a square sum equal to zero.
  have h4 : (x + 1) ^ 2 + (y - 1) ^ 2 + (z - 2) ^ 2 = 0 := by
    nlinarith
  have hx : x + 1 = 0 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 1), sq_nonneg (z - 2)]
  have hy : y - 1 = 0 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 1), sq_nonneg (z - 2)]
  have hz : z - 2 = 0 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 1), sq_nonneg (z - 2)]
  have hx2 : x = -1 := by linarith
  have hy2 : y = 1 := by linarith
  have hz2 : z = 2 := by linarith
  exact ⟨hx2, hy2, hz2⟩