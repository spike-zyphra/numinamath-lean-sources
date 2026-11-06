import Mathlib

theorem algebra_130207 {x y : ℝ} (h : (x + y)^2 = (x + 3) * (y - 3)) :
    (x, y) = (-3, 3) := by
  have eq1 : (x + y)^2 = (x + 3) * (y - 3) := h
  have eq2 : (x + y)^2 - (x + 3) * (y - 3) = 0 := by linarith
  have h1 : 4 * (x + (y + 3) / 2) ^ 2 + 3 * (y - 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x + (y + 3) / 2), sq_nonneg (y - 3),
              eq2]
  have h2 : (x + (y + 3) / 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x + (y + 3) / 2), sq_nonneg (y - 3)]
  have h3 : y - 3 = 0 := by
    nlinarith [sq_nonneg (x + (y + 3) / 2), sq_nonneg (y - 3)]
  have hy : y = 3 := by linarith
  have hx : x = -3 := by
    have h4 : x + (3 + 3) / 2 = 0 := by
      rw [hy] at h2
      nlinarith [h2]
    linarith
  simp [hx, hy]