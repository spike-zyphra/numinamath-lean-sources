import Mathlib

theorem algebra_14099 (x y z : ℝ) (h₁ : x + y = 2) (h₂ : x * y - z ^ 2 = 1) :
    (x, y, z) = (1, 1, 0) := by
  have h3 : y = 2 - x := by linarith
  rw [h3] at h₂
  have h3' : (x - 1) ^ 2 + z ^ 2 = 0 := by
    nlinarith
  have hx1 : (x - 1) ^ 2 = 0 := by
    linarith [sq_nonneg (x - 1), sq_nonneg z]
  have hx2 : x = 1 := by
    nlinarith
  have hz1 : z ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg z]
  have hz2 : z = 0 := by
    nlinarith
  have hy2 : y = 1 := by
    linarith [h₁, hx2]
  simp [hx2, hy2, hz2]
  all_goals linarith