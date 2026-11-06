import Mathlib

theorem algebra_13500 (l w h : ℝ) (hl : l = 3) (hw : w > 0) (h1 : h = 12)
    (h2 : √(l^2 + w^2 + h^2) = 13) : w = 4 := by
  have eq1 : √(3^2 + w^2 + 12^2) = 13 := by
    rw [hl, h1] at h2
    exact h2
  have eq2 : (3 : ℝ) ^ 2 + w ^ 2 + (12 : ℝ) ^ 2 = (13 : ℝ) ^ 2 := by
    have h3 : √(3^2 + w^2 + 12^2) = 13 := eq1
    have h4 : (√(3^2 + w^2 + 12^2)) ^ 2 = (13 : ℝ) ^ 2 := by
      rw [h3]
    rw [Real.sq_sqrt] at h4
    · linarith
    · positivity
  norm_num at eq2
  nlinarith [sq_nonneg w, hw]