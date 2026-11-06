import Mathlib

theorem algebra_289509 (x y z : ℝ)
    (h1 : x > 0) (h2 : y > 0) (h3 : z > 0)
    (h4 : 1 / x = 6 * 60 + 40) (h5 : 1 / y = 8 * 60)
    (h6 : 1 / z = 13 * 60 + 20) :
    1 / (x + y - z) = 5 * 60 := by
  have hx1 : x = 1 / (6 * 60 + 40) := by
    field_simp at h4 ⊢
    all_goals linarith
  have hy1 : y = 1 / (8 * 60) := by
    field_simp at h5 ⊢
    all_goals linarith
  have hz1 : z = 1 / (13 * 60 + 20) := by
    field_simp at h6 ⊢
    all_goals linarith

  rw [hx1, hy1, hz1]

  norm_num