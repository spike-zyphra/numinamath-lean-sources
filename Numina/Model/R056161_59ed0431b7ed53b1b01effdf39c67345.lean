import Mathlib

theorem algebra_97781 (d1 d2 d3 v1 v2 v3 : ℝ)
    (h1 : d1 = 1 / 4) (h2 : d2 = 3) (h3 : d3 = 15)
    (h4 : v1 = 2) (h5 : v2 = 6) (h6 : d1 / v1 + d2 / v2 + d3 / v3 = 2) :
    v3 = 120 / 11 := by
  rw [h1, h4, h2, h5, h3] at h6
  have h8 : v3 ≠ 0 := by
    by_contra h
    rw [h] at h6
    norm_num at h6 ⊢
    all_goals linarith
  field_simp at h6 ⊢
  nlinarith