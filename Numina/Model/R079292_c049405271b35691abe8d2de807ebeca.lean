import Mathlib

theorem calculus_15381 (x y z : ℝ) (h : x = 4) (h1 : (x - 2) / (5 - 2) = (y - 2) / (1 - 2)) (h2 : (y - 2) / (1 - 2) = (z - 1) / (-2 - 1)) :
    z = -1 := by
  rw [h] at h1
  have hy : y = 4 / 3 := by
    field_simp at h1
    linarith
  rw [hy] at h2
  field_simp at h2
  linarith