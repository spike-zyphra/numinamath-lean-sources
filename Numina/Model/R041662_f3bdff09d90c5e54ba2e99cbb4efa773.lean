import Mathlib

theorem algebra_251703 (d : ℝ) (h : d > 0) (h1 : 4 * d / (26 + 6) + 4 * d / (26 - 6) = 13) :
    d = 40 := by
  have eq1 : 4 * d / (26 + 6) + 4 * d / (26 - 6) = 4 * d / 32 + 4 * d / 20 := by
    norm_num
  rw [eq1] at h1
  have eq2 : (4 * d / 32 + 4 * d / 20 : ℝ) = (13 / 40) * d := by
    field_simp
    ring_nf
  rw [eq2] at h1
  linarith