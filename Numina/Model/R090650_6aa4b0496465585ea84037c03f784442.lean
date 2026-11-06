import Mathlib

theorem algebra_180921 (v1 v2 : ℝ) (h : v1 = 3 * v2) (h' : v2 ≠ 0) (h'' : 10 / v2 = 30 / 60) :
    (50 / v1 + 10 / v2) * 60 = 80 := by
  have hv2 : v2 = 20 := by
    field_simp [h'] at h''
    linarith
  have hv1 : v1 = 60 := by
    rw [show v2 = 20 by linarith [hv2]] at h
    linarith
  rw [hv1, hv2]
  norm_num