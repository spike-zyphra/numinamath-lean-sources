import Mathlib

theorem algebra_235608 (v : ℝ) (h : v > 0) (h1 : 90 / v = 2) :
    225 / v = 5 := by
  have hv : v = 45 := by
    have h2 : v ≠ 0 := by linarith
    field_simp at h1
    linarith 
  rw [hv]
  norm_num