import Mathlib

theorem algebra_279160 (x : ℝ) (hx : x > 0) (h : 42000 / x = 56000 / (x - 42000)) :
    x = 48000 := by

  have h1 : x ≠ 0 := by linarith
  have h2 : x - 42000 ≠ 0 := by
    by_contra h2
    have hx_eq : x = 42000 := by linarith
    rw [hx_eq] at h
    norm_num [hx_eq] at h
    all_goals linarith
  field_simp [h1, h2] at h
  nlinarith