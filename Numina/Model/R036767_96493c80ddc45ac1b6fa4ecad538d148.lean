import Mathlib

theorem algebra_21882 (v : ℝ) (h : v = 1 / 2.5) (l : ℝ) (hl : l / v = 90 / 3600) :
    l * 1000 = 10 := by

  have h1 : v = (2 / 5 : ℝ) := by
    rw [h]
    norm_num

  have h2 : l = (1 / 100 : ℝ) := by
    have eq1 : l / v = (90 / 3600 : ℝ) := by
      linarith
    rw [h1] at eq1
    field_simp at eq1 ⊢
    linarith

  rw [h2]
  norm_num