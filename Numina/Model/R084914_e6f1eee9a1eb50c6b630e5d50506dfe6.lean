import Mathlib

theorem algebra_165770 (a b : ℝ) (ha : a = 27 * 5 * 5 + 27 * 8 * 15) (hb : b = 25 * 1000)
    (h : a + b ≥ 60 * 1000) :
    a + b = 64.15 * 1000 := by
  rw [ha, hb] at h ⊢
  norm_num at h ⊢
  all_goals linarith