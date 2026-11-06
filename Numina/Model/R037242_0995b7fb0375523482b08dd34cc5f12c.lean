import Mathlib

theorem algebra_222248 (l : ℝ) (hl : l = 110) (v : ℝ) (h : v = 25 / 3)
    (t1 t2 : ℝ) (ht1 : t1 = 9.10) (ht2 : t2 = 9.16) (h1 : l / v = 15) (h2 : l / (v + w) = 12)
    (w : ℝ) (hw : w > 0) :
    (l + w * 15) / (v + w) = 9.40 := by
  rw [hl, h] at h1
  norm_num at h1
  all_goals linarith