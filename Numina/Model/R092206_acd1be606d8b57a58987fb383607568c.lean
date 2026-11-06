import Mathlib

theorem algebra_233960 (l w : ℝ) (hl : l > 0) (hw : w > 0)
    (h : (l * w) * 1.35 * 0.86 = (l * w) * (1 + x / 100)) :
    x = 16.1 := by
  have h1 : l * w > 0 := by
    apply mul_pos
    exact hl
    exact hw
  -- notice that left side = right side * some ratio, multiply through by 1/pos to solve
  have h2 : 1.35 * (0.86 : ℝ) = (1 + x / 100 : ℝ) := by
    apply (mul_left_inj' (ne_of_gt h1)).mp
    linarith
  have h3 : (1.35 : ℝ) * (0.86 : ℝ) = 1.161 := by norm_num
  rw [h3] at h2
  norm_num at h2
  linarith