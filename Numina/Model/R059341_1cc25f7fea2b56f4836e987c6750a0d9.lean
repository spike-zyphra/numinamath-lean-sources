import Mathlib

theorem other_143586 {a b : ℝ} (ha : a = 11 / 100) (hb : b = 20 / 100)
    (h : a * 71 = b * 85) :
    b / a = 3.97 := by
  rw [ha, hb] at h
  all_goals
    norm_num at h
    all_goals
      norm_num [ha, hb] at *
      <;> linarith