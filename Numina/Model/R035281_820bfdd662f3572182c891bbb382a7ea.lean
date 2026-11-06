import Mathlib

theorem algebra_618628 (v1 v2 d1 d2 t1 t2 : ℝ) (h1 : v1 = 20) (h2 : d1 = 4) (h3 : t1 = d1 / v1)
    (h4 : t2 = 20 / 60) (h5 : v2 = 12) (h6 : d2 = 8) (h7 : t3 = d2 / v2) :
    (d1 + d2) / (t1 + t2 + t3) = 10 := by
  have ht1 : t1 = 0.2 := by
    rw [h3, h2, h1]
    norm_num
  have ht2 : t2 = (1 / 3 : ℝ) := by 
    rw [h4]
    norm_num
  have ht3 : t3 = (2 / 3 : ℝ) := by
    rw [h7, h6, h5]
    norm_num
  have h8 : d1 + d2 = (12 : ℝ) := by
    rw [h2, h6]
    norm_num
  have h9 : t1 + t2 + t3 = (6 / 5 : ℝ) := by
    rw [ht1, ht2, ht3]
    norm_num
  rw [h8, h9]
  all_goals norm_num