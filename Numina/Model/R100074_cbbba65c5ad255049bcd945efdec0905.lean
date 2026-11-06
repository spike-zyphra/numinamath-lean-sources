import Mathlib

theorem algebra_199458 (d t1 t2 : ℝ) (ht1 : t1 > 0) (ht2 : t2 > 0)
    (h1 : d / t1 = d / t2 + 1) (h2 : d / t1 = 45 / 60) (h3 : d / t2 = 1 * 60 + 20) :
    d = 7 := by
  have h5 : d / t2 = 80 := by
    linarith
  have h6 : d / t1 = 81 := by
    linarith [h1, h5]
  have h7 : 81 = (45 : ℝ) / 60 := by 
    linarith [h2, h6]
  norm_num at h7
  all_goals linarith