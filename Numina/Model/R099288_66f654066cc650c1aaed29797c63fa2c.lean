import Mathlib

theorem algebra_5936 (d1 d2 t1 t2 : ℝ) (h1 : d1 = 80 * t1) (h2 : d2 = 60 * t2)
    (ht1 : t1 = 3) (ht2 : t2 = 1) :
    (d1 + d2) / (t1 + t2) / 60 = 1 + 1 / 4 := by
  have hd1 : d1 = 240 := by 
    rw [h1, ht1]
    norm_num
  have hd2 : d2 = 60 := by 
    rw [h2, ht2]
    norm_num
  have ht : t1 + t2 = 4 := by 
    rw [ht1, ht2]
    norm_num
  rw [hd1, hd2, ht]
  norm_num