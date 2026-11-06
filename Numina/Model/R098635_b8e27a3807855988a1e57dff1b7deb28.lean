import Mathlib

theorem algebra_243999 (d1 d2 d3 t1 t2 t3 : ℝ)
    (h1 : d1 = 12 * t1) (h2 : d2 = 15 * t2) (h3 : d3 = 18 * t3)
    (ht1 : t1 = 5 / 60) (ht2 : t2 = 10 / 60) (ht3 : t3 = 15 / 60) :
    (d1 + d2 + d3) / (t1 + t2 + t3) = 16 := by
  have hd1 : d1 = 1 := by
    rw [h1, ht1]
    norm_num
  have hd2 : d2 = 2.5 := by 
    rw [h2, ht2]
    norm_num
  have hd3 : d3 = 4.5 := by 
    rw [h3, ht3]
    norm_num
  have ht_total : t1 + t2 + t3 = 0.5 := by 
    rw [ht1, ht2, ht3]
    norm_num
  rw [hd1, hd2, hd3, ht_total]
  norm_num