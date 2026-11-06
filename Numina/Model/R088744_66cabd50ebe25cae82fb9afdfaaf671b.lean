import Mathlib

theorem algebra_6287 (d1 d2 t1 t2 : ℝ) (h1 : d1 = 80 * t1) (h2 : d2 = 40 * t2)
    (ht1 : t1 = 2 * 60) (ht2 : t2 = 1 * 60) : (d1 + d2) / (t1 + t2) = 66 + 2 / 3 := by
  have ht1' : t1 = 120 := by
    rw [ht1]
    norm_num
  have ht2' : t2 = 60 := by
    rw [ht2]
    norm_num
  have hd1 : d1 = 9600 := by 
    rw [h1]
    rw [ht1']
    norm_num
  have hd2 : d2 = 2400 := by 
    rw [h2]
    rw [ht2']
    norm_num
  have total_distance : d1 + d2 = 12000 := by 
    rw [hd1, hd2]
    norm_num
  have total_time : t1 + t2 = 180 := by 
    rw [ht1', ht2']
    norm_num
  rw [total_distance, total_time]
  norm_num