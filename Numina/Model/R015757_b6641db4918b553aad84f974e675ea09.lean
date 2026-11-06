import Mathlib

theorem algebra_6906 (d1 d2 t1 t2 : ℝ) (ht1 : t1 = 60) (ht2 : t2 = 120) (hd1 : d1 = 80 * t1) (hd2 : d2 = 40 * t2) :
    (d1 + d2) / (t1 + t2) = 53 + 1 / 3 := by
  have ht1' : t1 = 60 := ht1
  have ht2' : t2 = 120 := ht2
  have hd1' : d1 = 4800 := by 
    rw [hd1, ht1']
    norm_num
  have hd2' : d2 = 4800 := by 
    rw [hd2, ht2']
    norm_num
  have h1 : (d1 + d2 : ℝ) = 9600 := by
    rw [hd1', hd2']
    norm_num
  have h2 : (t1 + t2 : ℝ) = 180 := by
    rw [ht1', ht2']
    norm_num
  rw [h1, h2]
  norm_num