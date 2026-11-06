import Mathlib

theorem algebra_249201 (d t1 t2 : ℝ) (ht1 : t1 = d * (1 / 2) / 50 + d * (1 / 2) / (50 * 1.2)) (ht2 : t2 = d * (1 / 3) / 50 + d * (2 / 3) / (50 * 1.32)) (hd : d > 0) (h : t2 = t1 - 31 / 60) : d = 330 := by 
  rw [ht1] at h 
  rw [ht2] at h
  norm_num at h 
  linarith