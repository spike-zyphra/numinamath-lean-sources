import Mathlib

theorem algebra_14454 (d t1 t2 : ℝ) (ht1 : t1 = 4.5) (hd : d = 70 * t1)  (ht2 : t2 = d / 60):
    t2 = 5.25 := by
  rw [ht1] at hd
  rw [hd] at ht2
  rw [ht2]
  norm_num