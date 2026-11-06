import Mathlib

theorem algebra_174101 (d t1 t2 : ℝ) (ht1 : t1 = d / 50) (ht2 : t2 = d / 30)
    (ht3 : t2 = t1 + 10 / 60) :
    d = 12.5 := by
  rw [ht1, ht2] at ht3
  linarith