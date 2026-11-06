import Mathlib

theorem algebra_191083 (d t1 t2 : ℝ) (ht1 : t1 = d / 60) (ht2 : t2 = d / 65)
    (h1 : t1 + 1 / 60 = t2 - 1 / 65) (h2 : d > 0) :
    d = 52 := by
  rw [ht1, ht2] at h1
  linarith