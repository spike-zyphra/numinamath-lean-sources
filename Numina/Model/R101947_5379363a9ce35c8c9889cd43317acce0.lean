import Mathlib

theorem algebra_181500 (d1 d2 t1 t2 : ℝ) (h1 : d1 = 275) (h2 : d2 = 405)
    (ht1 : t1 > 0) (ht2 : t2 > 0) (h3 : d1 / 5 = t1 - 17) (h4 : d2 / 3 = t2 - 17)
    (h5 : t2 = t1 + 1 / 30) :
    t1 = 14 := by
  rw [h1] at h3
  rw [h2] at h4
  linarith