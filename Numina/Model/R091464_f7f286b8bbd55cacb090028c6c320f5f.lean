import Mathlib

theorem algebra_326028 (A B : ℝ) (hA : A = 2 * 300) (hB : B = 0.2 * 300)
    (h : A * 100 = B * 200) :
    A * 9 = B * 10 := by
  rw [hA, hB] at h
  norm_num at h
  all_goals linarith