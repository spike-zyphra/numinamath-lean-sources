import Mathlib

theorem other_235613 (d : ℝ) (h : d = 19) :
    3 < d / 5 ∧ d / 5 < 4 := by
  rw [h]
  constructor
  · norm_num
  · norm_num