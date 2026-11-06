import Mathlib

theorem other_202549 (m : ℝ) (h : m = 1) :
    m = 100 / 100 ∧ 40 / 10 = 4 ∧ 10 / 10 = 1 := by
  constructor
  · -- m = 100 / 100
    rw [h]
    norm_num
  constructor
  · -- 40 / 10 = 4
    norm_num
  · -- 10 / 10 = 1
    norm_num