import Mathlib

theorem algebra_21594 : {x : ℝ | x / 7 + x / 3 = 1 - x} = {21 / 31} := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x / 7 + x / 3 = 1 - x, prove x = 21 / 31 
    intro h
    linarith
  · -- Assume x = 21 / 31, prove x / 7 + x / 3 = 1 - x
    intro h
    rw [h]
    norm_num