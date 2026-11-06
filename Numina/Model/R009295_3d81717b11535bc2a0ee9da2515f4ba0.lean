import Mathlib

theorem algebra_14411 : {x : ℚ | x / 2 = 1 / 7} = {2 / 7} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x / 2 = 1 / 7, we need to show x = 2 / 7
    intro h
    linarith
  · -- Assume x = 2 / 7, we need to show x / 2 = 1 / 7
    intro h
    rw [h]
    norm_num