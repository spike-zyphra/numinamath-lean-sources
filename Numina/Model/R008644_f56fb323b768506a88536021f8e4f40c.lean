import Mathlib

theorem algebra_11960 : {x : ℝ | x / 3 = x / 4 + 50} = {600} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x / 3 = x / 4 + 50, prove x = 600
    intro h
    linarith
  · -- Assume x = 600, prove x / 3 = x / 4 + 50
    intro h
    rw [h]
    norm_num