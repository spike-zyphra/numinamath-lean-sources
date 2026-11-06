import Mathlib

theorem algebra_5567 : {x : ℝ | x - 2 * x / 5 = (7 + x) / 4} = {5} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x - 2x/5 = (7 + x)/4, prove x = 5
    intro h
    linarith
  · -- Assume x = 5, prove x - 2x/5 = (7 + x)/4
    intro h
    rw [h]
    norm_num