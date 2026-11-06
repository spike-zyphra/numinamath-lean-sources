import Mathlib

theorem algebra_13368 : {r : ℝ | (r - 45) / 2 = (3 - 2 * r) / 5} = {77 / 3} := by 
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume h: (r - 45) / 2 = (3 - 2 * r) / 5, derive r = 77 / 3
    intro h
    linarith
  · -- Assume r = 77 / 3, derive (r - 45) / 2 = (3 - 2 * r) / 5
    intro h
    rw [h]
    norm_num