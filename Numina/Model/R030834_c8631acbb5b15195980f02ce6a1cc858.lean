import Mathlib

theorem algebra_289497 :
  {x : ℚ | (9/7 : ℚ) * (5/6 : ℚ) * x - x = 50} = {700} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume (9/7 : ℚ) * (5/6 : ℚ) * x - x = 50, prove x = 700
    intro h
    linarith
  · -- Assume x = 700, prove (9/7 : ℚ) * (5/6 : ℚ) * x - x = 50
    intro h
    rw [h]
    norm_num