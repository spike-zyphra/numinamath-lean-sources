import Mathlib

theorem algebra_248561 :
    {x : ℝ | x + (16 * (2 * (x - 3000) - 15 * 3000)) / 2 + (16 * (2 * (x - 4500) - 15 * 4500)) / 2 = 25 * (x - 12000)} = {90000} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume the equation holds, prove x = 90000
    intro h
    linarith
  · -- Assume x = 90000, prove the equation
    intro h
    rw [h]
    norm_num