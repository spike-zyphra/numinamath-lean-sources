import Mathlib

theorem algebra_19356 : {r : ℝ | -13 * (r + 5) + 25 > 4 * (r - 10)} = Set.Iio 0 := by
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_Iio]
  constructor
  · -- Assume the inequality holds, prove r < 0
    intro h
    linarith
  · -- Assume r < 0, prove the inequality holds
    intro h
    linarith