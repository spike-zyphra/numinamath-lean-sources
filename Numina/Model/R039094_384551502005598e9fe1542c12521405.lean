import Mathlib

theorem algebra_289688 :
  {x : ℝ | 4 * x * (10 * x - (-10 - (3 * x - 8 * (x + 1)))) + 5 * (12 - (4 * (x + 1) - 3 * x)) =
    18 * x ^ 2 - (6 * x ^ 2 - (7 * x + 4 * (2 * x ^ 2 - x + 11)))} = ∅ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  nlinarith