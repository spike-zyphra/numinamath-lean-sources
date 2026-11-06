import Mathlib

theorem algebra_197684 (x : ℝ) :
    (8 * x + 13) / 3 = (19 - 12 * x) / 2 - (16 * x - (7 - 4 * x) / 6) ↔
    x = 1 / 4 := by
  constructor
  · -- Forward direction: Equation implies x = 1/4
    intro h
    linarith
  · -- Backward direction: x = 1/4 implies Equation
    intro h
    rw [h]
    norm_num