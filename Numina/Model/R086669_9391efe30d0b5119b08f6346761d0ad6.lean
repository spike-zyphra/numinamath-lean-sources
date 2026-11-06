import Mathlib

theorem algebra_303075 :
    IsLeast {t : ℝ | ∃ x y, t = x^2 + y^2 ∧ x^3 + y^3 + 3 * x * y = 1} (1 / 2) := by
  constructor
  · -- Show that 1/2 is achievable, by finding specific x and y
    use 1 / 2, 1 / 2
    constructor
    · -- Verify that 1/2 = x^2 + y^2
      norm_num
    · -- Verify that x^3 + y^3 + 3 * x * y = 1
      norm_num
  · -- Show that 1/2 is a lower bound
    intro t ht
    rcases ht with ⟨x, y, ht_eq, h_eq⟩
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2)]