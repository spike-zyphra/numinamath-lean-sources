import Mathlib

theorem inequalities_81714 (a : ℝ) (ha : a ≠ 1) :
    (1 + a + a^2)^2 < 3 * (1 + a^2 + a^4) := by
  have h1 : a - 1 ≠ 0 := by
    intro h
    apply ha
    linarith
  have h2 : (1 + a + a^2) > 0 := by
    nlinarith [sq_nonneg (a + 1 / 2), sq_nonneg (a), sq_nonneg (a - 1)]
  have h3 : (a - 1) ^ 2 > 0 := by
    apply sq_pos_of_ne_zero
    exact h1
  nlinarith [sq_pos_of_pos (show 0 < (a - 1) ^ 2 by nlinarith), sq_nonneg (a - 1), sq_nonneg (a + 1), h2]