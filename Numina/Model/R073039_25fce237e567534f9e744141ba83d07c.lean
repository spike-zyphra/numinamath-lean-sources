import Mathlib

theorem inequalities_136902 (a : ℝ) (ha : a ≠ 1) :
    (1 + a + a^2)^2 < 3 * (1 + a^2 + a^4) := by 
  have h1 : (a - 1) ^ 2 > 0 := by 
    apply sq_pos_of_ne_zero
    intro h
    apply ha
    linarith
  have h2 : 1 + a + a^2 > 0 := by
    nlinarith [sq_nonneg (a - 0.5), sq_nonneg (a + 0.5)]
  have h3 : (1 + a + a^2) ^ 2 - 3 * (1 + a^2 + a^4) < 0 := by
    nlinarith [sq_pos_of_ne_zero (show a - 1 ≠ 0 by
      intro h'
      apply ha
      linarith), sq_nonneg (a + 0.5), sq_nonneg (a - 0.5), sq_nonneg (a^2 - a), sq_nonneg (a^2 + a + 1 - 1), sq_nonneg (a^2 + a + 1), sq_nonneg (a - 1)]
  linarith