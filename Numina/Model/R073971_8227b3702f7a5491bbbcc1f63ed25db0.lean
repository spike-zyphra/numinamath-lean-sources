import Mathlib

theorem algebra_2719 {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : (a - b)^2 + (b - a) * |a - b| = a * b) : ¬(a * b < 0) := by
  by_contra h
  have h1 : a * b < 0 := by linarith
  by_cases h2 : a - b ≥ 0
  · -- Case where $a - b \geq 0$, so $|a - b| = a - b$
    have h3 : |a - b| = a - b := by
      rw [abs_of_nonneg h2]
    rw [h3] at hab
    nlinarith [sq_nonneg (a - b), sq_pos_of_ne_zero (show a ≠ 0 by assumption), sq_pos_of_ne_zero (show b ≠ 0 by assumption)]
  · -- Case where $a - b < 0$, so $|a - b| = b - a$
    have h3 : |a - b| = b - a := by
      rw [abs_of_neg (lt_of_not_ge h2)]
      all_goals ring
    rw [h3] at hab
    have h4 : 2 * (a - b) ^ 2 = a * b := by
      nlinarith
    have h5 : a * b ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_pos_of_ne_zero (show a ≠ 0 by assumption), sq_pos_of_ne_zero (show b ≠ 0 by assumption)]
    nlinarith