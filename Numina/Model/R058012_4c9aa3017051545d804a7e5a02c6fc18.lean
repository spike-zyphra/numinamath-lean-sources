import Mathlib

theorem algebra_301751 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (h : a^3 - b^3 = a^2 - b^2) :
    1 < a + b ∧ a + b < 4 / 3 := by
  have h1 : a^2 + a * b + b^2 = a + b := by
    have h2 : a - b ≠ 0 := sub_ne_zero_of_ne hab
    have eq1 : a^3 - b^3 = (a - b) * (a^2 + a * b + b^2) := by ring
    have eq2 : a^2 - b^2 = (a - b) * (a + b) := by ring
    rw [eq1, eq2] at h
    have h3 : (a - b) * (a^2 + a * b + b^2) = (a - b) * (a + b) := by linarith
    have h4 : a^2 + a * b + b^2 = a + b := by
      apply (mul_left_inj' h2).mp
      linarith
    exact h4
  have h3 : 1 < a + b := by
    nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by exact sub_ne_zero_of_ne hab), sq_pos_of_pos ha, sq_pos_of_pos hb]
  have h4 : a + b < 4 / 3 := by
    nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by exact sub_ne_zero_of_ne hab), sq_pos_of_pos ha, sq_pos_of_pos hb]
  constructor
  · exact h3
  · exact h4