import Mathlib

theorem algebra_195526 (a : ℝ) (ha : a < -1) :
    (a^2 - 2 * a - 1 > 0 ∧ (a + 1) / abs (a + 1) < 0) := by
  have h1 : a + 1 < 0 := by linarith
  have h2 : a ^ 2 - 2 * a - 1 > 0 := by
    nlinarith [sq_nonneg (a + 1)]
  have h3 : abs (a + 1) = -(a + 1) := by
    rw [abs_of_neg h1]
  have h4 : (a + 1) / abs (a + 1) < 0 := by
    rw [h3]
    apply div_neg_of_neg_of_pos
    · -- Show that a + 1 < 0
      linarith
    · -- Show that -(a + 1) > 0
      linarith
  constructor
  · exact h2
  · exact h4