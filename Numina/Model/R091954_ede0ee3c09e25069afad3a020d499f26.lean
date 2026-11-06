import Mathlib

theorem inequalities_1459 (a : ℝ) : 2 * a^4 + 1 / (1 + a^2) ≥ 3 * a^2 - 1 := by 
  have h1 : 1 + a^2 > 0 := by
    suffices a^2 ≥ 0 by linarith
    exact sq_nonneg a
  have h2 : 2 * a^4 + 1 / (1 + a^2) - (3 * a^2 - 1) ≥ 0 := by
    have h3 : (2 * a^4 + 1 / (1 + a^2) - (3 * a^2 - 1)) = (2 * a^6 - a^4 - 2 * a^2 + 2) / (1 + a^2) := by
      field_simp at *
      ring 
    rw [h3]
    apply div_nonneg
    · -- Show that the numerator is non-negative 
      nlinarith [sq_nonneg (a^3), sq_nonneg (a^2 - 1), sq_nonneg (a), sq_nonneg (a^2 - 2)]
    · -- Show that the denominator is positive 
      linarith [h1]
  linarith