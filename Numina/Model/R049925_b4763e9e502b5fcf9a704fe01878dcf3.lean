import Mathlib

theorem inequalities_298093 (a : ℝ) (ha : a > 1) : a^3 - 1 / a > a - 1 := by
  have h1 : a > 0 := by linarith
  have h2 : a^4 - a^2 + a - 1 > 0 := by
    have h2a : (a - 1) > 0 := by linarith
    have h3 : a^3 + a^2 + 1 > 0 := by
      nlinarith [sq_nonneg (a + 1), sq_nonneg (a - 1)]
    have h2b : (a - 1) * (a^3 + a^2 + 1) = a^4 - a^2 + a - 1 := by
      ring
    nlinarith [h2a, h3]
  have h4a : a^3 - 1 / a - (a - 1) = (a^4 - a^2 + a - 1) / a := by
    field_simp
    all_goals
      nlinarith [sq_nonneg (a + 1), sq_nonneg (a - 1)]
  have h4 : a^3 - 1 / a - (a - 1) > 0 := by 
    have h4b : a > 0 := h1
    rw [h4a]
    have h5 : a^4 - a^2 + a - 1 > 0 := h2
    apply div_pos
    linarith
    linarith
  linarith [h4]