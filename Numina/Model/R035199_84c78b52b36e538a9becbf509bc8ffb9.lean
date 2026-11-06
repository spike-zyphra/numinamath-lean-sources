import Mathlib

theorem inequalities_73198 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a^3 + b^3 = 2) :
    2 * (a^2 - a + 1) * (b^2 - b + 1) ≤ 1 / a + 1 / b := by
  have h1 : 0 < a * b := by
    nlinarith
  have eq3 : 2 * (a^2 - a + 1) * (b^2 - b + 1) ≤ 1 / a + 1 / b := by
    have h4 : 2 * (a^2 - a + 1) * (b^2 - b + 1) ≤ (a + b) / (a * b) := by
      have h5 : 0 < a * b := by
        nlinarith
      have h10 : 2 * (a * b) * (a^2 - a + 1) * (b^2 - b + 1) ≤ a + b := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a^2 - b^2), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a * b - 1), sq_nonneg (a^3 - b^3), mul_pos ha hb, h, sq_nonneg (a^2 - b^2), sq_nonneg (a * b * (a - b))]
      have h11 : 0 < a * b := by
        nlinarith
      have : 2 * (a^2 - a + 1) * (b^2 - b + 1) ≤ (a + b) / (a * b) := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < a * b)).mpr
        nlinarith [h10, mul_pos ha hb]
      linarith
    have eq4 : 1 / a + 1 / b = (a + b) / (a * b) := by
      field_simp
      <;> ring
    linarith [h4, eq4]
  linarith [eq3]