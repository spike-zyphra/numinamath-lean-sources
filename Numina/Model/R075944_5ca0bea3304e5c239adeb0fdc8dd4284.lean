import Mathlib

theorem inequalities_245058 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^3 / (a^2 + a * b + b^2)) + (b^3 / (b^2 + b * c + c^2)) +
    (c^3 / (c^2 + c * a + a^2)) ≥ (a + b + c) / 3 := by 
  have h1 : a^3 / (a^2 + a * b + b^2) ≥ (2 * a - b)/3 := by
    have h2 : 0 < a^2 + a * b + b^2 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_nonneg (a - b)]
    apply (le_div_iff₀ h2).mpr
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 2 * b), sq_nonneg (a + 2 * b), mul_pos ha hb]
  have h2 : b^3 / (b^2 + b * c + c^2) ≥ (2 * b - c)/3 := by
    have h3 : 0 < b^2 + b * c + c^2 := by
      nlinarith [sq_pos_of_pos hb, sq_pos_of_pos hc, sq_nonneg (b - c)]
    apply (le_div_iff₀ h3).mpr
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (b - 2 * c), sq_nonneg (b + 2 * c), mul_pos hb hc]
  have h3 : c^3 / (c^2 + c * a + a^2) ≥ (2 * c - a)/3 := by
    have h4 : 0 < c^2 + c * a + a^2 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hc, sq_nonneg (c - a)]
    apply (le_div_iff₀ h4).mpr
    nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (c - 2 * a), sq_nonneg (c + 2 * a), mul_pos ha hc]
  linarith [h1, h2, h3]