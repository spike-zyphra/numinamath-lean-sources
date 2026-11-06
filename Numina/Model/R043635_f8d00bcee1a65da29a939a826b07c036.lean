import Mathlib

theorem inequalities_292204 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^3 / (a^2 + a * b + b^2) + b^3 / (b^2 + b * c + c^2) +
    c^3 / (c^2 + c * a + a^2) ≥
    (1 / 3) * (a + b + c) := by
  have h1 : a ^ 3 / (a^2 + a * b + b^2) ≥ (2 * a - b) / 3 := by
    have h1 : 0 < a^2 + a * b + b^2 := by
      nlinarith [mul_pos ha hb, sq_pos_of_pos ha, sq_pos_of_pos hb]
    apply (le_div_iff₀ h1).mpr
    have h2 : 3 * a^3 ≥ (2 * a - b) * (a^2 + a * b + b^2) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b),
          sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), mul_pos ha hb, mul_pos ha (show 0 < a * b by nlinarith)]
    linarith
  have h2 : b ^ 3 / (b^2 + b * c + c^2) ≥ (2 * b - c) / 3 := by
    have h1 : 0 < b^2 + b * c + c^2 := by
      nlinarith [mul_pos hb hc, sq_pos_of_pos hb, sq_pos_of_pos hc]
    apply (le_div_iff₀ h1).mpr
    have h3 : 3 * b^3 ≥ (2 * b - c) * (b^2 + b * c + c^2) := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (b * c),
          sq_nonneg (b * (b - c)), sq_nonneg (c * (b - c)), mul_pos hb hc, mul_pos hb (show 0 < b * c by nlinarith)]
    linarith
  have h3 : c ^ 3 / (c^2 + c * a + a^2) ≥ (2 * c - a) / 3 := by
    have h1 : 0 < c^2 + c * a + a^2 := by
      nlinarith [mul_pos hc ha, sq_pos_of_pos hc, sq_pos_of_pos ha]
    apply (le_div_iff₀ h1).mpr
    have h4 : 3 * c^3 ≥ (2 * c - a) * (c^2 + c * a + a^2) := by
      nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (c * a),
          sq_nonneg (c * (c - a)), sq_nonneg (a * (c - a)), mul_pos hc ha, mul_pos hc (show 0 < c * a by nlinarith)]
    linarith
  linarith [h1, h2, h3]