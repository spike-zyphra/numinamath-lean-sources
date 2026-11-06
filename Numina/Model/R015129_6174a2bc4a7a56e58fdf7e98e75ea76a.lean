import Mathlib

theorem inequalities_180912 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 3 / (a ^ 2 + a * b + b ^ 2) + b ^ 3 / (b ^ 2 + b * c + c ^ 2) +
     c ^ 3 / (c ^ 2 + c * a + a ^ 2)) ≥ (a + b + c) / 3 := by
  
  have h1 : a ^ 3 / (a ^ 2 + a * b + b ^ 2) ≥ (2 * a - b) / 3 := by
    have h2 : a ^ 2 + a * b + b ^ 2 > 0 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, mul_pos ha hb]
    apply (le_div_iff₀ h2).mpr
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - b), mul_pos ha hb, sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hc]

  have h2 : b ^ 3 / (b ^ 2 + b * c + c ^ 2) ≥ (2 * b - c) / 3 := by
    have h3 : b ^ 2 + b * c + c ^ 2 > 0 := by
      nlinarith [sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos hb hc]
    apply (le_div_iff₀ h3).mpr
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (b - c), mul_pos hb hc, sq_nonneg (b - c), sq_nonneg (b + c), mul_pos ha hc]

  have h3 : c ^ 3 / (c ^ 2 + c * a + a ^ 2) ≥ (2 * c - a) / 3 := by
    have h4 : c ^ 2 + c * a + a ^ 2 > 0 := by
      nlinarith [sq_pos_of_pos hc, sq_pos_of_pos ha, mul_pos hc ha]
    apply (le_div_iff₀ h4).mpr
    nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (c - a), mul_pos hc ha, sq_nonneg (c - a), sq_nonneg (c + a), mul_pos ha hc]

  linarith [h1, h2, h3]