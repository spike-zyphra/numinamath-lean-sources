import Mathlib

theorem inequalities_3213 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 * (a ^ 3 / (a ^ 2 + b ^ 2) + b ^ 3 / (b ^ 2 + c ^ 2) + c ^ 3 / (c ^ 2 + a ^ 2)) ≥
    a + b + c := by
  have h1 : a ^ 3 / (a ^ 2 + b ^ 2) ≥ (a - b / 2 : ℝ) := by
    have h2 : 0 < (a ^ 2 + b ^ 2 : ℝ) := by nlinarith
    apply (le_div_iff₀ h2).mpr
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b), sq_nonneg ((a : ℝ) - (b : ℝ) / 2), sq_nonneg ((a : ℝ) * (b : ℝ)), mul_pos ha hb, sq_nonneg (a - 2 * b)]
  
  have h2 : b ^ 3 / (b ^ 2 + c ^ 2) ≥ (b - c / 2 : ℝ) := by
    have h3 : 0 < (b ^ 2 + c ^ 2 : ℝ) := by nlinarith
    apply (le_div_iff₀ h3).mpr
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (b * c), sq_nonneg ((b : ℝ) - (c : ℝ) / 2), sq_nonneg ((b : ℝ) * (c : ℝ)), mul_pos hb hc, sq_nonneg (b - 2 * c)]

  have h3 : c ^ 3 / (c ^ 2 + a ^ 2) ≥ (c - a / 2 : ℝ) := by
    have h4 : 0 < (c ^ 2 + a ^ 2 : ℝ) := by nlinarith
    apply (le_div_iff₀ h4).mpr
    nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (c * a), sq_nonneg ((c : ℝ) - (a : ℝ) / 2), sq_nonneg ((c : ℝ) * (a : ℝ)), mul_pos hc ha, sq_nonneg (c - 2 * a)]
  
  have h4 : (a ^ 3 / (a ^ 2 + b ^ 2) + b ^ 3 / (b ^ 2 + c ^ 2) + c ^ 3 / (c ^ 2 + a ^ 2)) ≥ ((a - b / 2) + (b - c / 2) + (c - a / 2) : ℝ) := by linarith [h1, h2, h3]

  linarith [h4]