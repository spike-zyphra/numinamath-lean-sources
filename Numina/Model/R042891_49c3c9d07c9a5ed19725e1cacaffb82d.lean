import Mathlib

theorem inequalities_63026 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 3 / (a ^ 2 + a * b + b ^ 2)) + (b ^ 3 / (b ^ 2 + b * c + c ^ 2)) +
    (c ^ 3 / (c ^ 2 + c * a + a ^ 2)) ≥ (a + b + c) / 3 := by

  have h1 : a ^ 3 / (a ^ 2 + a * b + b ^ 2) ≥ (2 * a - b) / 3 := by 
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * (a - b)), sq_nonneg (b * (b - a)), mul_pos ha hb]

  have h2 : b ^ 3 / (b ^ 2 + b * c + c ^ 2) ≥ (2 * b - c) / 3 := by 
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - b)), mul_pos hb hc]

  have h3 : c ^ 3 / (c ^ 2 + c * a + a ^ 2) ≥ (2 * c - a) / 3 := by 
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (c * (c - a)), sq_nonneg (a * (a - c)), mul_pos hc ha]

  linarith [h1, h2, h3]