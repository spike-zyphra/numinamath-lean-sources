import Mathlib

theorem inequalities_135317 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 ≤ 1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) := by

  have ha1 : 1 + 2 * a > 0 := by linarith
  have hb1 : 1 + 2 * b > 0 := by linarith
  have hc1 : 1 + 2 * c > 0 := by linarith
  
  have h1 : 1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) - 1 ≥ 0 := by
    have h3 : (1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) - 1) = 
      ( (1 + 2 * b) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * b) - (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c)) / ((1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c)) := by 
      field_simp
      ring
    rw [h3]
    apply div_nonneg
    -- Now we need to show that numerator expression is ≥ 0
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
      sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (a * c - 1)]
    -- Show that the denominator is positive
    positivity
  
  linarith [h1]