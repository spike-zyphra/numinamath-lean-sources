import Mathlib

open Real

theorem inequalities_177514 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b * c) + b / (a * c) + c / (a * b) ≥ 2 * (1 / a + 1 / b - 1 / c) := by 
  have h1 : 0 < a * b * c := by 
    positivity
  have h2 : a / (b * c) + b / (a * c) + c / (a * b) = (a^2 + b^2 + c^2) / (a * b * c) := by 
    field_simp 
    ring 
  have h3 : 2 * (1 / a + 1 / b - 1 / c) = 2 * ( (b * c + a * c - a * b) / (a * b * c) ) := by 
    field_simp 
    ring 
  rw [h2, h3] 
  have pos1 : 0 < a * b * c := h1 
  have h5 : a^2 + b^2 + c^2 ≥ 2 * (b * c + a * c - a * b) := by 
    nlinarith [sq_nonneg (a + b - c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h4 : (a^2 + b^2 + c^2) / (a * b * c) ≥ 2 * ( (b * c + a * c - a * b) / (a * b * c) ) := by
    have pos1 : 0 < a * b * c := h1 
    have eq1 : 2 * ( (b * c + a * c - a * b) / (a * b * c) ) = (2 * (b * c + a * c - a * b)) / (a * b * c) := by 
      ring 
    rw [eq1] 
    have h7 : (a^2 + b^2 + c^2) / (a * b * c) - (2 * (b * c + a * c - a * b)) / (a * b * c) ≥ 0 := by 
      have pos1 : 0 < a * b * c := h1 
      have h8 : (a^2 + b^2 + c^2) / (a * b * c) - (2 * (b * c + a * c - a * b)) / (a * b * c) = 
        (a^2 + b^2 + c^2 - 2 * (b * c + a * c - a * b)) / (a * b * c) := by 
        ring 
      rw [h8] 
      apply div_nonneg 
      · -- Show numerator is non-negative 
        linarith [h5] 
      · -- Show denominator is non-negative 
        positivity 
    linarith
  linarith