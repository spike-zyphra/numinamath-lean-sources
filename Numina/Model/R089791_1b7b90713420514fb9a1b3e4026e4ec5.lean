import Mathlib

theorem inequalities_140365 (a b c d : ℝ) (h : a + b + c + d = 1) : a * b + b * c + c * d + d * a ≤ 1 / 4 := by 
  have h1 : a * b + b * c + c * d + d * a = (a + c) * (b + d) := by
    ring
  rw [h1]
  have h2 : (a + c) + (b + d) = 1 := by 
    linarith [h]
  have h3 : (a + c) * (b + d) ≤ 1 / 4 := by 
    have h4 : (a + c) + (b + d) = 1 := h2
    have h5 : (a + c) ^ 2 + (b + d) ^ 2 ≥ 2 * ((a + c) * (b + d)) := by 
      linarith [sq_nonneg ((a + c) - (b + d))]
    have h6 : (a + c) ^ 2 + (b + d) ^ 2 = 1 - 2 * ((a + c) * (b + d)) := by 
      have h7 : (a + c) + (b + d) = 1 := h4
      have h8 : (a + c) ^ 2 + (b + d) ^ 2 = ((a + c) + (b + d)) ^ 2 - 2 * ((a + c) * (b + d)) := by 
        ring
      rw [h8, h7]
      all_goals nlinarith
    nlinarith [h5, h6, h4]
  linarith [h3]