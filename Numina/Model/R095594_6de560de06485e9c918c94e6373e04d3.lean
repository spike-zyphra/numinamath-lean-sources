import Mathlib

open Real

theorem inequalities_195847 (a b : ℝ) :
    sqrt ((a ^ 2 + b ^ 2) / 2) ≥ (a + b) / 2 := by
  have h1 : sqrt ((a ^ 2 + b ^ 2) / 2) ≥ 0 := by positivity
  have h2 : (a + b) / 2 ≤ sqrt ((a ^ 2 + b ^ 2) / 2) := by 
    by_cases h : (a + b) / 2 ≥ 0
    · -- Case where the right side is non-negative
      have h3 : ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
        linarith [sq_nonneg (a - b)]
      have h4 : sqrt ((a ^ 2 + b ^ 2) / 2) ≥ (a + b) / 2 := by
        have h5 : ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := h3
        have h7 : sqrt (((a + b) / 2) ^ 2) ≤ sqrt ((a ^ 2 + b ^ 2) / 2) := Real.sqrt_le_sqrt h5
        have h8 : sqrt (((a + b) / 2) ^ 2) = (a + b) / 2 := by
          rw [Real.sqrt_sq]
          linarith
        linarith
      linarith
    · -- Case where the right side is negative
      have h3 : (a + b) / 2 ≤ 0 := by linarith
      have h4 : (a + b) / 2 ≤ sqrt ((a ^ 2 + b ^ 2) / 2) := by 
        have h5 : sqrt ((a ^ 2 + b ^ 2) / 2) ≥ 0 := by positivity
        linarith
      linarith
  linarith