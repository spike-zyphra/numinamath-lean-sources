import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_314486 (x : ℝ) :
  1 / 7 ≤ (x ^ 2 - 3 * x + 4) / (x ^ 2 + 3 * x + 4) ∧
  (x ^ 2 - 3 * x + 4) / (x ^ 2 + 3 * x + 4) ≤ 7 := by

  have h1 : x ^ 2 + 3 * x + 4 > 0 := by 
    nlinarith [sq_nonneg (x + 3 / 2)]
  
  constructor

  · -- First part: 1/7 ≤ (x^2 - 3x + 4) / (x^2 + 3x + 4)
    have h3 : x ^ 2 + 3 * x + 4 > 0 := h1
    apply (le_div_iff₀ h3).mpr 
    nlinarith [sq_nonneg (x - 2)]

  · -- Second part: (x^2 - 3x + 4) / (x^2 + 3x + 4) ≤ 7
    have h3 : x ^ 2 + 3 * x + 4 > 0 := h1
    apply (div_le_iff₀ h3).mpr 
    nlinarith [sq_nonneg (x + 2)]