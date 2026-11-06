import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_309165 :
  ∀ x : ℝ, (x^2 + 5) / sqrt (x^2 + 4) ≥ 2 := by
  intro x 
  have h1 : sqrt (x ^ 2 + 4) > 0 := by 
    apply Real.sqrt_pos.mpr
    linarith [sq_nonneg x]

  have h3 : (x ^ 2 + 5) ≥ 2 * sqrt (x ^ 2 + 4) := by 
    have h4 : (x ^ 2 + 5) ^ 2 ≥ 4 * (x ^ 2 + 4) := by 
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 + 3)]
    
    have h5 : (x ^ 2 + 5) ^ 2 ≥ (2 * sqrt (x ^ 2 + 4)) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 4), sq_nonneg (x ^ 2 + 3), 
        Real.sq_sqrt (show 0 ≤ x ^ 2 + 4 by positivity), 
        sq_nonneg (2 * sqrt (x ^ 2 + 4)), 
        sq_nonneg (x ^ 2 + 5 - 2 * sqrt (x ^ 2 + 4)), 
        Real.sqrt_nonneg (x ^ 2 + 4), 
        h4
      ]
    
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 4), Real.sq_sqrt (show 0 ≤ x ^ 2 + 4 by positivity)]

  have h4 : (x ^ 2 + 5) / sqrt (x ^ 2 + 4) ≥ (2 * sqrt (x ^ 2 + 4)) / sqrt (x ^ 2 + 4) := by 
    apply (div_le_div_right h1).mpr
    linarith [h3]

  have h5 : (2 * sqrt (x ^ 2 + 4)) / sqrt (x ^ 2 + 4) = 2 := by 
    have h6 : sqrt (x ^ 2 + 4) > 0 := h1
    field_simp [h6]
    <;> ring_nf <;> norm_num
    all_goals try { tauto }

  linarith [h4, h5]