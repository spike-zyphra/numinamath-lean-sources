import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_317031 (P : ℝ × ℝ) (hP : P.1^2/8 - P.2^2/4 = 1) :
    abs (P.1 - P.2) ≥ 2 := by 
  have eq1 : P.1^2 - 2 * P.2^2 = 8 := by
    field_simp at hP
    nlinarith
  
  have h1 : (P.1 - P.2) ^ 2 ≥ 4 := by 
    nlinarith [sq_nonneg (P.1 + 4 * P.2), sq_nonneg (P.1 - 4 * P.2), 
      sq_nonneg (P.1 + 2 * P.2), sq_nonneg (P.1 - 2 * P.2),
      sq_nonneg (P.1 ^ 2 - 4 * P.2 ^ 2), 
      sq_nonneg (P.2 ^ 2 - 4)]
  
  have h2 : abs (P.1 - P.2) ≥ 2 := by 
    have h3 : (P.1 - P.2) ^ 2 ≥ 4 := h1
    have h4 : abs (P.1 - P.2) = Real.sqrt ((P.1 - P.2) ^ 2) := by 
      rw [Real.sqrt_sq_eq_abs]
    have h5 : Real.sqrt ((P.1 - P.2) ^ 2) ≥ Real.sqrt (4 : ℝ) := by 
      have h6 : (P.1 - P.2) ^ 2 ≥ (4 : ℝ) := h3
      have h7 : Real.sqrt ((P.1 - P.2) ^ 2) ≥ Real.sqrt (4 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      exact h7
    have h7 : Real.sqrt (4 : ℝ) = 2 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> nlinarith
    have h8 : Real.sqrt ((P.1 - P.2) ^ 2) ≥ 2 := by 
      linarith [h5, h7]
    linarith [h4, h8]
  exact h2