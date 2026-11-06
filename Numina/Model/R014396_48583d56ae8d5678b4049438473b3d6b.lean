import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_159287 {f : ℝ → ℝ}
  (hf : ∀ x, f x = sqrt (x - 2 * sqrt (x - 1)) / (sqrt (x - 1) - 1)) :
  ∀ x, (x ∈ Ico 1 2 → f x = -1) ∧ (x > 2 → f x = 1) := by
  intro x 
  constructor 
  · -- First, prove that if x ∈ [1, 2) then f x = -1
    intro hx
    rcases hx with ⟨hx1, hx2⟩
    have h1 : 1 ≤ x := hx1
    have h2 : x < 2 := hx2
    have h3 : 0 ≤ x - 1 := by linarith
    have h4 : x - 1 < 1 := by nlinarith 
    have h5 : sqrt (x - 1) < 1 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ (x - 1 : ℝ) by nlinarith)]
    have h6 : sqrt (x - 1) - 1 < 0 := by 
      linarith 
    have h7 : f x = sqrt (x - 2 * sqrt (x - 1)) / (sqrt (x - 1) - 1) := hf x 
    rw [h7] 
    have h8 : x - 2 * sqrt (x - 1) = (sqrt (x - 1) - 1) ^ 2 := by 
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ (x - 1 : ℝ) by nlinarith)]
    have h9 : sqrt (x - 2 * sqrt (x - 1)) = abs (sqrt (x - 1) - 1) := by
      rw [h8]
      have : sqrt ((sqrt (x - 1) - 1) ^ 2) = abs (sqrt (x - 1) - 1) := by 
        rw [Real.sqrt_sq_eq_abs]
      exact this
    rw [h9] 
    have h10 : sqrt (x - 1) - 1 < 0 := h6 
    have h11 : abs (sqrt (x - 1) - 1) = - (sqrt (x - 1) - 1) := by 
      rw [abs_of_neg h10]
    rw [h11] 
    field_simp [(show sqrt (x - 1) - 1 ≠ 0 by 
      nlinarith [Real.sqrt_nonneg (x - 1), h5]
    )]
  · -- Now prove that if x > 2, then f x = 1
    intro hx 
    have h1 : x > 2 := hx 
    have h2 : x - 1 > 1 := by linarith 
    have h3 : sqrt (x - 1) > 1 := by 
      have : sqrt (x - 1) > sqrt (1 : ℝ) := by 
        apply Real.sqrt_lt_sqrt 
        all_goals linarith 
      have h4 : sqrt (1 : ℝ) = 1 := Real.sqrt_one 
      linarith 
    have h4 : sqrt (x - 1) - 1 > 0 := by 
      linarith [h3] 
    have h7 : f x = sqrt (x - 2 * sqrt (x - 1)) / (sqrt (x - 1) - 1) := hf x 
    rw [h7] 
    have h8 : x - 2 * sqrt (x - 1) = (sqrt (x - 1) - 1) ^ 2 := by 
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ (x - 1 : ℝ) by nlinarith)]
    have h9 : sqrt (x - 2 * sqrt (x - 1)) = abs (sqrt (x - 1) - 1) := by 
      rw [h8] 
      have : sqrt ((sqrt (x - 1) - 1) ^ 2) = abs (sqrt (x - 1) - 1) := by 
        rw [Real.sqrt_sq_eq_abs] 
      exact this 
    rw [h9] 
    have h10 : sqrt (x - 1) - 1 > 0 := h4 
    have h11 : abs (sqrt (x - 1) - 1) = sqrt (x - 1) - 1 := by 
      rw [abs_of_pos h10] 
    rw [h11] 
    field_simp [(show sqrt (x - 1) - 1 ≠ 0 by 
      nlinarith [Real.sqrt_nonneg (x - 1), h3]
    )]