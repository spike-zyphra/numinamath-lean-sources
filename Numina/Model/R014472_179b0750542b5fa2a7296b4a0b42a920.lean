import Mathlib


theorem algebra_251523 (x : ℝ) (hx : x ≥ 0) :
    Real.sqrt (x ^ 2 * (x - 1)) = abs x ↔ x = 0 ∨ x = 2 := by
  constructor
  · -- Forward implication: If sqrt(x^2*(x-1)) = |x|, then x = 0 or x = 2.
    intro h_eq
    by_cases h1 : x ≥ 1
    · -- Case where x ≥ 1.
      have h2 : abs x = x := by
        rw [abs_of_nonneg]
        linarith
      have h3 : Real.sqrt (x ^ 2 * (x - 1)) = x := by
        nlinarith [h_eq, h2]
      have h4 : x ^ 2 * (x - 1) = x ^ 2 := by
        have h5 : Real.sqrt (x ^ 2 * (x - 1)) = x := by
          nlinarith [h_eq, h2]
        have h6 : Real.sqrt (x ^ 2 * (x - 1)) ^ 2 = x ^ 2 * (x - 1) := by
          rw [Real.sq_sqrt]
          nlinarith
        have h7 : Real.sqrt (x ^ 2 * (x - 1)) ^ 2 = x ^ 2 := by
          rw [h5]
          all_goals nlinarith
        nlinarith
      have h5 : x ^ 2 * (x - 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h5) with h6 h7
      · -- Case where x^2 = 0.
        have h8 : x = 0 := by
          nlinarith
        linarith
      · -- Case where x - 2 = 0.
        have h8 : x = 2 := by
          nlinarith
        right
        linarith
    · -- Case where x < 1.
      have h2 : x < 1 := by linarith
      have h3 : Real.sqrt (x ^ 2 * (x - 1)) = 0 := by
        have h4 : x ^ 2 * (x - 1) ≤ 0 := by
          nlinarith [show x ^ 2 ≥ 0 by nlinarith]
        have h5 : Real.sqrt (x ^ 2 * (x - 1)) = 0 := by
          rw [Real.sqrt_eq_zero']
          nlinarith
        linarith
      have h4 : abs x = 0 := by
        nlinarith [h_eq, h3]
      have h5 : x = 0 := by
        cases abs_cases x with
        | inl h =>
          nlinarith
        | inr h =>
          nlinarith
      left
      linarith
  · -- Backward implication: If x = 0 or x = 2, then sqrt(x^2*(x - 1)) = |x|.
    rintro (h_eq | h_eq)
    · -- Case where x = 0.
      rw [h_eq]
      norm_num [Real.sqrt_eq_zero]
    · -- Case where x = 2.
      rw [h_eq]
      have h7 : Real.sqrt ((2 : ℝ) ^ 2 * ((2 : ℝ) - 1 : ℝ)) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h8 : abs ((2 : ℝ) : ℝ) = 2 := by
        norm_num [abs_of_nonneg]
      linarith [h7, h8]