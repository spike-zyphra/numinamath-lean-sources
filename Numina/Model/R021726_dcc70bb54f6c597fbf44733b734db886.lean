import Mathlib

theorem algebra_598340 (p q1 q2 : ℝ) (h : p = q1 + q2 + 1) :
    ∃ x y, x ≠ y ∧ x^2 + x + q1 = 0 ∧ y^2 + y + q1 = 0 ∨
    ∃ x y, x ≠ y ∧ x^2 + p * x + q2 = 0 ∧ y^2 + p * y + q2 = 0 := by
  by_cases h1 : 1 - 4 * q1 > 0
  · use (-1 + Real.sqrt (1 - 4 * q1)) / 2, (-1 - Real.sqrt (1 - 4 * q1)) / 2
    left
    constructor
    · -- Show the two roots are distinct
      by_contra h'
      have h3 : Real.sqrt (1 - 4 * q1) = 0 := by
        nlinarith 
      have h4 : 1 - 4 * q1 = 0 := by
        rw [Real.sqrt_eq_zero (by nlinarith)] at h3 
        linarith 
      linarith
    constructor
    · -- Show the first root is a solution
      nlinarith [Real.sqrt_nonneg (1 - 4 * q1), Real.sq_sqrt (show 0 ≤ (1 - 4 * q1 : ℝ) by nlinarith)]
    · -- Show the second root is a solution
      nlinarith [Real.sqrt_nonneg (1 - 4 * q1), Real.sq_sqrt (show 0 ≤ (1 - 4 * q1 : ℝ) by nlinarith)]
  · -- Then the second quadratic has discriminant > 0
    push_neg at h1
    have h2 : p ^ 2 - 4 * q2 > 0 := by
      nlinarith [sq_nonneg (p - 2), sq_nonneg (p - (5 + 4 * q2) / 4), sq_nonneg (q2 - 1)]
    use (-p + Real.sqrt (p ^ 2 - 4 * q2)) / 2, (-p - Real.sqrt (p ^ 2 - 4 * q2)) / 2
    right
    use (-p + Real.sqrt (p ^ 2 - 4 * q2)) / 2, (-p - Real.sqrt (p ^ 2 - 4 * q2)) / 2
    constructor
    · -- Show the two roots are distinct
      by_contra h'
      have h3 : Real.sqrt (p ^ 2 - 4 * q2) = 0 := by
        nlinarith 
      have h4 : p ^ 2 - 4 * q2 = 0 := by
        rw [Real.sqrt_eq_zero (by nlinarith)] at h3 
        linarith 
      linarith
    constructor
    · -- Show the first root is a solution
      nlinarith [Real.sqrt_nonneg (p ^ 2 - 4 * q2), Real.sq_sqrt (show 0 ≤ (p ^ 2 - 4 * q2 : ℝ) by nlinarith)]
    · -- Show the second root is a solution
      nlinarith [Real.sqrt_nonneg (p ^ 2 - 4 * q2), Real.sq_sqrt (show 0 ≤ (p ^ 2 - 4 * q2 : ℝ) by nlinarith)]