import Mathlib

theorem algebra_213210 (p q1 q2 : ℝ) (h : p = q1 + q2 + 1) :
    (∃ x y : ℝ, x ≠ y ∧ x^2 + x + q1 = 0 ∧ y^2 + y + q1 = 0) ∨
    (∃ x y : ℝ, x ≠ y ∧ x^2 + p * x + q2 = 0 ∧ y^2 + p * y + q2 = 0) := by
  by_cases h1 : 1 - 4 * q1 > 0
  · -- If $1 - 4q_1 > 0$, then the equation $x^2 + x + q_1 = 0$ has two distinct real roots.
    left
    have h2 : ∃ x y : ℝ, x ≠ y ∧ x^2 + x + q1 = 0 ∧ y^2 + y + q1 = 0 := by
      use (-1 + Real.sqrt (1 - 4 * q1)) / 2, (-1 - Real.sqrt (1 - 4 * q1)) / 2
      constructor
      · -- Show the two roots are distinct.
        by_contra h3
        have h4 : Real.sqrt (1 - 4 * q1) = 0 := by
          nlinarith [Real.sqrt_nonneg (1 - 4 * q1), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - 4 * q1 by linarith)]
        have h5 : Real.sqrt (1 - 4 * q1) > 0 := by
          apply Real.sqrt_pos.mpr
          linarith
        nlinarith [Real.sqrt_nonneg (1 - 4 * q1), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - 4 * q1 by linarith)]
      constructor
      · -- Show the first root is a solution.
        nlinarith [Real.sqrt_nonneg (1 - 4 * q1), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - 4 * q1 by linarith)]
      · -- Show the second root is a solution.
        nlinarith [Real.sqrt_nonneg (1 - 4 * q1), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - 4 * q1 by linarith)]
    exact h2
  · -- If $1 - 4q_1 \leq 0$, then the equation $x^2 + px + q_2 = 0$ must have two distinct real roots.
    by_cases h2 : p ^ 2 - 4 * q2 > 0
    · -- If $p^2 - 4q_2 > 0$, then the equation $x^2 + px + q_2 = 0$ has two distinct real roots.
      right
      use (-p + Real.sqrt (p ^ 2 - 4 * q2)) / 2, (-p - Real.sqrt (p ^ 2 - 4 * q2)) / 2
      constructor
      · -- Show the two roots are distinct.
        by_contra h3
        have h4 : Real.sqrt (p ^ 2 - 4 * q2) = 0 := by
          nlinarith [Real.sqrt_nonneg (p ^ 2 - 4 * q2), Real.sq_sqrt (show (0 : ℝ) ≤ p ^ 2 - 4 * q2 by nlinarith)]
        have h5 : Real.sqrt (p ^ 2 - 4 * q2) > 0 := by
          apply Real.sqrt_pos.mpr
          linarith
        nlinarith [Real.sqrt_nonneg (p ^ 2 - 4 * q2), Real.sq_sqrt (show (0 : ℝ) ≤ p ^ 2 - 4 * q2 by nlinarith)]
      constructor
      · -- Show the first root is a solution.
        nlinarith [Real.sqrt_nonneg (p ^ 2 - 4 * q2), Real.sq_sqrt (show (0 : ℝ) ≤ p ^ 2 - 4 * q2 by nlinarith)]
      · -- Show the second root is a solution.
        nlinarith [Real.sqrt_nonneg (p ^ 2 - 4 * q2), Real.sq_sqrt (show (0 : ℝ) ≤ p ^ 2 - 4 * q2 by nlinarith)]
    · -- Assume both discriminants are non-positive.
      have h3 : 1 - 4 * q1 ≤ 0 := by linarith
      have h4 : p ^ 2 - 4 * q2 ≤ 0 := by linarith
      nlinarith [sq_nonneg (p - 2), sq_nonneg (q1 - 1 / 4), h, sq_nonneg (q2 - (p^2 / 4)), sq_nonneg (q1 - 1 / 4), sq_nonneg (q2 - (p ^ 2 / 4)), sq_nonneg (p - 2)]