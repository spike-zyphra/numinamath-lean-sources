import Mathlib

theorem algebra_170055 (x : ℝ) (hx : 25 + x ^ 2 ≥ 0) :
    10 * x = Real.sqrt (25 + x ^ 2) * (5 + x - Real.sqrt (25 + x ^ 2)) ↔ x = -5 ∨ x = 0 := by
  constructor
  · -- Assume $10 * x = \sqrt{25 + x^2} \cdot (5 + x - \sqrt{25 + x^2})$ implies $x = -5 \vee x = 0$.
    intro h_eq
    have h1 : Real.sqrt (25 + x ^ 2) ≥ 0 := by positivity
    have h2 : (Real.sqrt (25 + x ^ 2)) ^ 2 = 25 + x ^ 2 := Real.sq_sqrt (by nlinarith)
    have h3 : x * (x + 5) = 0 := by
      nlinarith [sq_nonneg (x + 5), sq_nonneg (x), sq_nonneg (Real.sqrt (25 + x ^ 2) - 5), sq_nonneg (Real.sqrt (25 + x ^ 2) - (5 + x)), Real.sqrt_nonneg (25 + x ^ 2), Real.sq_sqrt (show 0 ≤ (25 + x ^ 2 : ℝ) by nlinarith)]
    cases' (mul_eq_zero.mp h3) with hx1 hx2
    · -- Case x * 1 = 0, so x = 0
      right
      linarith
    · -- Case x + 5 = 0, so x = -5
      left
      linarith
  · -- Assume x = -5 or x = 0 implies the equation.
    rintro (h_eq | h_eq)
    · -- Case x = -5.
      rw [show x = -5 by linarith [h_eq]]
      have h1 : Real.sqrt (25 + (-5: ℝ) ^ 2) = Real.sqrt 50 := by norm_num
      rw [h1]
      have h2 : Real.sqrt (50 : ℝ) ≥ 0 := by positivity
      nlinarith [Real.sqrt_nonneg (50 : ℝ), Real.sq_sqrt (show 0 ≤ (50 : ℝ) by norm_num)]
    · -- Case x = 0.
      rw [show x = (0: ℝ) by linarith [h_eq]]
      have h1 : Real.sqrt (25 + (0: ℝ) ^ 2) = 5 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> linarith
      rw [h1]
      all_goals norm_num