import Mathlib

theorem algebra_235967 (x : ℝ) : 2*x^4+4*x^3+3*x^2+x-1=0 ↔ x=-1/2+Real.sqrt 3/2 ∨ x=-1/2-Real.sqrt 3/2 := by
  constructor
  · -- Assume 2*x^4+4*x^3+3*x^2+x-1=0, prove x=-1/2+Real.sqrt 3/2 ∨ x=-1/2-Real.sqrt 3/2
    intro h
    have h1 : 2 * (x ^ 2 + x) ^ 2 + (x ^ 2 + x) - 1 = 0 := by
      nlinarith [h]
    have h2 : (x ^ 2 + x - 1 / 2) * (x ^ 2 + x + 1) = 0 := by
      nlinarith [h1]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case x^2 + x - 1/2 = 0
      have h5 : (x - (-1 / 2 + Real.sqrt 3 / 2)) * (x - (-1 / 2 - Real.sqrt 3 / 2)) = 0 := by
        nlinarith [h3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h5) with h6 h7
      · -- First root
        left
        nlinarith
      · -- Second root
        right
        nlinarith
    · -- Case x^2 + x + 1 = 0
      nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (x ^ 2 + x + 1), sq_nonneg (x), sq_nonneg (x ^ 2)]
  · -- Assume x=-1/2+Real.sqrt 3/2 ∨ x=-1/2-Real.sqrt 3/2, prove 2*x^4+4*x^3+3*x^2+x-1=0
    rintro (h | h)
    · -- First root
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 ^ 2 - 3), sq_nonneg (Real.sqrt 3 - 0)]
    · -- Second root
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 ^ 2 - 3), sq_nonneg (Real.sqrt 3 - 0)]