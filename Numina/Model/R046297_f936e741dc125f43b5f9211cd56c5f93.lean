import Mathlib

theorem algebra_142370 (x : ℝ) :
    2*x^4-3*x^3-5*x^2+7*x-2=0 ↔
    x=2 ∨ x=1/2 ∨ x=(-1 - Real.sqrt 5)/2 ∨ x=(-1 + Real.sqrt 5)/2 := by
  constructor
  · -- Assume 2*x^4-3*x^3-5*x^2+7*x-2=0, prove the disjunction of roots
    intro h
    have h1 : (2 * x^2 - 5 * x + 2) * (x^2 + x - 1) = 0 := by
      nlinarith [sq_nonneg (x^2 - 2), sq_nonneg (x - 1 / 2), sq_nonneg (x + 1), sq_nonneg (x - 2),
        sq_nonneg (x^2 + x - 1)]
    cases' (mul_eq_zero.mp h1) with h2 h3
    · -- Case where 2x^2 -5x +2 = 0
      have h4 : (2 * x - 1) * (x - 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h4) with h5 h6
      · -- Case where 2x - 1 = 0, so x = 1/2
        right
        left
        linarith
      · -- Case where x - 2 = 0, so x = 2
        left
        linarith
    · -- Case where x^2 +x -1 = 0
      have h7 : x^2 + x - 1 = 0 := by
        linarith
      have h8 : x^2 + x - 1 = (x - (-1 - Real.sqrt 5)/2) * (x - (-1 + Real.sqrt 5)/2) := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      rw [h8] at h7
      cases' (mul_eq_zero.mp h7) with h9 h10
      · -- Case where x - (-1 - Real.sqrt 5)/2 = 0
        right
        right
        left
        linarith
      · -- Case where x - (-1 + Real.sqrt 5)/2 = 0
        right
        right
        right
        linarith
  · -- Show that each root satisfies the polynomial equation
    rintro (h | h | h | h)
    · -- Case x = 2
      rw [h]
      norm_num
    · -- Case x = 1/2
      rw [h]
      norm_num
    · -- Case x = (-1 - Real.sqrt 5)/2
      rw [h]
      nlinarith [sq_nonneg (Real.sqrt 5), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg ((-1 - Real.sqrt 5) / 2), sq_nonneg ((-1 + Real.sqrt 5) / 2),
        Real.sqrt_nonneg 5]
    · -- Case x = (-1 + Real.sqrt 5)/2
      rw [h]
      nlinarith [sq_nonneg (Real.sqrt 5), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg ((-1 - Real.sqrt 5) / 2), sq_nonneg ((-1 + Real.sqrt 5) / 2),
        Real.sqrt_nonneg 5]