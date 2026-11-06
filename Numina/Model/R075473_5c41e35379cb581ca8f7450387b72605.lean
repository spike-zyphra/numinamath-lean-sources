import Mathlib

theorem algebra_165565 (x : ℝ) : x^3 - 9 * (1 - x)^2 = x ↔
    x = 1 ∨ x = 4 - Real.sqrt 7 ∨ x = 4 + Real.sqrt 7 := by
  constructor
  · -- Assume x^3 - 9 * (1 - x)^2 = x, prove x = 1 ∨ x = 4 - Real.sqrt 7 ∨ x = 4 + Real.sqrt 7
    intro h
    -- First, convert the given equation to standard form.
    have h1 : x^3 - 9 * (1 - x)^2 - x = 0 := by linarith
    -- Then compute to standard polynomial form.
    have h2 : x^3 - 9 * x^2 + 17 * x - 9 = 0 := by
      nlinarith
    -- Factor cubic equation as (x - 1)(x^2 - 8x + 9) = 0
    have h3 : (x - 1) * (x^2 - 8 * x + 9) = 0 := by
      nlinarith [sq_nonneg (x - 4), sq_nonneg (x - 1)]
    -- Case analysis: either x-1=0 or x^2 - 8x + 9 = 0
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- Case where x - 1 = 0, so x = 1
      left
      linarith
    · -- Case where x^2 - 8 x + 9 = 0, solve quadratic
      have h6 : x^2 - 8 * x + 9 = 0 := by
        linarith
      -- Factor quadratic as (x - (4 - Real.sqrt 7)) * (x - (4 + Real.sqrt 7)) = 0
      have h7 : (x - (4 - Real.sqrt 7)) * (x - (4 + Real.sqrt 7)) = 0 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
      -- Case analysis: either x - (4 - Real.sqrt 7) = 0 or x - (4 + Real.sqrt 7) = 0
      cases' (mul_eq_zero.mp h7) with h8 h9
      · -- Case where x = 4 - Real.sqrt 7
        right
        left
        linarith
      · -- Case where x = 4 + Real.sqrt 7
        right
        right
        linarith
  · -- Assume x = 1 ∨ x = 4 - Real.sqrt 7 ∨ x = 4 + Real.sqrt 7, prove x^3 - 9 * (1 - x)^2 = x
    rintro (h | h | h)
    · -- Case where x = 1
      rw [h]
      norm_num
    · -- Case where x = 4 - Real.sqrt 7
      rw [h]
      have h1 : Real.sqrt 7 ^ 2 = 7 := by
        exact Real.sq_sqrt (by norm_num)
      nlinarith [h1, Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
    · -- Case where x = 4 + Real.sqrt 7
      rw [h]
      have h1 : Real.sqrt 7 ^ 2 = 7 := by
        exact Real.sq_sqrt (by norm_num)
      nlinarith [h1, Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]