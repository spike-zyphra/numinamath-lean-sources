import Mathlib

theorem algebra_221020 (x : ℝ) :
    x^4 + 2 * x^3 + 3 * x^2 + 2 * x - 81600 = 0 ↔
    x = -1 / 2 + Real.sqrt (Real.sqrt 81601 - 3 / 4) ∨
    x = -1 / 2 - Real.sqrt (Real.sqrt 81601 - 3 / 4) := by
  constructor
  · -- Assume x^4 + 2 * x^3 + 3 * x^2 + 2 * x - 81600 = 0, prove the disjunction
    intro h
    have h2 : (x^2 + x + 1)^2 = 81601 := by nlinarith
    have h3 : (x^2 + x + 1 - Real.sqrt 81601) * (x^2 + x + 1 + Real.sqrt 81601) = 0 := by
      nlinarith [Real.sqrt_nonneg 81601, Real.sq_sqrt (show (0 : ℝ) ≤ (81601 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- Case `(x^2 + x + 1 - Real.sqrt 81601) = 0`, will lead to (R)
      have h6 : x^2 + x + 1 - Real.sqrt 81601 = 0 := by
        nlinarith
      have h7 : (x + 1 / 2)^2 = Real.sqrt 81601 - 3 / 4 := by 
        nlinarith [h6]
      have h8a : Real.sqrt (Real.sqrt 81601 - 3 / 4) ^ 2 = Real.sqrt 81601 - 3 / 4 := by 
        apply Real.sq_sqrt
        nlinarith [Real.sqrt_nonneg (81601 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (81601 : ℝ) by norm_num)]
      have h8b : (x + 1 / 2) ^ 2 - Real.sqrt (Real.sqrt 81601 - 3 / 4) ^ 2 = 0 := by
        nlinarith [h7, h8a]
      have h9 : (x + 1 / 2 + Real.sqrt (Real.sqrt 81601 - 3 / 4)) * (x + 1 / 2 - Real.sqrt (Real.sqrt 81601 - 3 / 4)) = 0 := by
        nlinarith 
      cases' (mul_eq_zero.mp h9) with h9a h9b
      · -- First root
        right
        have h10 : x = -1 / 2 - Real.sqrt (Real.sqrt 81601 - 3 / 4) := by nlinarith
        exact_mod_cast h10
      · -- Second root
        left
        have h11 : x = -1 / 2 + Real.sqrt (Real.sqrt 81601 - 3 / 4) := by nlinarith
        exact_mod_cast h11
    · -- Case `(x^2 + x + 1 + Real.sqrt 81601) = 0`, will lead to Contradiction
      have h8 : Real.sqrt 81601 ≥ 3 / 4 := by 
        nlinarith [Real.sqrt_nonneg (81601 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 81601 by norm_num), sq_nonneg (Real.sqrt (81601 : ℝ) - 3 / 4)]
      nlinarith [Real.sqrt_nonneg 81601, Real.sqrt_nonneg (Real.sqrt 81601 - 3 / 4), sq_nonneg (x + 1 / 2), Real.sq_sqrt (show (0 : ℝ) ≤ 81601 by norm_num)]
  · -- Assume the disjunction, prove x^4 + 2 * x^3 + 3 * x^2 + 2 * x - 81600 = 0
    rintro (h | h)
    · -- Assuming x = -1/2 + Real.sqrt (Real.sqrt 81601 - 3/4)
      rw [h]
      nlinarith [Real.sqrt_nonneg (81601 : ℝ), Real.sqrt_nonneg (Real.sqrt 81601 - 3 / 4 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (81601 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (Real.sqrt 81601 - 3 / 4 : ℝ) by
        have h5 : Real.sqrt 81601 ≥ 3 / 4 := by
          nlinarith [Real.sqrt_nonneg (81601 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (81601 : ℝ) by norm_num), sq_nonneg (Real.sqrt (81601 : ℝ) - 3 / 4)]
        linarith
      )]
    · -- Assuming x = -1/2 - Real.sqrt (Real.sqrt 81601 - 3/4)
      rw [h]
      nlinarith [Real.sqrt_nonneg (81601 : ℝ), Real.sqrt_nonneg (Real.sqrt 81601 - 3 / 4 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (81601 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (Real.sqrt 81601 - 3 / 4 : ℝ) by
        have h5 : Real.sqrt 81601 ≥ 3 / 4 := by
          nlinarith [Real.sqrt_nonneg (81601 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (81601 : ℝ) by norm_num), sq_nonneg (Real.sqrt (81601 : ℝ) - 3 / 4)]
        linarith
      )]