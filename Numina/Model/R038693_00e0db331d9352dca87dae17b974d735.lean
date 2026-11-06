import Mathlib

theorem algebra_249352 (x : ℝ) :
    (x^2 - 3)^3 - (4 * x + 6)^3 + 6^3 = 18 * (4 * x + 6) * (3 - x^2) ↔
    x = 2 + Real.sqrt 7 ∨ x = 2 - Real.sqrt 7 ∨ x = -3 := by
  constructor
  · -- First, prove from `h` to the goal
    intro h
    have h1 : (x^2 - 3)^3 - (4 * x + 6)^3 + (6 : ℝ) ^ 3 - 18 * (4 * x + 6) * (3 - x^2) = 0 := by linarith
    have h2 : (x^2 - 4 * x - 3) * (x + 3) ^ 2 * (x^2 - 2 * x + 13) = 0 := by
      nlinarith [sq_nonneg (x^2 - 4 * x - 3), sq_nonneg (x^2 - 2 * x + 13), sq_nonneg (x^2 - 2 * x + 13), sq_nonneg (x * Real.sqrt 7), sq_nonneg ((x - 2)^2), sq_nonneg ((x)^2), Real.sqrt_nonneg 7, Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    ·
      cases' (mul_eq_zero.mp h3) with h5 h6
      ·
        have h7 : x^2 - 4 * x - 3 = 0 := by linarith
        have h8 : x^2 - 4 * x - 3 = (x - (2 + Real.sqrt 7)) * (x - (2 - Real.sqrt 7)) := by
          ring_nf
          rw [Real.sq_sqrt (by norm_num)]
          ring
        rw [h8] at h7
        cases' (mul_eq_zero.mp h7) with h9 h10
        ·
          left
          linarith
        ·
          right
          left
          linarith
      ·
        have h11 : x + 3 = 0 := by
          apply pow_eq_zero 
          exact h6
        right
        right
        linarith
    ·
      exfalso
      nlinarith [sq_nonneg (x - 1)]
  ·
    rintro (h | h | h)
    · 
      have h1 : x = 2 + Real.sqrt 7 := h
      have h2 : x^2 = 4 * x + 3 := by
        have h7 : (2 + Real.sqrt 7) ^ 2 = 4 * (2 + Real.sqrt 7) + 3 := by
          nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
      have h3 : (x^2 - 3) ^ 3 - (4 * x + 6) ^ 3 + (6 : ℝ) ^ 3 = 18 * (4 * x + 6) * (3 - x^2) := by
        nlinarith [sq_nonneg (x^2 - 4 * x - 3), sq_nonneg ((x + 3)^2), sq_nonneg (x^2 - 2 * x + 13), Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
      linarith
    ·
      have h1 : x = 2 - Real.sqrt 7 := h
      have h2 : x^2 = 4 * x + 3 := by
        have h7 : (2 - Real.sqrt 7) ^ 2 = 4 * (2 - Real.sqrt 7) + 3 := by
          nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
      have h3 : (x^2 - 3) ^ 3 - (4 * x + 6) ^ 3 + (6 : ℝ) ^ 3 = 18 * (4 * x + 6) * (3 - x^2) := by
        nlinarith [sq_nonneg (x^2 - 4 * x - 3), sq_nonneg ((x + 3)^2), sq_nonneg (x^2 - 2 * x + 13), Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
      linarith 
    ·
      have h2 : x = -3 := by
        linarith
      rw [show x = -3 by linarith]
      norm_num