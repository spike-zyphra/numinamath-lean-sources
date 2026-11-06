import Mathlib

theorem algebra_599737 (x : ℝ) (hx : 5 * x ^ 2 - 1 ≥ 0) :
    5 * x ^ 2 + x - x * Real.sqrt (5 * x ^ 2 - 1) - 2 = 0 ↔
    x = Real.sqrt 10 / 5 ∨ x = -Real.sqrt 10 / 5 := by
  constructor
  · -- Assume 5x² + x - x√(5x² - 1) - 2 = 0, prove x = √10/5 ∨ x = -√10/5
    intro h_eq
    have h1 : Real.sqrt (5 * x ^ 2 - 1) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h2 : 5 * x ^ 2 - 1 ≥ 0 := hx
    have h_eq2 : 5 * x ^ 2 + x - 2 = x * Real.sqrt (5 * x ^ 2 - 1) := by linarith
    have h_eq3 : (5 * x ^ 2 + x - 2) ^ 2 = (x * Real.sqrt (5 * x ^ 2 - 1)) ^ 2 := by
      rw [h_eq2]
    have h_eq4 : (5 * x ^ 2 + x - 2) ^ 2 = 25 * x ^ 4 + 10 * x ^ 3 - 19 * x ^ 2 - 4 * x + 4 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x + 1), sq_nonneg (x - 1 / 2)]
    have h_eq5 : (x * Real.sqrt (5 * x ^ 2 - 1)) ^ 2 = x ^ 2 * (5 * x ^ 2 - 1) := by
      have h4 : (Real.sqrt (5 * x ^ 2 - 1)) ^ 2 = 5 * x ^ 2 - 1 := by
        rw [Real.sq_sqrt]
        linarith
      calc
        (x * Real.sqrt (5 * x ^ 2 - 1)) ^ 2
          = x ^ 2 * (Real.sqrt (5 * x ^ 2 - 1) ) ^ 2 := by ring
        _ = x ^ 2 * (5 * x ^ 2 - 1) := by rw [h4]
    rw [h_eq5] at h_eq3
    rw [h_eq4] at h_eq3
    have h_eq6 : 10 * x ^ 4 + 5 * x ^ 3 - 9 * x ^ 2 - 2 * x + 2 = 0 := by
      nlinarith
    have h_eq7 : (5 * x ^ 2 - 2) * (2 * x ^ 2 + x - 1) = 0 := by
      nlinarith [h_eq6]
    cases' (mul_eq_zero.1 h_eq7) with h_eq8 h_eq9
    · -- 5x^2 - 2 = 0
      have h_eq10 : 5 * x ^ 2 - 2 = 0 := by
        nlinarith
      have h_eq11 : x ^ 2 = (2 / 5 : ℝ) := by
        linarith
      have h_eq12 : x = Real.sqrt 10 / 5 ∨ x = -Real.sqrt 10 / 5 := by
        have h_eq13 : x ^ 2 - (2 / 5 : ℝ) = 0 := by
          linarith
        have h_eq14 : (x - Real.sqrt 10 / 5) * (x + Real.sqrt 10 / 5) = 0 := by
          nlinarith [Real.sqrt_pos.mpr (show 0 < (10 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
        cases' (mul_eq_zero.1 h_eq14) with h_eq15 h_eq16
        · left
          linarith
        · right
          linarith
      tauto
    · -- 2x^2 + x - 1 = 0
      have h_eq17 : 2 * x ^ 2 + x - 1 = 0 := by
        nlinarith
      have h_eq18 : (x - 1 / 2) * (2 * x + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h_eq18) with h_eq19 h_eq20
      · -- x = 1/2
        have h_eq21 : x = 1 / 2 := by
          linarith
        rw [h_eq21] at h_eq
        nlinarith [Real.sqrt_nonneg (5 * (1 / 2: ℝ) ^ 2 - 1), Real.sq_sqrt (show 5 * (1 / 2: ℝ) ^ 2 - 1 ≥ 0 by norm_num)]
      · -- x = -1
        have h_eq22 : x = -1 := by
          linarith
        rw [h_eq22] at h_eq
        nlinarith [Real.sqrt_nonneg (5 * (-1: ℝ) ^ 2 - 1), Real.sq_sqrt (show 5 * (-1: ℝ) ^ 2 - 1 ≥ 0 by norm_num)]
  · -- Assume x = Real.sqrt 10 / 5 ∨ x = -Real.sqrt 10 / 5, prove 5 * x ^ 2 + x - x * Real.sqrt (5 * x ^ 2 - 1) - 2 = 0
    rintro (h_eq | h_eq)
    · -- x = Real.sqrt 10 / 5
      rw [h_eq]
      have h_eq1 : Real.sqrt (5 * (Real.sqrt 10 / 5) ^ 2 - 1) = (1 : ℝ) := by
        have h_eq2 : 5 * (Real.sqrt 10 / 5) ^ 2 - 1 = (1 : ℝ) := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
        rw [h_eq2]
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      nlinarith [Real.sqrt_nonneg (10 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), h_eq1]
    · -- x = -Real.sqrt 10 / 5
      rw [h_eq]
      have h_eq1 : Real.sqrt (5 * (-Real.sqrt 10 / 5) ^ 2 - 1) = (1 : ℝ) := by
        have h_eq2 : 5 * (-Real.sqrt 10 / 5) ^ 2 - 1 = (1 : ℝ) := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
        rw [h_eq2]
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      nlinarith [Real.sqrt_nonneg (10 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), h_eq1]