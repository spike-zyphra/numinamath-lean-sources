import Mathlib

theorem algebra_324182 (x : ℝ) (hx : x^2 + 3 * x + 7 ≥ 0 ∧ x^2 - x + 10 ≥ 0) :
    Real.sqrt (x^2 + 3 * x + 7) - Real.sqrt (x^2 - x + 10) = 1 ↔ x = 3 := by
  constructor
  · -- Prove the forward direction: if √(x² + 3x + 7) - √(x² - x + 10) = 1 then x = 3.
    intro h
    have h1 : Real.sqrt (x^2 + 3 * x + 7) = 1 + Real.sqrt (x^2 - x + 10) := by
      linarith
    have h2 : (Real.sqrt (x^2 + 3 * x + 7)) ^ 2 = (1 + Real.sqrt (x^2 - x + 10)) ^ 2 := by
      rw [h1]
    have h3 : (Real.sqrt (x^2 + 3 * x + 7)) ^ 2 = x ^ 2 + 3 * x + 7 := by
      rw [Real.sq_sqrt]
      linarith [hx.1]
    have h4 : (1 + Real.sqrt (x^2 - x + 10)) ^ 2 = 1 + 2 * Real.sqrt (x^2 - x + 10) + (Real.sqrt (x^2 - x + 10) ^ 2) := by
      ring
    rw [h3, h4] at h2
    have h5 : (Real.sqrt (x^2 - x + 10)) ^ 2 = x^2 - x + 10 := by
      rw [Real.sq_sqrt]
      linarith [hx.2]
    rw [h5] at h2
    have h6 : 4 * x - 4 = 2 * Real.sqrt (x^2 - x + 10) := by
      nlinarith
    have h7 : 2 * x - 2 = Real.sqrt (x^2 - x + 10) := by
      linarith
    have h8 : (2 * x - 2) ^ 2 = (Real.sqrt (x^2 - x + 10)) ^ 2 := by
      rw [h7]
    have h9 : (Real.sqrt (x^2 - x + 10)) ^ 2 = x^2 - x + 10 := by
      rw [Real.sq_sqrt]
      linarith [hx.2]
    rw [h9] at h8
    have h10 : 3 * x^2 - 7 * x - 6 = 0 := by
      nlinarith
    have h11 : (x - 3) * (3 * x + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h11) with h12 h13
    · -- x - 3 = 0, so x = 3
      linarith
    · -- 3 * x + 2 = 0, so x = -2/3
      have h14 : x = -2 / 3 := by linarith
      rw [h14] at h
      have h15 : Real.sqrt ((-2 / 3 : ℝ) ^ 2 + 3 * (-2 / 3 : ℝ) + 7) = 7 / 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> nlinarith
      have h16 : Real.sqrt ((-2 / 3 : ℝ) ^ 2 - (-2 / 3 : ℝ) + 10) = 10 / 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> nlinarith
      rw [h15, h16] at h
      nlinarith
  · -- Prove the reverse direction: if x = 3 then √(x² + 3x + 7) - √(x² - x + 10) = 1.
    intro h
    rw [h]
    have h5 : Real.sqrt ((3 : ℝ) ^ 2 + 3 * (3 : ℝ) + 7) = 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h6 : Real.sqrt ((3 : ℝ) ^ 2 - (3 : ℝ) + 10) = 4 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h5, h6]
    all_goals norm_num