import Mathlib

theorem algebra_187402 (x : ℝ) (hx : 2*x^2 + 3*x - 5 ≥ 0 ∧ 2*x^2 + 3*x - 8 ≥ 0) :
    Real.sqrt (2*x^2 + 3*x - 5) - Real.sqrt (2*x^2 + 3*x - 8) = 1 ↔
    x = 3/2 ∨ x = -3 := by
  constructor
  · -- Forward direction: equation implies solutions
    intro h_eq
    have h1 : Real.sqrt (2*x^2 + 3*x - 5) = 1 + Real.sqrt (2*x^2 + 3*x - 8) := by linarith
    have h2 : Real.sqrt (2*x^2 + 3*x - 5) ^ 2 = (1 + Real.sqrt (2*x^2 + 3*x - 8)) ^ 2 := by rw [h1]
    have h3 : Real.sqrt (2*x^2 + 3*x - 5) ^ 2 = 2*x^2 + 3*x - 5 := by
      rw [Real.sq_sqrt]
      linarith [hx.1]
    have h4 : (1 + Real.sqrt (2*x^2 + 3*x - 8)) ^ 2 = 1 + 2 * Real.sqrt (2*x^2 + 3*x - 8) + Real.sqrt (2*x^2 + 3*x - 8) ^ 2 := by ring
    have h5 : Real.sqrt (2*x^2 + 3*x - 8) ^ 2 = 2*x^2 + 3*x - 8 := by
      rw [Real.sq_sqrt]
      linarith [hx.2]
    rw [h3, h4, h5] at h2
    have h6 : Real.sqrt (2 * x ^ 2 + 3 * x - 8) = 1 := by
      nlinarith
    have h7 : 2 * x ^ 2 + 3 * x - 8 = 1 := by
      calc
        2 * x ^ 2 + 3 * x - 8 = Real.sqrt (2 * x ^ 2 + 3 * x - 8) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith [hx.2]
        _ = 1 ^ 2 := by rw [h6]
        _ = (1 : ℝ) := by norm_num
    have h8 : 2 * x ^ 2 + 3 * x - 9 = 0 := by
      linarith
    have h9 : (x - 3/2) * (x + 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h9) with h10 h11
    · left
      linarith
    · right
      linarith
  · -- Backward direction: solutions satisfy the equation
    rintro (h | h)
    · -- x = 3/2
      rw [h]
      have h1 : Real.sqrt (2 * (3 / 2 : ℝ) ^ 2 + 3 * (3 / 2 : ℝ) - 5) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : Real.sqrt (2 * (3 / 2 : ℝ) ^ 2 + 3 * (3 / 2 : ℝ) - 8) = 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1, h2]
      all_goals norm_num
    · -- x = -3
      rw [h]
      have h1 : Real.sqrt (2 * (-3 : ℝ) ^ 2 + 3 * (-3 : ℝ) - 5) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : Real.sqrt (2 * (-3 : ℝ) ^ 2 + 3 * (-3 : ℝ) - 8) = 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1, h2]
      all_goals norm_num