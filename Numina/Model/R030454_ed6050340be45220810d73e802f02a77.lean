import Mathlib

open Real

theorem algebra_177982 (x : ℝ) (hx : x^2 + x + 4 ≥ 0 ∧ x^2 + x + 1 ≥ 0 ∧ 2 * x^2 + 2 * x + 9 ≥ 0) :
     sqrt (x^2 + x + 4) + sqrt (x^2 + x + 1) =
    sqrt (2 * x^2 + 2 * x + 9) ↔ x = 0 ∨ x = -1 := by

  constructor
  · -- Assume the equation holds, prove x = 0 ∨ x = -1
    intro h_eq

    rcases hx with ⟨hx1, hx2, hx3⟩

    have h1 : (sqrt (x^2 + x + 4) + sqrt (x^2 + x + 1))^2 = (sqrt (2 * x^2 + 2 * x + 9))^2 := by
      rw [h_eq]

    have h2 : (sqrt (x^2 + x + 4) + sqrt (x^2 + x + 1))^2 = (sqrt (x^2 + x + 4))^2 + (sqrt (x^2 + x + 1))^2 + 2 * (sqrt (x^2 + x + 4) * sqrt (x^2 + x + 1)) := by ring
    have h3 : (sqrt (2 * x^2 + 2 * x + 9))^2 = 2 * x^2 + 2 * x + 9 := Real.sq_sqrt (by linarith)
    rw [h2, h3] at h1
    have h4 : (sqrt (x^2 + x + 4))^2 = x^2 + x + 4 := by apply Real.sq_sqrt; linarith
    have h5 : (sqrt (x^2 + x + 1))^2 = x^2 + x + 1 := by apply Real.sq_sqrt; linarith
    rw [h4, h5] at h1
    have h6 : 2 * (sqrt (x^2 + x + 4) * sqrt (x^2 + x + 1)) = 4 := by
      nlinarith
    have h7 : sqrt (x^2 + x + 4) * sqrt (x^2 + x + 1) = 2 := by
      nlinarith
    have h8 : (sqrt (x^2 + x + 4) * sqrt (x^2 + x + 1)) ^ 2 = (2 : ℝ) ^ 2 := by
      rw [h7]
    have h9 : (sqrt (x^2 + x + 4) * sqrt (x^2 + x + 1)) ^ 2 = (sqrt (x^2 + x + 4)) ^ 2 * (sqrt (x^2 + x + 1)) ^ 2 := by
      rw [mul_pow]
    rw [h9] at h8
    have h10 : (sqrt (x^2 + x + 4)) ^ 2 = x^2 + x + 4 := Real.sq_sqrt (by linarith)
    have h11 : (sqrt (x^2 + x + 1)) ^ 2 = x^2 + x + 1 := Real.sq_sqrt (by linarith)
    rw [h10, h11] at h8
    have h12 : (x^2 + x + 4) * (x^2 + x + 1) = 4 := by
      nlinarith
    have h13 : x^2 + x = 0 := by
      nlinarith [sq_nonneg (x^2 + x), sq_nonneg (x + 1)]
    have : x * (x + 1) = 0 := by
      linarith [h13]
    cases' (mul_eq_zero.1 this) with h14 h15
    · left
      linarith
    · right
      linarith
  · -- Assume x = 0 ∨ x = -1, prove the equation
    rintro (h | h)
    · -- Case x = 0
      rw [show x = 0 by linarith]
      have h1 : sqrt (0^2 + (0 : ℝ) + 4) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : sqrt (0^2 + (0 : ℝ) + 1) = 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h3 : sqrt (2 * (0 : ℝ)^2 + 2 * (0 : ℝ) + 9) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1, h2, h3]
      all_goals norm_num
    · -- Case x = -1
      rw [show x = -1 by linarith]
      have h1 : sqrt ((-1 : ℝ)^2 + (-1 : ℝ) + 4) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : sqrt ((-1 : ℝ)^2 + (-1 : ℝ) + 1) = 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h3 : sqrt (2 * (-1 : ℝ)^2 + 2 * (-1 : ℝ) + 9) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1, h2, h3]
      all_goals norm_num