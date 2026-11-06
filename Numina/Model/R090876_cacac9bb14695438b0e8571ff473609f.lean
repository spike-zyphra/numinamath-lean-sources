import Mathlib

theorem algebra_165799 (x : ℝ) : Real.sqrt (x^2 + x + 4) + Real.sqrt (x^2 + x + 1) = Real.sqrt (2 * x^2 + 2 * x + 9) ↔ x = 0 ∨ x = -1 := by
  constructor
  · -- Assume the equation holds, prove x = 0 or x = -1
    intro h
    have h1 : Real.sqrt (x^2 + x + 4) + Real.sqrt (x^2 + x + 1) = Real.sqrt (2 * x^2 + 2 * x + 9) := by
      linarith
    have h2 : Real.sqrt (x^2 + x + 4) ≥ 0 := by positivity
    have h3 : Real.sqrt (x^2 + x + 1) ≥ 0 := by positivity
    have h4 : Real.sqrt (2 * x^2 + 2 * x + 9) ≥ 0 := by positivity
    have eq1 : (Real.sqrt (x^2 + x + 4) + Real.sqrt (x^2 + x + 1))^2 = (Real.sqrt (2 * x^2 + 2 * x + 9))^2 := by
      rw [h1]
    have eq2 : (Real.sqrt (x^2 + x + 4) + Real.sqrt (x^2 + x + 1))^2 = (Real.sqrt (x^2 + x + 4)) ^ 2 + (Real.sqrt (x^2 + x + 1)) ^ 2 + 2 * (Real.sqrt (x^2 + x + 4) * Real.sqrt (x^2 + x + 1)) := by ring
    have eq3 : (Real.sqrt (2 * x^2 + 2 * x + 9)) ^ 2 = 2 * x^2 + 2 * x + 9 := by
      exact Real.sq_sqrt (by nlinarith)
    have eq4 : (Real.sqrt (x^2 + x + 4)) ^ 2 = x^2 + x + 4 := by
      exact Real.sq_sqrt (by nlinarith)
    have eq5 : (Real.sqrt (x^2 + x + 1)) ^ 2 = x^2 + x + 1 := by
      exact Real.sq_sqrt (by nlinarith)
    rw [eq2] at eq1
    rw [eq3] at eq1
    rw [eq4, eq5] at eq1
    have eq6 : Real.sqrt (x^2 + x + 4) * Real.sqrt (x^2 + x + 1) = 2 := by
      nlinarith
    have eq7 : (Real.sqrt (x^2 + x + 4) * Real.sqrt (x^2 + x + 1)) ^ 2 = 4 := by
      rw [eq6]
      all_goals norm_num
    have eq8 : (Real.sqrt (x^2 + x + 4) * Real.sqrt (x^2 + x + 1)) ^ 2 = (Real.sqrt (x^2 + x + 4)) ^ 2 * (Real.sqrt (x^2 + x + 1)) ^ 2 := by
      ring_nf
    rw [eq8] at eq7
    rw [eq4, eq5] at eq7
    have eq9 : x^4 + 2 * x^3 + 6 * x^2 + 5 * x = 0 := by
      nlinarith [eq7]
    have eq10 : x * (x + 1) * (x^2 + x + 5) = 0 := by
      nlinarith [eq9]
    cases' (mul_eq_zero.mp eq10) with h11 h12
    cases' (mul_eq_zero.mp h11) with h13 h14
    · -- Case x = 0
      left
      exact h13
    · -- Case x + 1 = 0, so x = -1
      right
      linarith
    · -- Case x^2 + x + 5 = 0, no real solutions
      have h15 : x^2 + x + 5 > 0 := by
        nlinarith [sq_nonneg (x + 0.5)]
      nlinarith
  · -- Assume x = 0 or x = -1, prove the equation
    rintro (h | h)
    · -- Case x = 0
      rw [h]
      have h1 : Real.sqrt (0^2 + (0 : ℝ) + 4) = 2 := by
        norm_num [Real.sqrt_eq_iff_sq_eq]
      have h2 : Real.sqrt (0^2 + (0 : ℝ) + 1) = 1 := by
        norm_num [Real.sqrt_eq_iff_sq_eq]
      have h3 : Real.sqrt (2 * (0 : ℝ)^2 + 2 * (0 : ℝ) + 9) = 3 := by
        norm_num [Real.sqrt_eq_iff_sq_eq]
      rw [h1, h2, h3]
      all_goals norm_num
    · -- Case x = -1
      rw [h]
      have h1 : Real.sqrt ((-1 : ℝ)^2 + (-1 : ℝ) + 4) = 2 := by
        norm_num [Real.sqrt_eq_iff_sq_eq]
      have h2 : Real.sqrt ((-1 : ℝ)^2 + (-1 : ℝ) + 1) = 1 := by
        norm_num [Real.sqrt_eq_iff_sq_eq]
      have h3 : Real.sqrt (2 * (-1 : ℝ)^2 + 2 * (-1 : ℝ) + 9) = 3 := by
        norm_num [Real.sqrt_eq_iff_sq_eq]
      rw [h1, h2, h3]
      all_goals norm_num