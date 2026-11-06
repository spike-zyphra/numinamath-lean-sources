import Mathlib

open Real

theorem algebra_218400 (x : ℝ) (hx : 0 < x ∧ x < 1) :
    (√(1 + x) / (√(1 + x) - √(1 - x)) + (1 - x) / (√(1 - x^2) + x - 1)) *
    (√((1 / x^2) - 1) - 1 / x) = -1 := by
  have h1 : 0 < x := hx.1
  have h2 : x < 1 := hx.2
  have h3 : 0 < 1 - x := by linarith
  have h4 : 0 < 1 - x ^ 2 := by nlinarith
  have h5 : 0 < x ^ 2 := by nlinarith
  have h6 : √(1 + x) > 0 := by positivity
  have h7 : √(1 - x) > 0 := by positivity
  have h8 : √(1 - x ^ 2) > 0 := by positivity
  have h9 : √(1 + x) - √(1 - x) ≠ 0 := by
    by_contra h
    have h10 : √(1 + x) = √(1 - x) := by linarith
    have h11 : √(1 + x) ^ 2 = √(1 - x) ^ 2 := by rw [h10]
    rw [Real.sq_sqrt (by nlinarith), Real.sq_sqrt (by nlinarith)] at h11
    nlinarith
  have eq1 : √(1 + x) / (√(1 + x) - √(1 - x)) + (1 - x) / (√(1 - x^2) + x - 1) = (1 + √(1 - x^2)) / x := by
    have eq2 : √(1 + x) / (√(1 + x) - √(1 - x)) = (1 + x + √(1 - x ^ 2)) / (2 * x) := by
      field_simp [h9]
      have h10 : √(1 + x) ^ 2 = 1 + x := by rw [Real.sq_sqrt (show 0 ≤ (1 + x) by nlinarith)]
      have h11 : √(1 - x) ^ 2 = 1 - x := by rw [Real.sq_sqrt (show 0 ≤ (1 - x) by nlinarith)]
      have h12 : √(1 + x) * √(1 - x) = √(1 - x ^ 2) := by
        have h13 : √(1 + x) * √(1 - x) = √((1 + x) * (1 - x)) := by
          rw [← Real.sqrt_mul (by nlinarith)]
        have h14 : (1 + x) * (1 - x) = 1 - x ^ 2 := by ring
        rw [h14] at h13
        linarith
      nlinarith [Real.sqrt_nonneg (1 + x), Real.sqrt_nonneg (1 - x), Real.sqrt_nonneg (1 - x^2), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x ^ 2 by nlinarith)]
    have eq3 : (1 - x) / (√(1 - x^2) + x - 1) = (Real.sqrt (1 - x^2) - x + 1) / (2 * x) := by
      have h10 : (√(1 - x^2) + x - 1) ≠ 0 := by
        by_contra h
        have h11 : √(1 - x^2) = 1 - x := by nlinarith
        have h12 : √(1 - x^2) ^ 2 = (1 - x) ^ 2 := by
          rw [h11]
        have h13 : √(1 - x^2) ^ 2 = 1 - x^2 := by
          rw [Real.sq_sqrt (show 0 ≤ (1 - x^2 : ℝ) by nlinarith)]
        have h14 : (1 - x) ^ 2 = 1 - 2 * x + x ^ 2 := by ring
        nlinarith
      field_simp [h10]
      have h11 : Real.sqrt (1 - x^2) ^ 2 = 1 - x^2 := by
        rw [Real.sq_sqrt (show 0 ≤ (1 - x^2 : ℝ) by nlinarith)]
      nlinarith [Real.sqrt_nonneg (1 - x^2), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x ^ 2 by nlinarith)]
    rw [eq2, eq3]
    field_simp [show x ≠ 0 by nlinarith]
    nlinarith [Real.sqrt_nonneg (1 - x^2), Real.sq_sqrt (show 0 ≤ 1 - x^2 by nlinarith)]
  have eq2 : (√((1 / x^2) - 1) - 1 / x) = (Real.sqrt (1 - x ^ 2) - 1) / x := by
    have h10 : Real.sqrt ((1 / x ^ 2) - 1) = Real.sqrt (1 - x ^ 2) / x := by
      have h11 : (1 / x ^ 2) - 1 = (1 - x ^ 2) / x ^ 2 := by
        field_simp
      rw [h11]
      have h12 : Real.sqrt ((1 - x^2) / x^2) = Real.sqrt (1 - x^2) / Real.sqrt (x^2) := by
        rw [Real.sqrt_div (by
          have h17 : 1 - x^2 > 0 := by nlinarith
          have h18 : (1 - x^2) / x^2 ≥ 0 := by positivity
          nlinarith
        )]
      rw [h12]
      have h13 : Real.sqrt (x ^ 2) = x := by
        rw [Real.sqrt_sq (show 0 ≤ (x : ℝ) by linarith)]
      rw [h13]
    rw [h10]
    field_simp [show x ≠ 0 by nlinarith]
    all_goals
      nlinarith [Real.sqrt_nonneg (1 - x^2), Real.sq_sqrt (show 0 ≤ 1 - x^2 by nlinarith)]
  rw [eq1, eq2]
  have h10 : (1 + Real.sqrt (1 - x ^ 2)) / x * ((Real.sqrt (1 - x ^ 2) - 1) / x) = -1 := by
    have h11 : (1 + Real.sqrt (1 - x ^ 2)) * (Real.sqrt (1 - x ^ 2) - 1) = - (x^2) := by
      nlinarith [Real.sqrt_nonneg (1 - x^2), Real.sq_sqrt (show 0 ≤ 1 - x^2 by nlinarith)]
    field_simp
    nlinarith
  linarith