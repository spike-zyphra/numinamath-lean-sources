import Mathlib

theorem algebra_2883 (x : ℝ) (hx : 0 ≤ 3 * x + 6) (hx' : 0 ≤ x - Real.sqrt (3 * x + 6)) : Real.sqrt (x + Real.sqrt (3 * x + 6)) + Real.sqrt (x - Real.sqrt (3 * x + 6)) = 6 ↔ x = 10 := by
  constructor
  · -- First direction: Equation to x=10
    intro h_eq
    have h1 : Real.sqrt (x + Real.sqrt (3 * x + 6)) ≥ 0 := by positivity
    have h2 : Real.sqrt (x - Real.sqrt (3 * x + 6)) ≥ 0 := by positivity
    have h3 : Real.sqrt (x + Real.sqrt (3 * x + 6)) + Real.sqrt (x - Real.sqrt (3 * x + 6)) = 6 := h_eq
    have h4 : (Real.sqrt (x + Real.sqrt (3 * x + 6)) + Real.sqrt (x - Real.sqrt (3 * x + 6))) ^ 2 = 36 := by
      rw [h3]
      norm_num
    have h5 : (Real.sqrt (x + Real.sqrt (3 * x + 6)) + Real.sqrt (x - Real.sqrt (3 * x + 6))) ^ 2 = 
      (Real.sqrt (x + Real.sqrt (3 * x + 6)))^2 + (Real.sqrt (x - Real.sqrt (3 * x + 6)))^2 + 2 * (Real.sqrt (x + Real.sqrt (3 * x + 6)) * Real.sqrt (x - Real.sqrt (3 * x + 6))) := by ring
    have h6 : (Real.sqrt (x + Real.sqrt (3 * x + 6)))^2 = x + Real.sqrt (3 * x + 6) := by
      apply Real.sq_sqrt
      nlinarith [Real.sqrt_nonneg (3 * x + 6), Real.sq_sqrt (show 0 ≤ (3 * x + 6 : ℝ) by linarith)]
    have h7 : (Real.sqrt (x - Real.sqrt (3 * x + 6)))^2 = x - Real.sqrt (3 * x + 6) := by
      apply Real.sq_sqrt
      linarith [hx']
    have h8 : Real.sqrt (x + Real.sqrt (3 * x + 6)) * Real.sqrt (x - Real.sqrt (3 * x + 6)) = Real.sqrt ((x + Real.sqrt (3 * x + 6)) * (x - Real.sqrt (3 * x + 6))) := by
      rw [← Real.sqrt_mul (by
        nlinarith [Real.sqrt_nonneg (3 * x + 6), hx']
      )]
    have h9 : (x + Real.sqrt (3 * x + 6)) * (x - Real.sqrt (3 * x + 6)) = x^2 - (3 * x + 6 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (3 * x + 6), Real.sq_sqrt (show (0 : ℝ) ≤ (3 * x + 6 : ℝ) by linarith)]
    have h10 : Real.sqrt ((x + Real.sqrt (3 * x + 6)) * (x - Real.sqrt (3 * x + 6))) = Real.sqrt (x^2 - (3 * x + 6 : ℝ)) := by
      have h11 : (x + Real.sqrt (3 * x + 6)) * (x - Real.sqrt (3 * x + 6)) = x^2 - (3 * x + 6 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (3 * x + 6), Real.sq_sqrt (show (0 : ℝ) ≤ (3 * x + 6 : ℝ) by linarith)]
      rw [h11]
    have h11 : Real.sqrt (x + Real.sqrt (3 * x + 6)) * Real.sqrt (x - Real.sqrt (3 * x + 6)) = Real.sqrt (x^2 - (3 * x + 6 : ℝ)) := by
      rw [h8, h10]
    nlinarith [Real.sqrt_nonneg (x + Real.sqrt (3 * x + 6)), Real.sqrt_nonneg (x - Real.sqrt (3 * x + 6)), Real.sqrt_nonneg (3 * x + 6), Real.sq_sqrt (show (0 : ℝ) ≤ (3 * x + 6 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (x^2 - (3 * x + 6 : ℝ) ) by nlinarith [Real.sqrt_nonneg (3 * x + 6), sq_nonneg (x - Real.sqrt (3 * x + 6)), Real.sq_sqrt (show 0 ≤ (3 * x + 6 : ℝ) by linarith), sq_nonneg (Real.sqrt (3 * x + 6) - (x)), Real.sqrt_nonneg (3 * x + 6)]), sq_nonneg (x - 10), Real.sqrt_nonneg (3 * x + 6), Real.sqrt_nonneg (x ^ 2 - (3 * x + 6))]
  · -- Second direction: x=10 to equation
    intro h_eq
    rw [h_eq]
    have h2 : Real.sqrt (3 * (10 : ℝ) + 6) = 6 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    have h3 : Real.sqrt (10 + Real.sqrt (3 * (10 : ℝ) + 6)) = 4 := by
      rw [h2]
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    have h4 : Real.sqrt (10 - Real.sqrt (3 * (10 : ℝ) + 6)) = 2 := by
      rw [h2]
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    rw [h3, h4]
    all_goals norm_num