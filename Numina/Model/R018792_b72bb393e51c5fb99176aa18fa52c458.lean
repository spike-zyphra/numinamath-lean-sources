import Mathlib

theorem algebra_246333 (x : ℝ) (hx : 2*x^2+3*x+5≥0 ∧ 2*x^2-3*x+5≥0) :
    Real.sqrt (2*x^2+3*x+5) + Real.sqrt (2*x^2-3*x+5) = 3*x ↔ x=4 := by
  constructor
  · -- Assume the equation holds, prove x=4.
    intro h_eq
    have h1 : 0 ≤ Real.sqrt (2 * x ^ 2 + 3 * x + 5) := Real.sqrt_nonneg (2 * x ^ 2 + 3 * x + 5)
    have h2 : 0 ≤ Real.sqrt (2 * x ^ 2 - 3 * x + 5) := Real.sqrt_nonneg (2 * x ^ 2 - 3 * x + 5)
    have h5 : 3 * x ≥ 0 := by
      nlinarith [h_eq, Real.sqrt_nonneg (2 * x ^ 2 + 3 * x + 5), Real.sqrt_nonneg (2 * x ^ 2 - 3 * x + 5), mul_nonneg (Real.sqrt_nonneg (2 * x ^ 2 + 3 * x + 5)) (Real.sqrt_nonneg (2 * x ^ 2 - 3 * x + 5))]
    have h_eq1 : (Real.sqrt (2 * x ^ 2 + 3 * x + 5) + Real.sqrt (2 * x ^ 2 - 3 * x + 5)) ^ 2 = (3 * x) ^ 2 := by
      rw [h_eq]
    have h_eq2 : (Real.sqrt (2 * x^2 + 3 * x + 5) + Real.sqrt (2 * x^2 - 3 * x + 5)) ^2 = 
        Real.sqrt (2 * x^2 + 3 * x + 5) ^2 + Real.sqrt (2 * x^2 - 3 * x + 5) ^2 + 2 * (Real.sqrt (2 * x^2 + 3 * x + 5) * Real.sqrt (2 * x^2 - 3 * x + 5)) := by ring
    rw [h_eq2] at h_eq1
    have h_eq3 : Real.sqrt (2 * x^2 + 3 * x + 5) ^2 = 2 * x^2 + 3 * x + 5 := Real.sq_sqrt (show 2 * x^2 + 3 * x + 5 ≥ 0 by tauto)
    have h_eq4 : Real.sqrt (2 * x^2 - 3 * x + 5) ^2 = 2 * x^2 - 3 * x + 5 := Real.sq_sqrt (show 2 * x^2 - 3 * x + 5 ≥ 0 by tauto)
    rw [h_eq3, h_eq4] at h_eq1
    have h_eq5 : (Real.sqrt (2 * x^2 + 3 * x + 5) * Real.sqrt (2 * x^2 - 3 * x + 5)) ^ 2 = (2 * x ^ 2 + 3 * x + 5) * (2 * x ^ 2 - 3 * x + 5) := by
      calc 
        (Real.sqrt (2 * x^2 + 3 * x + 5) * Real.sqrt (2 * x^2 - 3 * x + 5)) ^ 2 = (Real.sqrt (2 * x^2 + 3 * x + 5) * Real.sqrt (2 * x^2 - 3 * x + 5)) ^ 2 := by ring
        _ = Real.sqrt ((2 * x^2 + 3 * x + 5) * (2 * x^2 - 3 * x + 5)) ^ 2 := by 
          rw [← Real.sqrt_mul (by 
            nlinarith [hx.1, hx.2]
          )
          ]
        _ = (2 * x^2 + 3 * x + 5) * (2 * x^2 - 3 * x + 5) := Real.sq_sqrt (by 
          nlinarith [hx.1, hx.2]
        )
    have h_eq6 : x * (x - 4) = 0 := by 
      nlinarith [sq_nonneg (x ^ 2 - 4), sq_nonneg ((2 * x^2 + 3 * x + 5) - (2 * x^2 - 3 * x + 5)), sq_nonneg ((Real.sqrt (2 * x^2 + 3 * x + 5)) ^ 2 - (Real.sqrt (2 * x^2 - 3 * x + 5)) ^ 2), h_eq1, h_eq5, mul_nonneg (Real.sqrt_nonneg (2 * x ^ 2 + 3 * x + 5)) (Real.sqrt_nonneg (2 * x ^ 2 - 3 * x + 5))]
    cases' (mul_eq_zero.mp h_eq6) with h_eq7 h_eq8
    · -- x = 0 
      have h0 : x = 0 := by linarith
      rw [h0] at h_eq
      nlinarith [Real.sqrt_nonneg (2 * (0 : ℝ) ^ 2 + 3 * (0 : ℝ) + 5), Real.sqrt_nonneg (2 * (0 : ℝ) ^ 2 - 3 * (0 : ℝ) + 5), Real.sq_sqrt (show (2 * (0 : ℝ) ^ 2 + 3 * (0 : ℝ) + 5 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (2 * (0 : ℝ) ^ 2 - 3 * (0 : ℝ) + 5 : ℝ) ≥ 0 by norm_num)]
    · -- x - 4 = 0 
      linarith
  · -- Assume x = 4, prove the equation.
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt (2 * (4 : ℝ) ^ 2 + 3 * (4 : ℝ) + 5) = 7 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt (2 * (4 : ℝ) ^ 2 - 3 * (4 : ℝ) + 5) = 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    all_goals norm_num