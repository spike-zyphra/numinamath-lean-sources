import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_169735 {x : ℝ} (hx : x ≥ 2) :
    3 * sqrt (x - 2) + 2 * sqrt (2 * x + 3) + sqrt (x + 1) = 11 ↔ x = 3 := by
  constructor
  · -- Assume the equation holds, prove x = 3
    intro h_eq
    have h10 : 3 * sqrt (x - 2) + 2 * sqrt (2 * x + 3) + sqrt (x + 1) = 11 := h_eq
    have h11 : sqrt (x - 2) ≥ 0 := Real.sqrt_nonneg (x - 2)
    have h12 : sqrt (2 * x + 3) ≥ 0 := Real.sqrt_nonneg (2 * x + 3)
    have h13 : sqrt (x + 1) ≥ 0 := Real.sqrt_nonneg (x + 1)
    have h14 : sqrt (x - 2) = 1 := by
      nlinarith [sq_nonneg (sqrt (x - 2) - 1), sq_nonneg (sqrt (2 * x + 3) - 3), sq_nonneg (sqrt (x + 1) - 2),
            Real.sq_sqrt (show 0 ≤ x - 2 by linarith), Real.sq_sqrt (show 0 ≤ 2 * x + 3 by nlinarith),
            Real.sq_sqrt (show 0 ≤ x + 1 by nlinarith), mul_nonneg (Real.sqrt_nonneg (x - 2)) (Real.sqrt_nonneg (2 * x + 3)), 
            mul_nonneg (Real.sqrt_nonneg (x - 2)) (Real.sqrt_nonneg (x + 1)), 
            mul_nonneg (Real.sqrt_nonneg (2 * x + 3)) (Real.sqrt_nonneg (x + 1))
          ]
    have h15 : sqrt (2 * x + 3) = 3 := by
      nlinarith [sq_nonneg (sqrt (x - 2) - 1), sq_nonneg (sqrt (2 * x + 3) - 3), sq_nonneg (sqrt (x + 1) - 2),
            Real.sq_sqrt (show 0 ≤ x - 2 by linarith), Real.sq_sqrt (show 0 ≤ 2 * x + 3 by nlinarith),
            Real.sq_sqrt (show 0 ≤ x + 1 by nlinarith), mul_nonneg (Real.sqrt_nonneg (x - 2)) (Real.sqrt_nonneg (2 * x + 3)), 
            mul_nonneg (Real.sqrt_nonneg (x - 2)) (Real.sqrt_nonneg (x + 1)), 
            mul_nonneg (Real.sqrt_nonneg (2 * x + 3)) (Real.sqrt_nonneg (x + 1))
          ]
    have h16 : sqrt (x + 1) = 2 := by
      nlinarith [sq_nonneg (sqrt (x - 2) - 1), sq_nonneg (sqrt (2 * x + 3) - 3), sq_nonneg (sqrt (x + 1) - 2),
            Real.sq_sqrt (show 0 ≤ x - 2 by linarith), Real.sq_sqrt (show 0 ≤ 2 * x + 3 by nlinarith),
            Real.sq_sqrt (show 0 ≤ x + 1 by nlinarith), mul_nonneg (Real.sqrt_nonneg (x - 2)) (Real.sqrt_nonneg (2 * x + 3)), 
            mul_nonneg (Real.sqrt_nonneg (x - 2)) (Real.sqrt_nonneg (x + 1)), 
            mul_nonneg (Real.sqrt_nonneg (2 * x + 3)) (Real.sqrt_nonneg (x + 1))
          ]
    have h17 : x - 2 = 1 := by
      calc
        x - 2 = (sqrt (x - 2)) ^ 2 := by rw [Real.sq_sqrt (show 0 ≤ x - 2 by linarith)]
        _ = (1) ^ 2 := by rw [h14]
        _ = 1 := by norm_num
    have h18 : x = 3 := by
      linarith
    exact_mod_cast h18
  · -- Assume x = 3 prove the equation
    intro h_eq
    rw [show x = 3 by linarith [h_eq]]
    have h1 : sqrt (3 - 2 : ℝ) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : sqrt (2 * (3 : ℝ) + 3) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : sqrt (3 + 1 : ℝ) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2, h3]
    all_goals norm_num