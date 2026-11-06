import Mathlib

theorem algebra_165831 (x : ℝ) (hx : x ≥ 4) :
    (Real.sqrt (x + 4) + Real.sqrt (x - 4)) / 2 = x + Real.sqrt (x^2 - 16) - 6 ↔ x = 5 := by
  constructor
  · -- Assume the equation holds, prove x = 5
    intro h_eq
    have h1 : Real.sqrt (x ^ 2 - 16) = Real.sqrt (x - 4) * Real.sqrt (x + 4) := by
      have h2 : x ^ 2 - 16 = (x - 4) * (x + 4) := by
        ring_nf
      rw [h2]
      rw [Real.sqrt_mul (by
        nlinarith
      )]
    rw [h1] at h_eq
    have h2 : Real.sqrt (x + 4) ^ 2 = x + 4 := by
      apply Real.sq_sqrt
      nlinarith
    have h3 : Real.sqrt (x - 4) ^ 2 = x - 4 := by
      apply Real.sq_sqrt
      nlinarith
    have h4 : Real.sqrt (x + 4) + Real.sqrt (x - 4) = 4 := by
      nlinarith [sq_nonneg (Real.sqrt (x + 4) - 3), sq_nonneg (Real.sqrt (x - 4) - 1),
          Real.sqrt_nonneg (x + 4), Real.sqrt_nonneg (x - 4), 
          mul_nonneg (Real.sqrt_nonneg (x + 4)) (Real.sqrt_nonneg (x - 4))
        ]
    have h4' : Real.sqrt (x + 4) = 3 := by
      nlinarith [Real.sqrt_nonneg (x + 4), Real.sqrt_nonneg (x - 4), 
          h4, sq_nonneg (Real.sqrt (x - 4) - 1)
        ]
    have h5 : x + 4 = 9 := by
      calc
        x + 4 = (Real.sqrt (x + 4)) ^ 2 := by 
          rw [Real.sq_sqrt]
          nlinarith
        _ = (3) ^ 2 := by 
          rw [h4']
        _ = (9 : ℝ) := by 
          norm_num
    nlinarith
  · -- Assume x = 5, prove the equation
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt (5 + 4) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt (5 - 4) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : Real.sqrt (5 ^ 2 - 16) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2, h3]
    all_goals norm_num