import Mathlib

theorem algebra_4612 {x : ℝ} (hx : x ≥ 0) (h : 2 * (x + 1) = 2 * Real.sqrt (x * (x + 8)) + Real.sqrt x - Real.sqrt (x + 8)) : x = 1 := by
  have h1 : Real.sqrt (x * (x + 8)) = Real.sqrt x * Real.sqrt (x + 8) := by
    rw [Real.sqrt_mul]
    all_goals nlinarith
  rw [h1] at h
  have h2 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
  have h3 : Real.sqrt (x + 8) ≥ 0 := Real.sqrt_nonneg (x + 8)
  have h4 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
  have h5 : (Real.sqrt (x + 8)) ^ 2 = x + 8 := by
    rw [Real.sq_sqrt]
    all_goals linarith
  nlinarith [sq_nonneg (Real.sqrt x - 1), sq_nonneg (Real.sqrt (x + 8) - 3),
    sq_nonneg (x - 1), Real.sqrt_nonneg x, Real.sqrt_nonneg (x + 8),
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (x + 8)),
    sq_nonneg (Real.sqrt x - Real.sqrt (x + 8))
  ]