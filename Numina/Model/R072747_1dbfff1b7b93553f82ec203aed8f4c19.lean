import Mathlib

theorem algebra_13652 {x : ℝ} (hx : x ≥ 0) (hx' : x = Real.sqrt x + 110) :
    x = 121 := by
  have h1 : Real.sqrt x = x - 110 := by linarith
  have h2 : x ≥ 110 := by
    have hsqrt_nonneg : Real.sqrt x ≥ 0 := by apply Real.sqrt_nonneg
    linarith [h1, hsqrt_nonneg]
  have h3 : x = (x - 110) ^ 2 := by
    calc
      x = (Real.sqrt x) ^ 2 := by rw [Real.sq_sqrt]; all_goals linarith
      _ = (x - 110) ^ 2 := by rw [h1]
  have h4 : (x - 121) * (x - 100) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h4) with h5 h6
  · -- First case, where $x - 121 = 0$, so $x = 121$
    linarith
  · -- Second case, where $x - 100 = 0$, so $x = 100$
    have h7 : x = 100 := by linarith
    rw [h7] at h1
    have h8 : Real.sqrt (100 : ℝ) = 10 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    nlinarith [h1, h8, Real.sqrt_nonneg (100 : ℝ)]