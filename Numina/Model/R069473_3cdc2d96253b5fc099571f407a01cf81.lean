import Mathlib

theorem algebra_13627 {x : ℝ} (hx : x = Real.sqrt x + 6) : x = 9 := by
  have h1 : x ≥ 0 := by
    have h2 : Real.sqrt x ≥ 0 := by positivity
    nlinarith [sq_nonneg (Real.sqrt x - 6), sq_nonneg (Real.sqrt x), Real.sq_sqrt (show x ≥ 0 by by_contra h; push_neg at h; nlinarith [Real.sqrt_nonneg x]) ]
  have h2 : Real.sqrt x ≥ 0 := by positivity
  have h4 : Real.sqrt x = x - 6 := by linarith [hx]
  have h5 : (Real.sqrt x) ^ 2 = x := by
    rw [Real.sq_sqrt]
    linarith -- Since we proved x ≥ 0
  have h6 : (x - 6) ^ 2 = x := by
    rw [show (x - 6) = Real.sqrt x by linarith [h4]] 
    nlinarith [h5] -- sqrt x = x - 6 => (x - 6) = sqrt x
  -- Expanding
  -- x^2 - 13x + 36 =0
  have h7 : x ^ 2 - 13 * x + 36 = 0 := by
    nlinarith [h6]
  -- Factor quadratic:
  have h8 : (x - 9) * (x - 4) = 0 := by
    nlinarith [h7]
  cases' (mul_eq_zero.mp h8) with h9 h10
  · -- Case x = 9.
    linarith
  · -- Case x = 4. But sqrt 4 = 2 = 4 - 6 = -2 contradicts
    have h10' : x = 4 := by linarith
    rw [h10'] at h4
    -- sqrt 4 = 2
    have h3 : Real.sqrt (4 : ℝ) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    nlinarith [h3, h4, Real.sqrt_nonneg 4, Real.sqrt_nonneg 4]