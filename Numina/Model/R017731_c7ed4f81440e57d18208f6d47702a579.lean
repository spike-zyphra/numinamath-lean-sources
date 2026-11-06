import Mathlib

theorem algebra_285554 {x y : ℝ} (hx : x + Real.sqrt (x * y) + y = 9) (hy : x ^ 2 + x * y + y ^ 2 = 27) :
    x - Real.sqrt (x * y) + y = 3 := by
  have h1 : x * y ≥ 0 := by
    by_contra h2
    push_neg at h2
    have h3 : Real.sqrt (x * y) = 0 := by
      rw [Real.sqrt_eq_zero']
      nlinarith
      all_goals nlinarith
    have h4 : x + y = 9 := by
      rw [h3] at hx
      linarith
    have h5 : x * y = 54 := by
      have h6 : x ^ 2 + x * y + y ^ 2 = 27 := by linarith
      have h7 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by nlinarith
      rw [h4] at h7
      nlinarith
    linarith
  have h2 : x + y = 6 := by
    have h4 : Real.sqrt (x * y) ^ 2 = x * y := by
      rw [Real.sq_sqrt]
      nlinarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 6), sq_nonneg (Real.sqrt (x * y) - 3)]
  have h3 : Real.sqrt (x * y) = 3 := by
    have h4 : Real.sqrt (x * y) ^ 2 = x * y := by
      rw [Real.sq_sqrt]
      nlinarith
    nlinarith [h2]
  linarith [h2, h3]