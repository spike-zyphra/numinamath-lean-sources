import Mathlib

theorem inequalities_114406 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a + b) / 2 ≥ Real.sqrt (a * b) := by 
  have h3 : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
    rw [Real.sqrt_mul (by nlinarith)]
  have h4 : a + b ≥ 2 * Real.sqrt (a * b) := by
    rw [h3]
    have h5 : (Real.sqrt a - Real.sqrt b) ^ 2 ≥ 0 := by
      apply sq_nonneg
    have ha1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt (show 0 ≤ a by linarith)
    have hb1 : Real.sqrt b ^ 2 = b := Real.sq_sqrt (show 0 ≤ b by linarith)
    have h51 : (Real.sqrt a - Real.sqrt b) ^ 2 = a + b - 2 * (Real.sqrt a * Real.sqrt b) := by
      nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt a), sq_nonneg (Real.sqrt b)]
    nlinarith [h5, h51, Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.mul_self_sqrt (show 0 ≤ a by linarith), Real.mul_self_sqrt (show 0 ≤ b by linarith)]
  linarith