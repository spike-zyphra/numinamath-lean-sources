import Mathlib

theorem algebra_49570 {a b x y : ℝ} (ha : a = Real.sqrt (1 + x ^ 2)) (hb : b = Real.sqrt (1 + y ^ 2))
    (hxy : x + y = 1) :
    (a + b + 1) * (a + b - 1) * (a - b + 1) * (-a + b + 1) = 4 := by
  have h1 : a ^ 2 = 1 + x ^ 2 := by
    rw [ha]
    rw [Real.sq_sqrt]
    nlinarith [show 0 ≤ (1 + x ^ 2 : ℝ) by nlinarith]
  have h2 : b ^ 2 = 1 + y ^ 2 := by
    rw [hb]
    rw [Real.sq_sqrt]
    nlinarith [show 0 ≤ (1 + y ^ 2 : ℝ) by nlinarith]
  have h3 : y = 1 - x := by linarith
  have h6 : a ^ 2 = 1 + x ^ 2 := by
    linarith [h1]
  have h7 : b ^ 2 = 1 + y ^ 2 := by
    linarith [h2]
  rw [show y = 1 - x by linarith [hxy]] at h7
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a * b - 1), sq_nonneg (x * y), sq_nonneg (x - y), sq_nonneg (x + y - 1), Real.sqrt_nonneg (1 + x ^ 2), Real.sqrt_nonneg (1 + y ^ 2), Real.mul_self_sqrt (show 0 ≤ (1 + x ^ 2 : ℝ) by nlinarith), Real.mul_self_sqrt (show 0 ≤ (1 + (1 - x) ^ 2 : ℝ) by nlinarith), sq_nonneg (a - b), sq_nonneg (a + b), Real.sqrt_nonneg (1 + x ^ 2), Real.sqrt_nonneg (1 + (1 - x) ^ 2)]