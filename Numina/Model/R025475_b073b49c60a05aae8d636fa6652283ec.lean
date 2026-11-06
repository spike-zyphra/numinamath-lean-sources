import Mathlib

theorem algebra_288125 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : Real.sqrt a - Real.sqrt b = 20) :
    a - 5 * b ≤ 500 := by 
  have h1 : Real.sqrt a = Real.sqrt b + 20 := by linarith
  have h2 : a = (Real.sqrt b + 20) ^ 2 := by
    calc
      a = (Real.sqrt a) ^ 2 := by rw [Real.sq_sqrt]; linarith
      _ = (Real.sqrt b + 20) ^ 2 := by rw [h1]
  have h3 : b = (Real.sqrt b) ^ 2 := by
    rw [Real.sq_sqrt]
    linarith
  have h4 : a - 5 * b = -4 * (Real.sqrt b) ^ 2 + 40 * (Real.sqrt b) + 400 := by 
    nlinarith [h2, h3, Real.sqrt_nonneg b]
  nlinarith [sq_nonneg (Real.sqrt b - 5), Real.sqrt_nonneg b]