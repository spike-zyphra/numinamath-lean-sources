import Mathlib

theorem algebra_328029 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + c = 2 * b) :
    2 / (Real.sqrt c + Real.sqrt a) = 1 / (Real.sqrt a + Real.sqrt b) +
    1 / (Real.sqrt b + Real.sqrt c) := by

  have h1 : 0 < Real.sqrt a := Real.sqrt_pos.mpr (show 0 < a by linarith)
  have h2 : 0 < Real.sqrt b := Real.sqrt_pos.mpr (show 0 < b by linarith)
  have h3 : 0 < Real.sqrt c := Real.sqrt_pos.mpr (show 0 < c by linarith)
  have h4 : Real.sqrt c ^ 2 = c := by 
    rw [Real.sq_sqrt]
    linarith
  have h5 : Real.sqrt a ^ 2 = a := by 
    rw [Real.sq_sqrt]
    linarith
  have h6 : Real.sqrt b ^ 2 = b := by 
    rw [Real.sq_sqrt]
    linarith

  have h64 : Real.sqrt c + Real.sqrt a > 0 := by 
    positivity 
  have h65 : Real.sqrt a + Real.sqrt b > 0 := by 
    positivity 
  have h66 : Real.sqrt b + Real.sqrt c > 0 := by 
    positivity 

  field_simp [(show Real.sqrt a + Real.sqrt b ≠ 0 by positivity), 
      (show Real.sqrt b + Real.sqrt c ≠ 0 by positivity), 
      (show Real.sqrt c + Real.sqrt a ≠ 0 by positivity)]
  <;> nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c, sq_nonneg (Real.sqrt a - Real.sqrt c), sq_nonneg (a - c), sq_nonneg (a - c), 
      mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3, 
      h, Real.sq_sqrt (show 0 ≤ a by linarith), 
      Real.sq_sqrt (show 0 ≤ b by linarith), 
      Real.sq_sqrt (show 0 ≤ c by linarith), 
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), 
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c), 
      mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c)
  ]