import Mathlib

open Real

theorem inequalities_601611 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (1/3) * (a + b + c)^2 ≥ a * sqrt (b * c) + b * sqrt (c * a) + c * sqrt (a * b) := by
  have h1 : 0 ≤ b * c := by nlinarith [hb, hc]
  have h2 : 0 ≤ c * a := by nlinarith [hc, ha]
  have h3 : 0 ≤ a * b := by nlinarith [ha, hb]
  have h4 : sqrt (b * c) ≥ 0 := Real.sqrt_nonneg (b * c)
  have h5 : sqrt (c * a) ≥ 0 := Real.sqrt_nonneg (c * a)
  have h6 : sqrt (a * b) ≥ 0 := Real.sqrt_nonneg (a * b)
  have h7 : sqrt (b * c) = Real.sqrt b * Real.sqrt c := by
    rw [Real.sqrt_mul (by nlinarith)]
  have h8 : sqrt (c * a) = Real.sqrt c * Real.sqrt a := by 
    rw [Real.sqrt_mul (by nlinarith)]
  have h9 : sqrt (a * b) = Real.sqrt a * Real.sqrt b := by 
    rw [Real.sqrt_mul (by nlinarith)]
  have h15 : (sqrt (b * c))^2 = b * c := Real.sq_sqrt (by nlinarith)
  have h16 : (sqrt (c * a))^2 = c * a := Real.sq_sqrt (by nlinarith)
  have h17 : (sqrt (a * b))^2 = a * b := Real.sq_sqrt (by nlinarith)
  have h18 : sqrt (b * c) * sqrt (c * a) = (Real.sqrt b * Real.sqrt c) * (Real.sqrt c * Real.sqrt a) := by 
    rw [h7, h8]
  have h19 : sqrt (c * a) * sqrt (a * b) = (Real.sqrt c * Real.sqrt a) * (Real.sqrt a * Real.sqrt b) := by 
    rw [h8, h9]
  have h26 : sqrt (b * c) * sqrt (a * b) = (Real.sqrt b * Real.sqrt c) * (Real.sqrt a * Real.sqrt b) := by 
    rw [h7, h9]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha, h1, h2, h3,
            sq_nonneg (sqrt (b * c) - sqrt (c * a)), sq_nonneg (sqrt (c * a) - sqrt (a * b)), sq_nonneg (sqrt (b * c) - sqrt (a * b)), 
            h4, h5, h6,
            mul_nonneg h4 h5, mul_nonneg h4 h6, mul_nonneg h5 h6, 
            h15, h16, h17, 
            h18, h19, h26
          ]