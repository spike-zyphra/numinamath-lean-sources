import Mathlib

open Real

theorem inequalities_196383 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a^3 + b^3 + c^3 ≥ a^2 * sqrt (b * c) + b^2 * sqrt (a * c) + c^2 * sqrt (a * b) := by
  have h1 : 0 ≤ a * b := mul_nonneg ha hb
  have h2 : 0 ≤ a * c := mul_nonneg ha hc
  have h3 : 0 ≤ b * c := mul_nonneg hb hc
  have h4 : sqrt (b * c) = Real.sqrt b * Real.sqrt c := by
    rw [Real.sqrt_mul (by positivity)]
  have h5 : sqrt (a * c) = Real.sqrt a * Real.sqrt c := by
    rw [Real.sqrt_mul (by positivity)]
  have h6 : sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
    rw [Real.sqrt_mul (by positivity)]
  rw [h4, h5, h6]
  have h7 : Real.sqrt a ≥ 0 := Real.sqrt_nonneg a
  have h8 : Real.sqrt b ≥ 0 := Real.sqrt_nonneg b
  have h9 : Real.sqrt c ≥ 0 := Real.sqrt_nonneg c
  have h10 : (Real.sqrt a) ^ 2 = a := by
    rw [Real.sq_sqrt]
    linarith
  have h11 : (Real.sqrt b) ^ 2 = b := by
    rw [Real.sq_sqrt]
    linarith
  have h12 : (Real.sqrt c) ^ 2 = c := by
    rw [Real.sq_sqrt]
    linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt a - Real.sqrt c), sq_nonneg (Real.sqrt b - Real.sqrt c),
          Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (c : ℝ) by linarith), 
          mul_nonneg h7 h8, mul_nonneg h7 h9, mul_nonneg h8 h9, 
          mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc, 
          mul_nonneg (show 0 ≤ Real.sqrt a by positivity) (show 0 ≤ Real.sqrt b by positivity), 
          mul_nonneg (show 0 ≤ Real.sqrt a by positivity) (show 0 ≤ Real.sqrt c by positivity), 
          mul_nonneg (show 0 ≤ Real.sqrt b by positivity) (show 0 ≤ Real.sqrt c by positivity)
        ]