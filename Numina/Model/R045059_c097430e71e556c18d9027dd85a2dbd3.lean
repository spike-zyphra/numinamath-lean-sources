import Mathlib

open Real

theorem inequalities_39073 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c)^2 + a * b + b * c + a * c ≥ 6 * sqrt (a * b * c * (a + b + c)) := by
  have h1 : 0 < a * b * c * (a + b + c) := by
    positivity
  have h5 : ( (a + b + c) ^ 2 + a * b + b * c + a * c ) ^ 2 ≥ 36 * (a * b * c * (a + b + c)) := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - a * c), sq_nonneg (a * b - a * c), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
      sq_nonneg (a * (a + b + c) - b * (a + b + c)), sq_nonneg (b * (a + b + c) - c * (a + b + c)), sq_nonneg (a * (a + b + c) - c * (a + b + c)), 
      mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < b * c from mul_pos hb hc), 
      mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < a * c from mul_pos ha hc)
    ]
  have h6 : 6 * sqrt (a * b * c * (a + b + c)) ≥ 0 := by
    nlinarith [Real.sqrt_nonneg (a * b * c * (a + b + c))]
  have h7 : (a + b + c) ^ 2 + a * b + b * c + a * c ≥ 0 := by positivity
  have h9 : sqrt (a * b * c * (a + b + c)) ≥ 0 := Real.sqrt_nonneg (a * b * c * (a + b + c))
  have h10 : (sqrt (a * b * c * (a + b + c)))^2 = a * b * c * (a + b + c) := by
    rw [Real.sq_sqrt]
    have h11 : 0 ≤ a * b * c * (a + b + c) := by positivity
    linarith
  nlinarith [sq_nonneg ( (a + b + c) ^ 2 + a * b + b * c + a * c - 6 * sqrt (a * b * c * (a + b + c)) ), 
    sq_nonneg ( sqrt (a * b * c * (a + b + c)) ), 
    Real.sqrt_nonneg (a * b * c * (a + b + c)), 
    h5, 
    Real.sq_sqrt (show 0 ≤ a * b * c * (a + b + c) by positivity ), 
    h10
  ]