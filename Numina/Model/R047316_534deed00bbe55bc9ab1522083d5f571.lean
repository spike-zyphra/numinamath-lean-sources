import Mathlib

open Real

theorem inequalities_105929
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a + b + c = 1) :
    a * sqrt (2 * b + 1) + b * sqrt (2 * c + 1) + c * sqrt (2 * a + 1) ≤
    sqrt (2 - (a ^ 2 + b ^ 2 + c ^ 2)) := by

  have h11 : 2 - (a ^ 2 + b ^ 2 + c ^ 2) ≥ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
              h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h14 : (a * sqrt (2 * b + 1) + b * sqrt (2 * c + 1) + c * sqrt (2 * a + 1)) ^ 2 ≤ 2 - (a ^ 2 + b ^ 2 + c ^ 2) := by
    have h21 : sqrt (2 * b + 1) ^ 2 = 2 * b + 1 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h22 : sqrt (2 * c + 1) ^ 2 = 2 * c + 1 := by 
      rw [Real.sq_sqrt]
      nlinarith
    have h23 : sqrt (2 * a + 1) ^ 2 = 2 * a + 1 := by
      rw [Real.sq_sqrt]
      nlinarith
    nlinarith [mul_nonneg (Real.sqrt_nonneg (2 * b + 1)) (Real.sqrt_nonneg (2 * c + 1)), 
              mul_nonneg (Real.sqrt_nonneg (2 * c + 1)) (Real.sqrt_nonneg (2 * a + 1)), 
              mul_nonneg (Real.sqrt_nonneg (2 * a + 1)) (Real.sqrt_nonneg (2 * b + 1)),
              sq_nonneg (sqrt (2 * b + 1) - sqrt (2 * c + 1)), 
              sq_nonneg (sqrt (2 * c + 1) - sqrt (2 * a + 1)), 
              sq_nonneg (sqrt (2 * a + 1) - sqrt (2 * b + 1)), 
              Real.sq_sqrt (show 2 * b + 1 ≥ 0 by nlinarith), 
              Real.sq_sqrt (show 2 * c + 1 ≥ 0 by nlinarith), 
              Real.sq_sqrt (show 2 * a + 1 ≥ 0 by nlinarith), 
              h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]

  have h15 : sqrt (2 - (a ^ 2 + b ^ 2 + c ^ 2)) ≥ 0 := by positivity
  have h16 : a * sqrt (2 * b + 1) + b * sqrt (2 * c + 1) + c * sqrt (2 * a + 1) ≥ 0 := by positivity

  have h17 : a * sqrt (2 * b + 1) + b * sqrt (2 * c + 1) + c * sqrt (2 * a + 1) ≤ sqrt (2 - (a ^ 2 + b ^ 2 + c ^ 2)) := by 
    have h18 : (a * sqrt (2 * b + 1) + b * sqrt (2 * c + 1) + c * sqrt (2 * a + 1)) ^ 2 ≤ 2 - (a ^ 2 + b ^ 2 + c ^ 2) := h14
    have h19 : sqrt (2 - (a ^ 2 + b ^ 2 + c ^ 2)) ≥ 0 := h15
    have h20 : (a * sqrt (2 * b + 1) + b * sqrt (2 * c + 1) + c * sqrt (2 * a + 1)) ≥ 0 := h16
    have h21 : (sqrt (2 - (a ^ 2 + b ^ 2 + c ^ 2))) ^ 2 = 2 - (a ^ 2 + b ^ 2 + c ^ 2) := by 
      rw [Real.sq_sqrt]
      nlinarith
    nlinarith [Real.sqrt_nonneg (2 - (a ^ 2 + b ^ 2 + c ^ 2)), 
              Real.sq_sqrt (show 2 - (a ^ 2 + b ^ 2 + c ^ 2) ≥ 0 by linarith [h11]
              )
    ]
  exact h17