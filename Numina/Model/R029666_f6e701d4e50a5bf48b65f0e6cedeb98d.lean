import Mathlib
set_option maxHeartbeats 200000000
theorem inequalities_168319 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c ≤ a + b + c) :
    a ^ 2 + b ^ 2 + c ^ 2 ≥ Real.sqrt 3 * a * b * c := by
  have h11 : (a ^ 2 + b ^ 2 + c ^ 2 ) ^ 2 ≥ 3 * (a * b * c ) ^ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        mul_pos (mul_pos ha hb) (hc)
      ]
  have h14 : a ^ 2 + b ^ 2 + c ^ 2 ≥ Real.sqrt 3 * (a * b * c ) := by
    have h15 : (a ^ 2 + b ^ 2 + c ^ 2 ) ^ 2 ≥ 3 * (a * b * c ) ^ 2 := h11
    have h15' : Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2 ) ^ 2 ) ≥ Real.sqrt (3 * (a * b * c ) ^ 2 ) := by
      apply Real.sqrt_le_sqrt
      linarith [h15]
    have h17 : Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2 ) ^ 2 ) = (a ^ 2 + b ^ 2 + c ^ 2 ) := by
      rw [Real.sqrt_sq (show 0 ≤ (a ^ 2 + b ^ 2 + c ^ 2 ) by positivity)]
    have h18 : Real.sqrt (3 * (a * b * c ) ^ 2 ) = Real.sqrt 3 * (a * b * c ) := by 
      have h19 : Real.sqrt (3 * (a * b * c ) ^ 2 ) = Real.sqrt (3 * ((a * b * c ) ^ 2 ) ) := by ring_nf
      rw [h19]
      have h20 : Real.sqrt (3 * ((a * b * c ) ^ 2 ) ) = Real.sqrt (3 ) * Real.sqrt ( ( (a * b * c ) ^ 2 ) ) := by 
        rw [Real.sqrt_mul (by positivity)]
      rw [h20]
      have h21 : Real.sqrt ( ( (a * b * c ) ^ 2 ) ) = (a * b * c ) := by 
        rw [Real.sqrt_sq (by positivity)]
      rw [h21]
    rw [h17, h18] at h15'
    linarith 
  linarith [h14]