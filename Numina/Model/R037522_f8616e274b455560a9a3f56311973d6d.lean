import Mathlib

theorem inequalities_142309 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    (a + 1 / a) ^ 3 + (b + 1 / b) ^ 3 + (c + 1 / c) ^ 3 ≥ 1000 / 9 := by
  have h1 : (a + 1 / a) ^ 3 + (b + 1 / b) ^ 3 + (c + 1 / c) ^ 3 ≥ 1000 / 9 := by
    have h2 : (a + 1 / a) ^ 3 ≥ - (800 / 3) * a + (3400 / 27) := by
      have h3 : a > 0 := ha
      have h4 : (a + 1 / a) ^ 3 ≥ - (800 / 3) * a + (3400 / 27) := by
        have h5 : (a + 1 / a) ^ 3 - (- (800 / 3) * a + (3400 / 27)) ≥ 0 := by
          have pos1 : a > 0 := ha
          have h6 : (a + 1 / a) ^ 3 - (- (800 / 3) * a + (3400 / 27)) = ( (a ^ 2 + 1) ^ 3 - (- (800 / 3) * a^4 + (3400 / 27) * a^3 ) ) / a^3 := by
            field_simp
            <;> ring
          rw [h6]
          have h8 : ( (a ^ 2 + 1) ^ 3 - (- (800 / 3) * a^4 + (3400 / 27) * a^3 ) ) ≥ 0 := by
            nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (a ^ 2 - 1), sq_nonneg (a - 1), 
                      sq_nonneg (a * (a - 1 / 3) ), sq_nonneg ((a ^ 2 - 1 / 9) ), sq_nonneg ((a * 3 - 1) ), 
                      sq_nonneg (a ^2 - 1/9), sq_nonneg (a^3 -1/27), mul_pos ha ha, mul_pos ha (show 0 < a^2 by positivity)
                    ]
          have h9 : a^3 > 0 := by positivity
          apply div_nonneg 
          linarith
          all_goals positivity
        linarith
      linarith
    have h3 : (b + 1 / b) ^ 3 ≥ - (800 / 3) * b + (3400 / 27) := by
      have h4 : b > 0 := hb
      have h5 : (b + 1 / b) ^ 3 ≥ - (800 / 3) * b + (3400 / 27) := by
        have h6 : (b + 1 / b) ^ 3 - (- (800 / 3) * b + (3400 / 27)) ≥ 0 := by
          have pos1 : b > 0 := hb
          have h6 : (b + 1 / b) ^ 3 - (- (800 / 3) * b + (3400 / 27)) = ( (b ^ 2 + 1) ^ 3 - (- (800 / 3) * b^4 + (3400 / 27) * b^3 ) ) / b^3 := by
            field_simp
            <;> ring
          rw [h6]
          have h8 : ( (b ^ 2 + 1) ^ 3 - (- (800 / 3) * b^4 + (3400 / 27) * b^3 ) ) ≥ 0 := by
            nlinarith [sq_nonneg (b - 1 / 3), sq_nonneg (b ^ 2 - 1), sq_nonneg (b - 1), 
                      sq_nonneg (b * (b - 1 / 3) ), sq_nonneg ((b ^ 2 - 1 / 9) ), sq_nonneg ((b * 3 - 1) ), 
                      sq_nonneg (b ^2 - 1/9), sq_nonneg (b^3 -1/27), mul_pos hb hb, mul_pos hb (show 0 < b^2 by positivity)
                    ]
          have h9 : b^3 > 0 := by positivity
          apply div_nonneg 
          linarith
          all_goals positivity
        linarith
      linarith
    have h4 : (c + 1 / c) ^ 3 ≥ - (800 / 3) * c + (3400 / 27) := by
      have h5 : c > 0 := hc
      have h6 : (c + 1 / c) ^ 3 ≥ - (800 / 3) * c + (3400 / 27) := by
        have h7 : (c + 1 / c) ^ 3 - (- (800 / 3) * c + (3400 / 27)) ≥ 0 := by
          have pos1 : c > 0 := hc
          have h7 : (c + 1 / c) ^ 3 - (- (800 / 3) * c + (3400 / 27)) = ( (c ^ 2 + 1) ^ 3 - (- (800 / 3) * c^4 + (3400 / 27) * c^3 ) ) / c^3 := by
            field_simp
            <;> ring
          rw [h7]
          have h8 : ( (c ^ 2 + 1) ^ 3 - (- (800 / 3) * c^4 + (3400 / 27) * c^3 ) ) ≥ 0 := by
            nlinarith [sq_nonneg (c - 1 / 3), sq_nonneg (c ^ 2 - 1), sq_nonneg (c - 1), 
                      sq_nonneg (c * (c - 1 / 3) ), sq_nonneg ((c ^ 2 - 1 / 9) ), sq_nonneg ((c * 3 - 1) ), 
                      sq_nonneg (c ^2 - 1/9), sq_nonneg (c^3 -1/27), mul_pos hc hc, mul_pos hc (show 0 < c^2 by positivity)
                    ]
          have h9 : c^3 > 0 := by positivity
          apply div_nonneg 
          linarith
          all_goals positivity
        linarith
      linarith
    linarith [h2, h3, h4, h]
  linarith