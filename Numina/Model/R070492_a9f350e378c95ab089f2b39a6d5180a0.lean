import Mathlib

theorem inequalities_99715 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c ≥ 1 / (a * b * c)) : Real.sqrt 3 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  have h1 : a * b * c > 0 := mul_pos (mul_pos ha hb) hc
  have h2 : (a + b + c) * (a * b * c) ≥ 1 := by
    have h3 : (a + b + c) * (a * b * c) ≥ (1 / (a * b * c)) * (a * b * c) := by 
      apply mul_le_mul_of_nonneg_right 
      linarith 
      positivity 
    have h4 : (1 / (a * b * c)) * (a * b * c) = 1 := by 
      field_simp 
    linarith 
  have h5 : (a ^ 2 + b ^ 2 + c ^ 2) ≥ Real.sqrt 3 := by 
    have h6 : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 := by 
      have h5 : (a * b * c * (a + b + c)) ≥ 1 := by 
        linarith 
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        h1, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
    have h10 : ( Real.sqrt 3 ) ^ 2 = (3 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have h11 : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ ( Real.sqrt 3 ) ^ 2 := by 
      nlinarith [h6, show ( Real.sqrt 3 ) ^ 2 >= 0 by positivity, mul_pos (show 0 < a ^ 2 + b ^ 2 + c ^ 2 by nlinarith) (show 0 < a * b * c by positivity), h1, mul_nonneg (show 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 by nlinarith) (show 0 ≤ Real.sqrt 3 by positivity)
      ]
    have h12 : (a ^ 2 + b ^ 2 + c ^ 2) >= 0 := by nlinarith 
    have h13 : 0 <= Real.sqrt 3 := Real.sqrt_nonneg 3
    nlinarith [Real.sqrt_nonneg 3, show 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 by nlinarith, h11, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      ]
  linarith [h5, Real.sqrt_nonneg 3]
  all_goals try linarith