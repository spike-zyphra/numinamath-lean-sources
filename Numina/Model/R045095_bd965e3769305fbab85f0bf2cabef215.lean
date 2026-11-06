import Mathlib

theorem inequalities_606277 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    a ^ 2 + b ^ 2 + c ^ 2 ≥ Real.sqrt 3 * a * b * c := by

  have h4 : ∀ m : ℝ, m ≥ 0 → Real.sqrt m ^ 2 = m := by
    intro m hm
    have h16 : Real.sqrt m ^ 2 = m := by
      rw [Real.sq_sqrt]
      linarith
    linarith
  
  have h42 : Real.sqrt 3 ≥ 0 := by
    have h3_nonneg : (3 : ℝ) ≥ 0 := by norm_num 
    have hsqrt_nonneg : Real.sqrt 3 ≥ 0 := by
      apply Real.sqrt_nonneg
      all_goals linarith
    exact hsqrt_nonneg

  have h5 : a ^ 2 + b ^ 2 + c ^ 2 ≥ 0 := by positivity
  
  have h6 : a * b * c > 0 := by positivity
  
  have h31 : (a^2 + b^2 + c^2) ^ 2 ≥ (3 : ℝ) * (a * b * c) ^ 2 := by 
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b + c - a * b * c), 
          h, 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]
  
  have h43 : (Real.sqrt 3) * (a * b * c) ≥ 0 := by
    have h44 : Real.sqrt 3 ≥ 0 := h42
    have h45 : a * b * c > 0 := h6
    have h46 : (Real.sqrt 3) * (a * b * c) ≥ 0 := by
      nlinarith [h44, h45]
    exact h46
  
  have h34 : a ^ 2 + b ^ 2 + c ^ 2 ≥ Real.sqrt 3 * (a * b * c) := by
    nlinarith [h31, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          Real.sqrt_nonneg 3, 
          h42
        ]

  have h44 : Real.sqrt 3 * a * b * c = Real.sqrt 3 * (a * b * c) := by ring
  rw [h44] at *
  linarith [h34]