import Mathlib

theorem inequalities_45786 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a + c ≤ a * c) (h2 : b + d ≤ b * d) : a * b + c * d ≥ 8 := by
  have h3 : (a - 1) * (c - 1) ≥ 1 := by 
    nlinarith
  have h4 : (b - 1) * (d - 1) ≥ 1 := by 
    nlinarith 
  have h5 : a * c ≥ 4 := by
    have ha1 : a > 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (c - 1),
        mul_pos ha hc
      ]
    have hc1 : c > 1 := by 
      nlinarith [sq_nonneg (a - 1), sq_nonneg (c - 1),
        mul_pos ha hc
      ]
    nlinarith [sq_nonneg (a - c), mul_pos ha hc, sq_nonneg (a - 2), sq_nonneg (c - 2)]
  have h6 : b * d ≥ 4 := by
    have hb1 : b > 1 := by 
      nlinarith [sq_nonneg (b - 1), sq_nonneg (d - 1), 
        mul_pos hb hd
      ]
    have hd1 : d > 1 := by 
      nlinarith [sq_nonneg (b - 1), sq_nonneg (d - 1), 
        mul_pos hb hd
      ]
    nlinarith [sq_nonneg (b - d), mul_pos hb hd, sq_nonneg (b - 2), sq_nonneg (d - 2)]
  have h7 : (a * b + c * d) ≥ 8 := by
    nlinarith [sq_nonneg (a * b - c * d), sq_nonneg (a * d - b * c), 
      mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
      mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, 
      h5, h6, 
      mul_pos (show 0 < a * c by nlinarith) (show 0 < b * d by nlinarith)
    ]
  exact h7