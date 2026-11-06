import Mathlib

theorem algebra_266296 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a * b + c * d = 4) (h2 : a * c + b * d = 4) (h3 : a * d + b * c = 5) :
    a + b + c + d ≥ 6 := by
  have h4 : (a + d) * (b + c) = 8 := by
    nlinarith
  have h5 : (a + b) * (c + d) = 9 := by
    nlinarith
  nlinarith [sq_nonneg (a + b - 3), sq_nonneg (c + d - 3), 
          sq_nonneg (a + d - 2), sq_nonneg (b + c - 4), 
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
          mul_pos hb hc, mul_pos hb hd, mul_pos hc hd
]