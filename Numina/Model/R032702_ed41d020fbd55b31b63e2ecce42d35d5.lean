import Mathlib

theorem algebra_167583 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a * b = 2) (h2 : c * d = 27) :
    (a + 1) * (b + 2) * (c + 3) * (d + 4) ≥ 600 := by
  have h3 : (a + 1) * (b + 2) ≥ 8 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2),
      h1, mul_pos ha hb
    ]
  -- Prove (c + 3) * (d + 4) ≥ 75
  have h4 : (c + 3) * (d + 4) ≥ 75 := by
    nlinarith [sq_nonneg (c - 9 / 2), sq_nonneg (d - 6),
      h2, mul_pos hc hd
    ]
  -- Multiply the two inequalities and get the final result
  have h5 : (a + 1) * (b + 2) * (c + 3) * (d + 4) ≥ 600 := by
    calc 
      (a + 1) * (b + 2) * (c + 3) * (d + 4)
          = ((a + 1) * (b + 2)) * ((c + 3) * (d + 4)) := by ring
      _ ≥ 8 * 75 := by nlinarith [h3, h4]
      _ = 600 := by norm_num
  -- Final proof through h5
  linarith [h5]