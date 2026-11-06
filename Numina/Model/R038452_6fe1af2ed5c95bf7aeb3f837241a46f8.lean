import Mathlib
theorem algebra_605126 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a + b + c ≥ √((a + 2) * (b + 2) * (c + 2) / 3) := by 
  have h1 : (a + b + c) ^ 2 ≥ (a + 2) * (b + 2) * (c + 2) / 3 := by
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
      sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  have h2 : (a + b + c) ≥ Real.sqrt ((a + 2) * (b + 2) * (c + 2) / 3) := by 
    have h3 : Real.sqrt ((a + b + c) ^ 2) ≥ Real.sqrt ((a + 2) * (b + 2) * (c + 2) / 3) := by
      apply Real.sqrt_le_sqrt
      linarith [h1]
    have h4 : Real.sqrt ((a + b + c) ^ 2) = a + b + c := by
      rw [Real.sqrt_sq (show 0 ≤ a + b + c by linarith [ha, hb, hc])]
    linarith [h3, h4]
  exact h2