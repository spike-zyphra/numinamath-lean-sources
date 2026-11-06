import Mathlib

theorem algebra_179583 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a^2 + a * b + b^2 = 1) (h2 : b^2 + b * c + c^2 = 3) (h3 : c^2 + c * a + a^2 = 4) :
    a + b + c = Real.sqrt 7 := by
  have h4 : (a + b + c) ^ 2 = 7 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  have h5 : a + b + c > 0 := by
    linarith [ha, hb, hc]
  have h6 : a + b + c = Real.sqrt 7 := by
    have h7 : Real.sqrt ((a + b + c) ^ 2) = Real.sqrt 7 := by
      rw [h4]
    have h8 : Real.sqrt ((a + b + c) ^ 2) = a + b + c := by
      rw [Real.sqrt_sq]
      linarith
    rw [h8] at h7
    linarith
  exact h6