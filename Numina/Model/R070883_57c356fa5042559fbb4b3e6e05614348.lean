import Mathlib

theorem inequalities_597701 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
  have h1 : b + c > 0 := by positivity
  have h2 : c + a > 0 := by positivity
  have h3 : a + b > 0 := by positivity
  have h6 : 2 * a * (c + a) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b) ≥ 0 := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
      sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]
  have h4 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h6' : 2 * a * (c + a) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b) ≥ 0 := h6
    have h5 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 = (2 * a * (c + a) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b)) / (2 * (b + c) * (c + a) * (a + b)) := by 
      field_simp [h1, h2, h3]
      ring
    rw [h5]
    apply div_nonneg 
    linarith [h6']
    positivity
  linarith [h4]