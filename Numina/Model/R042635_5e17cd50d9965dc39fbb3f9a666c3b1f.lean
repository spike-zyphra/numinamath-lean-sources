import Mathlib

theorem inequalities_297462 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c = 1) :
    1 / a + 1 / b + 1 / c + 3 / (a + b + c) ≥ 4 := by

  have h₁ : 0 < a + b + c := by
    have h₁ : 0 < a := ha
    have h₂ : 0 < b := hb
    have h₃ : 0 < c := hc
    linarith
  have h2 : 1 / a + 1 / b + 1 / c = a * b + a * c + b * c := by
    field_simp
    nlinarith [h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  rw [h2]

  have h3 : a * b + a * c + b * c ≥ 3 := by
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1), 
      h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
  have h4 : (a + b + c) > 0 := h₁
  have h5 : (a * b + a * c + b * c) * (a + b + c) + 3 - 4 * (a + b + c) ≥ 0 := by
    have h2 : a * b * c = 1 := h
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
      sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
      h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
  have h6a : (a * b + a * c + b * c + 3 / (a + b + c) ) - 4 =
    ((a * b + a * c + b * c) * (a + b + c) + 3 - 4 * (a + b + c)) / ((a + b + c)) := by
    field_simp
    nlinarith
  have h6b : ((a * b + a * c + b * c) * (a + b + c) + 3 - 4 * (a + b + c)) / ((a + b + c)) ≥ 0 := by
    apply div_nonneg
    nlinarith
    all_goals linarith
  linarith [h6a, h6b]