import Mathlib

theorem inequalities_146745 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    (a ^ 2 + b ^ 2 + c ^ 2) * (a / (b + c) + b / (a + c) + c / (a + b)) ≥ 1 / 2 := by

  have h1 : 0 < b + c := by nlinarith
  have h2 : 0 < a + c := by nlinarith
  have h3 : 0 < a + b := by nlinarith

  have h4 : a ^ 2 + b ^ 2 + c ^ 2 ≥ 1 / 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]

  have h5 : a / (b + c) + b / (a + c) + c / (a + b) ≥ 3 / 2 := by
    have hbc : 0 < b + c := by nlinarith
    have hac : 0 < a + c := by nlinarith
    have hab : 0 < a + b := by nlinarith
    have h6 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 ≥ 0 := by
      have h7 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 =
          (2 * a - (b + c)) / (2 * (b + c)) + (2 * b - (a + c)) / (2 * (a + c)) + (2 * c - (a + b)) / (2 * (a + b)) := by
        field_simp
        ring
      rw [h7]
      have h8 : (2 * a - (b + c)) / (2 * (b + c)) + (2 * b - (a + c)) / (2 * (a + c)) + (2 * c - (a + b)) / (2 * (a + b)) ≥ 0 := by
        have h9 : (2 * a - (b + c)) / (2 * (b + c)) + (2 * b - (a + c)) / (2 * (a + c)) + (2 * c - (a + b)) / (2 * (a + b)) =
            ((2 * a - (b + c)) * (a + c) * (a + b) + (2 * b - (a + c)) * (b + c) * (a + b) + (2 * c - (a + b)) * (b + c) * (a + c)) / (2 * (b + c) * (a + c) * (a + b)) := by
          field_simp
          ring
        rw [h9]
        have h10 : (2 * a - (b + c)) * (a + c) * (a + b) + (2 * b - (a + c)) * (b + c) * (a + b) + (2 * c - (a + b)) * (b + c) * (a + c) ≥ 0 := by
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]
        have h11 : 0 < 2 * (b + c) * (a + c) * (a + b) := by positivity
        exact div_nonneg h10 (by positivity)
      linarith
    linarith

  nlinarith [h4, h5, mul_nonneg (show 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 by nlinarith) (show 0 ≤ a / (b + c) + b / (a + c) + c / (a + b) by positivity)]