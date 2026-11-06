import Mathlib

theorem inequalities_603598 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 3) :
    3 / 2 ≤ 1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < b * c := mul_pos hb hc
  have h3 : 0 < c * a := mul_pos hc ha

  have h4 : 1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) - 3 / 2 ≥ 0 := by
    have h_eq1 : 1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) - 3 / 2 =
        (2 * (1 + b * c) * (1 + c * a) + 2 * (1 + a * b) * (1 + c * a) + 2 * (1 + a * b) * (1 + b * c) - 3 * (1 + a * b) * (1 + b * c) * (1 + c * a)) / (2 * (1 + a * b) * (1 + b * c) * (1 + c * a)) := by
      field_simp
      ring
    rw [h_eq1] at *
    
    have h5 : 2 * (1 + a * b) * (1 + b * c) * (1 + c * a) > 0 := by
      have h11 : 0 < 1 + a * b := by
        nlinarith
      have h12 : 0 < 1 + b * c := by
        nlinarith
      have h13 : 0 < 1 + c * a := by
        nlinarith
      positivity

    have h7 : 2 * (1 + b * c) * (1 + c * a) + 2 * (1 + a * b) * (1 + c * a) + 2 * (1 + a * b) * (1 + b * c) - 3 * (1 + a * b) * (1 + b * c) * (1 + c * a) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, mul_pos (show 0 < a * b from by nlinarith) (show 0 < b * c from by nlinarith), mul_pos (show 0 < a * b from by nlinarith) (show 0 < c * a from by nlinarith), mul_pos (show 0 < b * c from by nlinarith) (show 0 < c * a from by nlinarith)
        ]
    
    apply div_nonneg
    linarith [h7]
    all_goals nlinarith [h5]

  linarith [h4]