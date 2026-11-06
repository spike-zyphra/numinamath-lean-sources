import Mathlib


theorem inequalities_55397 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^4 + b^4 + c^4 = 3) :
    1 / (4 - a * b) + 1 / (4 - b * c) + 1 / (4 - c * a) ≤ 1 := by

  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < b * c := mul_pos hb hc
  have h3 : 0 < c * a := mul_pos hc ha


  have h5 : 1 / (4 - a * b) + 1 / (4 - b * c) + 1 / (4 - c * a) - 1 ≤ 0 := by

    have h7 : 4 - a * b > 0 := by
      nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1), sq_nonneg (c^2 - 1),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, h
      ]
    have h8 : 4 - b * c > 0 := by
      nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1), sq_nonneg (c^2 - 1),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, h
      ]
    have h9 : 4 - c * a > 0 := by
      nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1), sq_nonneg (c^2 - 1),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, h
      ]

    have h9 : (1 / (4 - a * b) + 1 / (4 - b * c) + 1 / (4 - c * a) - 1) =
        ((4 - b * c) * (4 - c * a) + (4 - a * b) * (4 - c * a) + (4 - a * b) * (4 - b * c) - (4 - a * b) * (4 - b * c) * (4 - c * a)) / ((4 - a * b) * (4 - b * c) * (4 - c * a)) := by
      field_simp
      ring
    rw [h9]

    have h8 : (4 - b * c) * (4 - c * a) + (4 - a * b) * (4 - c * a) + (4 - a * b) * (4 - b * c) - (4 - a * b) * (4 - b * c) * (4 - c * a) ≤ 0 := by
      nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a^2 + b^2 + c^2 - 3), sq_nonneg (a * b + b * c + c * a - 3),
          mul_pos ha hb, mul_pos hb hc, mul_pos hc ha,
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith),
          mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith),
          mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ a by linarith),
          h
      ]

    have h7 : ((4 - b * c) * (4 - c * a) + (4 - a * b) * (4 - c * a) + (4 - a * b) * (4 - b * c) - (4 - a * b) * (4 - b * c) * (4 - c * a)) / ((4 - a * b) * (4 - b * c) * (4 - c * a)) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      linarith
      positivity
    linarith

  linarith