import Mathlib

theorem inequalities_36215 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a * b / (a * b + a ^ 5 + b ^ 5) + b * c / (b * c + b ^ 5 + c ^ 5) +
    c * a / (c * a + c ^ 5 + a ^ 5) ≤ 1 := by
  have h1 : a * b / (a * b + a ^ 5 + b ^ 5) ≤ 1 / (1 + a * b * (a + b)) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a * b - b * a), mul_pos ha hb, sq_nonneg (a + b), sq_nonneg (a * b), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), sq_nonneg (a * (a ^ 2 - b ^ 2)), sq_nonneg (b * (a ^ 2 - b ^ 2))]
  have h2 : b * c / (b * c + b ^ 5 + c ^ 5) ≤ 1 / (1 + b * c * (b + c)) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b - c), sq_nonneg (b * c - c * b), mul_pos hb hc, sq_nonneg (b + c), sq_nonneg (b * c), sq_nonneg (b * (b - c)), sq_nonneg (c * (b - c)), sq_nonneg (b * (b ^ 2 - c ^ 2)), sq_nonneg (c * (b ^ 2 - c ^ 2))]
  have h3 : c * a / (c * a + c ^ 5 + a ^ 5) ≤ 1 / (1 + c * a * (c + a)) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c - a), sq_nonneg (c * a - a * c), mul_pos hc ha, sq_nonneg (c + a), sq_nonneg (c * a), sq_nonneg (c * (c - a)), sq_nonneg (a * (c - a)), sq_nonneg (c * (c ^ 2 - a ^ 2)), sq_nonneg (a * (c ^ 2 - a ^ 2))]
  have h4 : a * b / (a * b + a ^ 5 + b ^ 5) + b * c / (b * c + b ^ 5 + c ^ 5) + c * a / (c * a + c ^ 5 + a ^ 5) ≤ 1 / (1 + a * b * (a + b)) + 1 / (1 + b * c * (b + c)) + 1 / (1 + c * a * (c + a)) := by
    linarith [h1, h2, h3]
  have h5 : 1 / (1 + a * b * (a + b)) + 1 / (1 + b * c * (b + c)) + 1 / (1 + c * a * (c + a)) ≤ 1 := by
    have habc' : c = 1 / (a * b) := by
      field_simp [(show 0 < a * b from by nlinarith [ha, hb])]
      nlinarith [habc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    rw [habc']
    have h1 : 1 / (1 + a * b * (a + b)) + 1 / (1 + b * (1 / (a * b)) * (b + 1 / (a * b))) + 1 / (1 + (1 / (a * b)) * a * (1 / (a * b) + a)) = 1 := by
      field_simp [(show 0 < a * b by nlinarith), (show 0 < a * b * a by nlinarith), (show 0 < a * b * b by nlinarith)] at *
      <;> nlinarith [habc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
    linarith [h1
      ]
  linarith [h4, h5
    ]