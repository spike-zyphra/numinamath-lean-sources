import Mathlib

theorem inequalities_323797 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a^3 + b^3 + a * b * c) +
    1 / (b^3 + c^3 + a * b * c) +
    1 / (c^3 + a^3 + a * b * c) ≤
    1 / (a * b * c) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : a^3 + b^3 ≥ a * b * (a + b) := by
    nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a - b), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  have h3 : b^3 + c^3 ≥ b * c * (b + c) := by
    nlinarith [sq_nonneg (b^2 - c^2), sq_nonneg (b - c), sq_nonneg (b * (b - c)), sq_nonneg (c * (b - c)), mul_pos hb hc, mul_pos hb ha, mul_pos hc ha
    ]
  have h4 : c^3 + a^3 ≥ c * a * (c + a) := by
    nlinarith [sq_nonneg (c^2 - a^2), sq_nonneg (c - a), sq_nonneg (c * (c - a)), sq_nonneg (a * (c - a)), mul_pos hc ha, mul_pos hc hb, mul_pos ha hb
    ]
  have h5 : a^3 + b^3 + a * b * c ≥ a * b * (a + b + c) := by
    nlinarith [h2, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  have h6 : b^3 + c^3 + a * b * c ≥ b * c * (a + b + c) := by
    nlinarith [h3, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  have h7 : c^3 + a^3 + a * b * c ≥ c * a * (a + b + c) := by
    nlinarith [h4, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  have h8 : 1 / (a^3 + b^3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    all_goals nlinarith [h5]
  have h9 : 1 / (b^3 + c^3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    all_goals nlinarith [h6]
  have h10 : 1 / (c^3 + a^3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    all_goals nlinarith [h7]
  have h11 : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
    field_simp
    <;> nlinarith [ha, hb, hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  linarith [h8, h9, h10, h11]