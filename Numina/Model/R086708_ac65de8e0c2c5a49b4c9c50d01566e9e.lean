import Mathlib

theorem inequalities_602727 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a ^ 3 + b ^ 3 + a * b * c) +
    1 / (b ^ 3 + c ^ 3 + a * b * c) +
    1 / (c ^ 3 + a ^ 3 + a * b * c) ≤
    1 / (a * b * c) := by
  have h1 : a^ 3 + b^ 3 ≥ a * b * (a + b) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a^2 - a * b), sq_nonneg (b^2 - a * b), sq_nonneg (a * b), sq_nonneg (a - b), sq_nonneg (a * b - b^2), sq_nonneg (a * b - a^2), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  have h2 : b^ 3 + c^ 3 ≥ b * c * (b + c) := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (b^2 - b * c), sq_nonneg (c^2 - b * c), sq_nonneg (b * c), sq_nonneg (b - c), sq_nonneg (b * c - c^2), sq_nonneg (b * c - b^2), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  have h3 : c^ 3 + a^ 3 ≥ c * a * (c + a) := by
    nlinarith [sq_nonneg (c - a), sq_nonneg (c^2 - c * a), sq_nonneg (a^2 - c * a), sq_nonneg (c * a), sq_nonneg (c - a), sq_nonneg (c * a - a^2), sq_nonneg (c * a - c^2), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  have h4 : a^ 3 + b^ 3 + a * b * c ≥ a * b * (a + b + c) := by
    nlinarith [h1, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h8 : b^ 3 + c^ 3 + a * b * c ≥ b * c * (a + b + c) := by
    nlinarith [h2, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h10 : c^ 3 + a^ 3 + a * b * c ≥ c * a * (a + b + c) := by
    nlinarith [h3, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h11 : 1 / (a^ 3 + b^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    all_goals nlinarith [h4, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h12 : 1 / (b^ 3 + c^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    all_goals nlinarith [h8, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h13 : 1 / (c^ 3 + a^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    all_goals nlinarith [h10, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h14 : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
    field_simp [show 0 < a * b by positivity, show 0 < b * c by positivity, show 0 < c * a by positivity, show 0 < a + b + c by positivity]
    <;> ring
  linarith [h11, h12, h13, h14]