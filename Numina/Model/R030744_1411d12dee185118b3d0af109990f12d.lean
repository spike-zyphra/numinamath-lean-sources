import Mathlib

theorem algebra_606079 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) +
    1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
  have h1 : 0 < a * b * c := by positivity
  have h2 : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h3 : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := by 
    nlinarith [sq_nonneg (b - c), sq_nonneg (b - a), sq_nonneg (c - a), 
      mul_pos hb hc, mul_pos hb ha, mul_pos hc ha]
  have h4 : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (a + b + c) := by
    nlinarith [sq_nonneg (c - a), sq_nonneg (c - b), sq_nonneg (a - b),
      mul_pos hc ha, mul_pos hc hb, mul_pos ha hb]
  have h5 : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    linarith [h2]
  have h6 : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    linarith [h3]
  have h7 : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    linarith [h4]
  have h8 : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
    field_simp
    <;> nlinarith
  have h9 : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) := by
    linarith [h5, h6, h7]
  linarith [h9, h8]