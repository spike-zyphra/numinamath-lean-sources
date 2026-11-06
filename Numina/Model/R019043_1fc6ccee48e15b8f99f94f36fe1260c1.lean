import Mathlib

theorem inequalities_97319 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a^3 + b^3 + a * b * c) +
    1 / (b^3 + c^3 + a * b * c) +
    1 / (a^3 + c^3 + a * b * c) ≤
    1 / (a * b * c) := by
  have h1 : 0 < a * b * c := by
    positivity

  have h2 : a ^ 3 + b ^ 3 ≥ a * b * (a + b) := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a ^ 2 - b ^ 2)]

  have h3 : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := by
    nlinarith [h2]

  have h4 : b ^ 3 + c ^ 3 ≥ b * c * (b + c) := by 
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (b ^ 2 - c ^ 2)]

  have h5 : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := by
    nlinarith [h4, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h6 : a ^ 3 + c ^ 3 ≥ a * c * (a + c) := by 
    nlinarith [sq_nonneg (a - c), sq_nonneg (a + c), sq_nonneg (a ^ 2 - c ^ 2)]

  have h7 : a ^ 3 + c ^ 3 + a * b * c ≥ a * c * (a + b + c) := by
    nlinarith [h6, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h8 : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by 
    apply one_div_le_one_div_of_le 
    positivity 
    all_goals nlinarith [h3]

  have h9 : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by 
    apply one_div_le_one_div_of_le 
    positivity 
    all_goals nlinarith [h5]

  have h10 : 1 / (a ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (a * c * (a + b + c)) := by
    apply one_div_le_one_div_of_le 
    positivity 
    all_goals nlinarith [h7]

  have h11 : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (a * c * (a + b + c)) = 1 / (a * b * c) := by 
    field_simp 
    <;> ring

  linarith [h8, h9, h10, h11, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]