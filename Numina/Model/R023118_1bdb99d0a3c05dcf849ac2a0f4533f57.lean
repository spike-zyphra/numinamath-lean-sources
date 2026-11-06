import Mathlib

theorem inequalities_599586 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) +
    1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by

  have h1 : a ^ 3 + b ^ 3 ≥ a * b * (a + b) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  
  have h2 : b ^ 3 + c ^ 3 ≥ b * c * (b + c) := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c)]
  
  have h3 : c ^ 3 + a ^ 3 ≥ c * a * (c + a) := by
    nlinarith [sq_nonneg (c - a), sq_nonneg (c + a)]
  
  have h4 : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := by
    nlinarith
  
  have h5 : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := by
    nlinarith
  
  have h6 : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (a + b + c) := by
    nlinarith
  
  have h7 : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    linarith
  
  have h8 : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    linarith
  
  have h9 : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    linarith
  
  have h10 : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
    field_simp [show 0 < a * b * c from mul_pos (mul_pos ha hb) hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    <;> ring
  
  linarith [h7, h8, h9, h10]