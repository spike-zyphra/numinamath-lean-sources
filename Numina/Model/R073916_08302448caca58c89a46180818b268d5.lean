import Mathlib

theorem inequalities_214775 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) +
    1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
  have h1 : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (c - a), sq_nonneg (c + a)]
  have h2 : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (c - a), sq_nonneg (c + a)]
  have h3 : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (a + b + c) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (c - a), sq_nonneg (c + a)]
  have h4 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h5 : 0 < a * b * (a + b + c) := by 
    apply mul_pos
    apply mul_pos
    all_goals nlinarith
  have h6 : 0 < b * c * (a + b + c) := by 
    apply mul_pos
    apply mul_pos
    all_goals nlinarith
  have h7 : 0 < c * a * (a + b + c) := by 
    apply mul_pos
    apply mul_pos
    all_goals nlinarith
  have h8 : 0 < a ^ 3 + b ^ 3 + a * b * c := by 
    nlinarith [sq_nonneg (a), sq_nonneg (b), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h9 : 0 < b ^ 3 + c ^ 3 + a * b * c := by 
    nlinarith [sq_nonneg (b), sq_nonneg (c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h10 : 0 < c ^ 3 + a ^ 3 + a * b * c := by 
    nlinarith [sq_nonneg (c), sq_nonneg (a), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h11 : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by 
    apply (one_div_le_one_div (by linarith) (by linarith)).mpr
    nlinarith
  have h12 : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by 
    apply (one_div_le_one_div (by linarith) (by linarith)).mpr
    nlinarith
  have h13 : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by 
    apply (one_div_le_one_div (by linarith) (by linarith)).mpr
    nlinarith
  have h14 : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
    field_simp
    <;> ring
  linarith [h11, h12, h13, h14]