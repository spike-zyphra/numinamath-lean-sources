import Mathlib.Tactic

theorem inequalities_599857 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) +
    1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by

  have h1 : b ^ 3 + c ^ 3 ≥ b ^ 2 * c + b * c ^ 2 := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c)]
  
  have h1' : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), h1]
  
  have h2 : c ^ 3 + a ^ 3 ≥ c ^ 2 * a + c * a ^ 2 := by
    nlinarith [sq_nonneg (c - a), sq_nonneg (c + a)]
  
  have h2' : c ^ 3 + a ^ 3 + a * b * c ≥ a * c * (a + b + c) := by
    nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), h2]

  have h3 : a ^ 3 + b ^ 3 ≥ a ^ 2 * b + a * b ^ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  
  have h3' : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), h3]

  have h4 : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    all_goals
    nlinarith [h1']
  
  have h5 : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * c * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    all_goals
    nlinarith [h2']

  have h6 : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    apply one_div_le_one_div_of_le
    positivity
    all_goals
    nlinarith [h3']
  
  have h7 : 1 / (b * c * (a + b + c)) + 1 / (a * c * (a + b + c)) + 1 / (a * b * (a + b + c)) = 1 / (a * b * c) := by
    field_simp
    ring

  have h8 : 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) +
    1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) + 1 / (a * c * (a + b + c)) + 1 / (a * b * (a + b + c)) := by
    linarith [h4, h5, h6]

  linarith [h8, h7]