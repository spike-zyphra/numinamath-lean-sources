import Mathlib

theorem inequalities_50445 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a ^ 2 + b ^ 2) / (a ^ 4 + b ^ 4) + (b ^ 2 + c ^ 2) / (b ^ 4 + c ^ 4) +
    (c ^ 2 + a ^ 2) / (c ^ 4 + a ^ 4) ≤ a + b + c := by
  have h2 : (a ^ 2 + b ^ 2) / (a ^ 4 + b ^ 4) ≤ 1 / (a * b) := by
    have h3 : a ^ 4 + b ^ 4 ≥ 2 * (a * b) ^ 2 := by
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a * b - 1), sq_nonneg (a - b), sq_nonneg (a * b), sq_nonneg (a - 1), sq_nonneg (b - 1), mul_pos ha hb]
    have h4 : 0 < a * b := mul_pos ha hb
    have h6 : a * b * (a ^ 2 + b ^ 2) ≤ a ^ 4 + b ^ 4 := by
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a * b - 1), sq_nonneg (a - b), sq_nonneg (a * b), sq_nonneg (a - 1), sq_nonneg (b - 1), mul_pos ha hb, sq_nonneg (a * b)]
    have h7 : a ^ 4 + b ^ 4 > 0 := by positivity
    have h8 : a * b > 0 := h4
    have h9 : (a ^ 2 + b ^ 2) / (a ^ 4 + b ^ 4) ≤ 1 / (a * b) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a * b - 1), sq_nonneg (a - b), sq_nonneg (a * b), sq_nonneg (a - 1), sq_nonneg (b - 1), mul_pos ha hb]
    exact h9
  have h3 : (b ^ 2 + c ^ 2) / (b ^ 4 + c ^ 4) ≤ 1 / (b * c) := by
    have h4 : b ^ 4 + c ^ 4 ≥ 2 * (b * c) ^ 2 := by
      nlinarith [sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b * c - 1), sq_nonneg (b - c), sq_nonneg (b * c), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_pos hb hc]
    have h5 : 0 < b * c := mul_pos hb hc
    have h7 : b * c * (b ^ 2 + c ^ 2) ≤ b ^ 4 + c ^ 4 := by
      nlinarith [sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b * c - 1), sq_nonneg (b - c), sq_nonneg (b * c), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_pos hb hc, sq_nonneg (b * c)]
    have h7' : b ^ 4 + c ^ 4 > 0 := by positivity
    have h8' : b * c > 0 := h5
    have h9 : (b ^ 2 + c ^ 2) / (b ^ 4 + c ^ 4) ≤ 1 / (b * c) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b * c - 1), sq_nonneg (b - c), sq_nonneg (b * c), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_pos hb hc]
    exact h9
  have h4 : (c ^ 2 + a ^ 2) / (c ^ 4 + a ^ 4) ≤ 1 / (c * a) := by
    have h5 : c ^ 4 + a ^ 4 ≥ 2 * (c * a) ^ 2 := by
      nlinarith [sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c * a - 1), sq_nonneg (c - a), sq_nonneg (c * a), sq_nonneg (c - 1), sq_nonneg (a - 1), mul_pos hc ha]
    have h6 : 0 < c * a := mul_pos hc ha
    have h8 : c * a * (c ^ 2 + a ^ 2) ≤ c ^ 4 + a ^ 4 := by
      nlinarith [sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c * a - 1), sq_nonneg (c - a), sq_nonneg (c * a), sq_nonneg (c - 1), sq_nonneg (a - 1), mul_pos hc ha, sq_nonneg (c * a)]
    have h9 : c ^ 4 + a ^ 4 > 0 := by positivity
    have h10 : c * a > 0 := h6
    have h11 : (c ^ 2 + a ^ 2) / (c ^ 4 + a ^ 4) ≤ 1 / (c * a) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c * a - 1), sq_nonneg (c - a), sq_nonneg (c * a), sq_nonneg (c - 1), sq_nonneg (a - 1), mul_pos hc ha]
    exact h11
  have h5 : (a ^ 2 + b ^ 2) / (a ^ 4 + b ^ 4) + (b ^ 2 + c ^ 2) / (b ^ 4 + c ^ 4) + (c ^ 2 + a ^ 2) / (c ^ 4 + a ^ 4) ≤ (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) := by
    linarith [h2, h3, h4]
  have h6 : (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) = a + b + c := by
    have h7 : a * b * c = 1 := habc
    have h8 : 1 / (a * b) = c := by
      field_simp [(show 0 < a * b by positivity)]
      <;> nlinarith
      all_goals linarith
      all_goals try { tauto }
    have h9 : 1 / (b * c) = a := by
      field_simp [(show 0 < b * c by positivity)]
      <;> nlinarith
      all_goals linarith
      all_goals try { tauto }
    have h10 : 1 / (c * a) = b := by
      field_simp [(show 0 < c * a by positivity)]
      <;> nlinarith
      all_goals linarith
      all_goals try { tauto }
    rw [h8, h9, h10]
    all_goals linarith
    all_goals try { tauto }
  linarith [h5, h6]
  all_goals try { positivity }
  all_goals try { tauto }