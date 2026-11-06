import Mathlib

theorem inequalities_598560 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a * b / (a^5 + b^5 + a * b)) + (b * c / (b^5 + c^5 + b * c)) +
    (c * a / (c^5 + a^5 + c * a)) ≤ 1 := by
  have h1 : a * b / (a^5 + b^5 + a * b) ≤ 1 / (a * b * (a + b) + 1) := by
    have h2 : a^5 + b^5 ≥ a^2 * b^2 * (a + b) := by
      nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a * b - 1), sq_nonneg (a - b), sq_nonneg (a * (a - b)), sq_nonneg (b * (b - a)), sq_nonneg (a * b), sq_nonneg (a + b), mul_pos ha hb, habc]
    have h3 : a * b * (a^5 + b^5 + a * b) ≥ a * b * (a^2 * b^2 * (a + b) + a * b) := by 
      apply mul_le_mul_of_nonneg_left
      linarith
      positivity
    have h4 : a * b / (a^5 + b^5 + a * b) ≤ 1 / (a * b * (a + b) + 1) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    exact h4
  have h2 : b * c / (b^5 + c^5 + b * c) ≤ 1 / (b * c * (b + c) + 1) := by
    have h3 : b^5 + c^5 ≥ b^2 * c^2 * (b + c) := by
      nlinarith [sq_nonneg (b^2 - c^2), sq_nonneg (b * c - 1), sq_nonneg (b - c), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - b)), sq_nonneg (b * c), sq_nonneg (b + c), mul_pos hb hc, habc]
    have h4 : b * c * (b^5 + c^5 + b * c) ≥ b * c * (b^2 * c^2 * (b + c) + b * c) := by 
      apply mul_le_mul_of_nonneg_left
      linarith
      positivity
    have h5 : b * c / (b^5 + c^5 + b * c) ≤ 1 / (b * c * (b + c) + 1) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    exact h5
  have h3 : c * a / (c^5 + a^5 + c * a) ≤ 1 / (c * a * (c + a) + 1) := by
    have h4 : c^5 + a^5 ≥ c^2 * a^2 * (c + a) := by
      nlinarith [sq_nonneg (c^2 - a^2), sq_nonneg (c * a - 1), sq_nonneg (c - a), sq_nonneg (c * (c - a)), sq_nonneg (a * (a - c)), sq_nonneg (c * a), sq_nonneg (c + a), mul_pos hc ha, habc]
    have h5 : c * a * (c^5 + a^5 + c * a) ≥ c * a * (c^2 * a^2 * (c + a) + c * a) := by 
      apply mul_le_mul_of_nonneg_left
      linarith
      positivity
    have h6 : c * a / (c^5 + a^5 + c * a) ≤ 1 / (c * a * (c + a) + 1) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    exact h6
  have h4 : 1 / (a * b * (a + b) + 1) + 1 / (b * c * (b + c) + 1) + 1 / (c * a * (c + a) + 1) ≤ 1 := by
    have h5 : 1 / (a * b * (a + b) + 1) ≤ c / (a + b + c) := by
      have h6 : a * b * (a + b) + 1 > 0 := by positivity
      have h7 : c > 0 := by positivity
      have h8 : a + b + c > 0 := by positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [habc, sq_nonneg (a - b), sq_nonneg (a * b - 1), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have h6 : 1 / (b * c * (b + c) + 1) ≤ a / (b + c + a) := by
      have h7 : b * c * (b + c) + 1 > 0 := by positivity
      have h8 : a > 0 := by positivity
      have h9 : b + c + a > 0 := by positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [show b * c = (b * c) by rfl, show a * (b + c) = a * (b + c) by rfl, habc, sq_nonneg (b - c), sq_nonneg (b * c - 1), mul_pos hb hc, mul_pos ha hb, mul_pos ha hc]
    have h7 : 1 / (c * a * (c + a) + 1) ≤ b / (c + a + b) := by
      have h8 : c * a * (c + a) + 1 > 0 := by positivity
      have h9 : b > 0 := by positivity
      have h10 : c + a + b > 0 := by positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [show c * a = c * a by rfl, show b * (c + a) = b * (c + a) by rfl, habc, sq_nonneg (c - a), sq_nonneg (c * a - 1), mul_pos hc ha, mul_pos hb ha, mul_pos hb hc]
    have h8 : c / (a + b + c) + a / (b + c + a) + b / (c + a + b) = 1 := by
      field_simp
      <;> nlinarith
    linarith [h5, h6, h7, h8]
  linarith [h1, h2, h3, h4]