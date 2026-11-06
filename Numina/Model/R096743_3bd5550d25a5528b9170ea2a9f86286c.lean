import Mathlib

theorem inequalities_120763 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + 2 * b + 3 * c)^2 / (a^2 + 2 * b^2 + 3 * c^2) ≤ 6 := by 
  have h1 : 0 < a^2 + 2 * b^2 + 3 * c^2 := by 
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h2 : (a + 2 * b + 3 * c)^2 ≤ 6 * (a^2 + 2 * b^2 + 3 * c^2) := by
    nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (a - 3 * c), sq_nonneg (b - c), sq_nonneg (a - (2 * b + 3 * c) / 5)]

  have h4 : (a + 2 * b + 3 * c)^2 / (a^2 + 2 * b^2 + 3 * c^2) ≤ 6 := by
    have h5 : (a + 2 * b + 3 * c)^2 ≤ 6 * (a^2 + 2 * b^2 + 3 * c^2) := by 
      linarith [h2]
    have h6 : (a + 2 * b + 3 * c)^2 / (a^2 + 2 * b^2 + 3 * c^2) ≤ (6 * (a^2 + 2 * b^2 + 3 * c^2)) / (a^2 + 2 * b^2 + 3 * c^2) := by 
      apply (div_le_div_right h1).mpr 
      linarith 
    have h7 : (6 * (a^2 + 2 * b^2 + 3 * c^2)) / (a^2 + 2 * b^2 + 3 * c^2) = 6 := by 
      field_simp 
      <;> nlinarith 
    linarith 
  exact h4