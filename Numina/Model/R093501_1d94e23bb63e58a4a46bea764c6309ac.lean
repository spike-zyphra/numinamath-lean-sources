import Mathlib

theorem inequalities_92458 (a b c : ℝ) (ha : 0 < a ∧ a ≤ 2) (hb : 0 < b ∧ b ≤ 2) (hc : 0 < c ∧ c ≤ 2) :
    a * b * c / (a + b + c) ≤ 4 / 3 := by
  rcases ha with ⟨ha_pos, ha_le_2⟩
  rcases hb with ⟨hb_pos, hb_le_2⟩
  rcases hc with ⟨hc_pos, hc_le_2⟩
  have h1 : 0 < a + b + c := by
    linarith
  have h2 : 3 * (a * b * c) ≤ 4 * (a + b + c) := by
    nlinarith [show 0 ≤ 2 - a from by linarith, show 0 ≤ 2 - b from by linarith, show 0 ≤ 2 - c from by linarith,
        mul_nonneg (show 0 ≤ 2 - a by linarith) (show 0 ≤ 2 - b by linarith),
        mul_nonneg (show 0 ≤ 2 - a by linarith) (show 0 ≤ 2 - c by linarith),
        mul_nonneg (show 0 ≤ 2 - b by linarith) (show 0 ≤ 2 - c by linarith),
        mul_pos ha_pos hb_pos, mul_pos hb_pos hc_pos, mul_pos hc_pos ha_pos,
        mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith),
        mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith),
        mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith)]
  have h4 : a * b * c ≤ 4 / 3 * (a + b + c) := by
    linarith
  have h5 : a * b * c / (a + b + c) ≤ 4 / 3 := by
    have h_pos : 0 < a + b + c := h1
    have h_ineq : a * b * c ≤ 4 / 3 * (a + b + c) := h4
    have h_eq : (a * b * c / (a + b + c)) ≤ (4 / 3 * (a + b + c) / (a + b + c)) := by
      apply (div_le_div_right (by linarith)).mpr
      linarith
    have h_eq2 : (4 / 3 * (a + b + c) / (a + b + c)) = (4 / 3) := by
      field_simp [(show a + b + c ≠ 0 by linarith)]
      <;> linarith
    linarith [h_eq, h_eq2, h_ineq, h_pos]
  linarith [h5]
  all_goals linarith [h5, h1]