import Mathlib

theorem inequalities_233463 (a b c : ℝ) (ha : 0 < a) (hb : a ≤ b) (hc : b ≤ c) :
    (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c ∧
    ((a + 3 * b) * (b + 4 * c) * (c + 2 * a) = 60 * a * b * c ↔ a = b ∧ b = c) := by
  have h1 : (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
      mul_nonneg (show 0 ≤ b - a by linarith) (show 0 ≤ c - b by linarith),
      mul_nonneg (show 0 ≤ b - a by linarith) (show 0 ≤ c - a by linarith),
      mul_nonneg (show 0 ≤ c - b by linarith) (show 0 ≤ c - a by linarith),
      mul_pos ha (show 0 < b by nlinarith),
      mul_pos ha (show 0 < c by nlinarith),
      mul_pos (show 0 < b by nlinarith) (show 0 < c by nlinarith),
      mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hc)]
  constructor
  · exact h1
  · -- Assume equality holds, prove a = b ∧ b = c
    constructor
    · -- Forward implication: equality implies a = b ∧ b = c
      intro heq
      have h_eq1 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
          mul_nonneg (show 0 ≤ b - a by linarith) (show 0 ≤ c - b by linarith),
          mul_nonneg (show 0 ≤ b - a by linarith) (show 0 ≤ c - a by linarith),
          mul_nonneg (show 0 ≤ c - b by linarith) (show 0 ≤ c - a by linarith),
          mul_pos ha (show 0 < b by nlinarith),
          mul_pos ha (show 0 < c by nlinarith),
          mul_pos (show 0 < b by nlinarith) (show 0 < c by nlinarith),
          mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hc)]
      have ha1 : a - b = 0 := by
        nlinarith [h_eq1]
      have hb1 : a = b := by
        linarith
      have h_eq2 : (b - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
          mul_nonneg (show 0 ≤ b - a by linarith) (show 0 ≤ c - b by linarith),
          mul_nonneg (show 0 ≤ b - a by linarith) (show 0 ≤ c - a by linarith),
          mul_nonneg (show 0 ≤ c - b by linarith) (show 0 ≤ c - a by linarith),
          mul_pos ha (show 0 < b by nlinarith),
          mul_pos ha (show 0 < c by nlinarith),
          mul_pos (show 0 < b by nlinarith) (show 0 < c by nlinarith),
          mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hc)]
      have hc1 : b - c = 0 := by
        nlinarith [h_eq2]
      have hb2 : b = c := by
        linarith
      exact ⟨hb1, hb2⟩
    · -- Backward implication: a = b ∧ b = c implies equality
      rintro ⟨rfl, rfl⟩
      nlinarith [sq_nonneg (a - a), sq_nonneg (a - a), sq_nonneg (a - a),
        mul_nonneg (show 0 ≤ a - a by linarith) (show 0 ≤ a - a by linarith),
        mul_nonneg (show 0 ≤ a - a by linarith) (show 0 ≤ a - a by linarith),
        mul_nonneg (show 0 ≤ a - a by linarith) (show 0 ≤ a - a by linarith),
        mul_pos ha (show 0 < a by linarith),
        mul_pos ha (show 0 < a by linarith),
        mul_pos (show 0 < a by linarith) (show 0 < a by linarith),
        mul_nonneg (sub_nonneg.mpr (show a ≤ a by linarith)) (sub_nonneg.mpr (show a ≤ a by linarith))]