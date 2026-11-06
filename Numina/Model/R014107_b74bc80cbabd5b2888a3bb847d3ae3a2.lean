import Mathlib

theorem inequalities_88324 (a b c : ℝ) (ha : 0 < a ∧ a ≤ 1) (hb : 0 < b ∧ b ≤ 1) (hc : 0 < c ∧ c ≤ 1) :
    a^2 * b + b^2 * c + c^2 * a + 1 ≥ a^2 + b^2 + c^2 := by
  rcases ha with ⟨ha_pos, ha_le⟩
  rcases hb with ⟨hb_pos, hb_le⟩
  rcases hc with ⟨hc_pos, hc_le⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr ha_le) (sub_nonneg.mpr hb_le),
            mul_nonneg (sub_nonneg.mpr hb_le) (sub_nonneg.mpr hc_le),
            mul_nonneg (sub_nonneg.mpr ha_le) (sub_nonneg.mpr hc_le),
            mul_pos ha_pos hb_pos, mul_pos hb_pos hc_pos, mul_pos ha_pos hc_pos,
            mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith),
            mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ c by linarith),
            mul_nonneg (show (0 : ℝ) ≤ c by linarith) (show (0 : ℝ) ≤ a by linarith)]