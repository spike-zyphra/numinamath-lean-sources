import Mathlib

theorem inequalities_57095 (a b c : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (h1 : a * (1 - b) > 1 / 4) (h2 : b * (1 - c) > 1 / 4) (h3 : c * (1 - a) > 1 / 4) :
    False := by
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  rcases hc with ⟨hc0, hc1⟩
  nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2), 
          mul_pos ha0 hb0, mul_pos hb0 hc0, mul_pos ha0 hc0,
          mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hb1), 
          mul_pos (sub_pos.mpr hb1) (sub_pos.mpr hc1), 
          mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hc1)]