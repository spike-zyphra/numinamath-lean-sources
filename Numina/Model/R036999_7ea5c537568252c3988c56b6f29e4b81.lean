import Mathlib

theorem inequalities_222679 (a b c : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1)
    (h1 : a * (1 - b) > 1 / 4) (h2 : b * (1 - c) > 1 / 4) (h3 : c * (1 - a) > 1 / 4) :
    False := by
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  rcases hc with ⟨hc0, hc1⟩
  nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2),
    mul_nonneg (sub_nonneg.mpr ha0) (sub_nonneg.mpr hb1),
    mul_nonneg (sub_nonneg.mpr hb0) (sub_nonneg.mpr hc1),
    mul_nonneg (sub_nonneg.mpr hc0) (sub_nonneg.mpr ha1),
    mul_nonneg (sub_nonneg.mpr ha0) (sub_nonneg.mpr hc1),
    mul_nonneg (sub_nonneg.mpr hb0) (sub_nonneg.mpr ha1),
    mul_nonneg (sub_nonneg.mpr hc0) (sub_nonneg.mpr hb1)]