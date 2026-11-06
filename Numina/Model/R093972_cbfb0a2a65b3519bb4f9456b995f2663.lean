import Mathlib

theorem inequalities_139652 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a < 1) (h2 : b < 1) (h3 : c < 1) :
    a * (1 - b) ≤ 1 / 4 ∨ b * (1 - c) ≤ 1 / 4 ∨ c * (1 - a) ≤ 1 / 4 := by
  by_contra h
  push_neg at h
  nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2),
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
    mul_pos (sub_pos.mpr h1) (sub_pos.mpr hb),
    mul_pos (sub_pos.mpr h2) (sub_pos.mpr hc),
    mul_pos (sub_pos.mpr h3) (sub_pos.mpr ha)]