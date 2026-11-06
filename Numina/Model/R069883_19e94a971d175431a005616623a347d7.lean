import Mathlib

theorem inequalities_300060 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a < 1) (h2 : b < 1) (h3 : c < 1) :
    ¬(1/4 < (1 - a) * b ∧ 1/4 < (1 - b) * c ∧ 1/4 < (1 - c) * a) := by
  intro h
  rcases h with ⟨h12, h23, h31⟩

  nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2),
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
    mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2),
    mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3),
    mul_pos (sub_pos.mpr h3) (sub_pos.mpr h1)]