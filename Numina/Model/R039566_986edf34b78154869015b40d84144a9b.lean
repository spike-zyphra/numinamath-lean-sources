import Mathlib

theorem inequalities_285950
    (a b : ℝ)
    (h₀ : 0 < a ∧ a < 1)
    (h₁ : 0 < b ∧ b < 1) :
    0 < a + b - a * b ∧ a + b - a * b < 1 := by
  have ha1 : 0 < a := h₀.1
  have ha2 : a < 1 := h₀.2
  have hb1 : 0 < b := h₁.1
  have hb2 : b < 1 := h₁.2
  constructor
  · -- Prove 0 < a + b - a * b
    nlinarith [mul_pos ha1 hb1, mul_pos (sub_pos.mpr ha2) (sub_pos.mpr hb2), mul_self_nonneg (a - 1), mul_self_nonneg (b - 1)]
  · -- Prove a + b - a * b < 1
    nlinarith [mul_pos ha1 hb1, mul_pos (sub_pos.mpr ha2) (sub_pos.mpr hb2), mul_self_nonneg (a - 1), mul_self_nonneg (b - 1)]