import Mathlib

theorem inequalities_232452 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    3 / 2 ≤ a ^ 3 / (a ^ 2 + 1) + b ^ 3 / (b ^ 2 + 1) +
    c ^ 3 / (c ^ 2 + 1) := by

  have h1 : 0 < a ^ 2 + 1 := by
    nlinarith
  have h2 : 0 < b ^ 2 + 1 := by
    nlinarith
  have h3 : 0 < c ^ 2 + 1 := by
    nlinarith

  have h4 : a ^ 3 / (a ^ 2 + 1) ≥ a - 1 / 2 := by
    have h1' : 0 < a ^ 2 + 1 := h1
    apply (le_div_iff₀ h1').mpr
    nlinarith [sq_nonneg (a - 1), sq_pos_of_pos ha]

  have h5 : b ^ 3 / (b ^ 2 + 1) ≥ b - 1 / 2 := by
    have h2' : 0 < b ^ 2 + 1 := h2
    apply (le_div_iff₀ h2').mpr
    nlinarith [sq_nonneg (b - 1), sq_pos_of_pos hb]

  have h6 : c ^ 3 / (c ^ 2 + 1) ≥ c - 1 / 2 := by
    have h3' : 0 < c ^ 2 + 1 := h3
    apply (le_div_iff₀ h3').mpr
    nlinarith [sq_nonneg (c - 1), sq_pos_of_pos hc]

  have h7 : a ^ 3 / (a ^ 2 + 1) + b ^ 3 / (b ^ 2 + 1) + c ^ 3 / (c ^ 2 + 1) ≥ (a - 1 / 2) + (b - 1 / 2) + (c - 1 / 2) := by
    linarith [h4, h5, h6]

  have h8 : (a - 1 / 2) + (b - 1 / 2) + (c - 1 / 2) = (a + b + c) - 3 / 2 := by
    ring

  have h9 : (a + b + c) - 3 / 2 = 3 / 2 := by
    linarith [h]

  have h10 : a ^ 3 / (a ^ 2 + 1) + b ^ 3 / (b ^ 2 + 1) + c ^ 3 / (c ^ 2 + 1) ≥ 3 / 2 := by
    linarith [h7, h8, h9]

  linarith [h10]