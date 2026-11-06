import Mathlib

theorem algebra_228983 (a b c d : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : 1 / a + 1 / b = 1 / 8)
    (h₂ : 1 / b + 1 / c = 1 / 6)
    (h₃ : 1 / c + 1 / d = 1 / 12) :
    1 / a + 1 / d = 1 / 24 := by
  have ha : 0 < a := h₀.1
  have hb : 0 < b := h₀.2.1
  have hc : 0 < c := h₀.2.2.1
  have hd : 0 < d := h₀.2.2.2
  have ha_eq : 1 / a = 1 / 8 - 1 / b := by linarith
  have h4 : 1 / c = 1 / 6 - 1 / b := by linarith [h₁, h₂]
  have hd_eq : 1 / d = 1 / b - 1 / 12 := by
    linarith [h₃, h4]
  linarith [ha_eq, hd_eq]