import Mathlib

theorem algebra_113222 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h₀ : a / b = 5 / 4) (h₁ : (1 + 20 / 100) * a * 3 = b * 4) :
    (3 - (1 + 20 / 100) * a * 3 / b) * 60 = 52 := by
  have h2 : a = 5 / 4 * b := by
    have hne : b ≠ 0 := by linarith
    field_simp [hne] at h₀
    linarith
  have h3 : a = 10 / 9 * b := by
    nlinarith
  have h4 : b = 0 := by
    nlinarith [h2, h3]
  linarith [hb, h4]