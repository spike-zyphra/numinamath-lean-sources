import Mathlib

theorem algebra_274034 (a b c : ℝ)
    (h₀ : a^2 + b^2 - 4 * a ≤ 1)
    (h₁ : b^2 + c^2 - 8 * b ≤ -3)
    (h₂ : c^2 + a^2 - 12 * c ≤ -26) :
    (a + b)^c = 27 := by

  have h3 : (a - 1)^2 + (b - 2)^2 + (c - 3)^2 ≤ 0 := by
    nlinarith

  have ha1 : (a - 1)^2 = 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (c - 3)]

  have hb1 : (b - 2)^2 = 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (c - 3)]

  have hc1 : (c - 3)^2 = 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (c - 3)]

  have ha2 : a = 1 := by
    nlinarith

  have hb2 : b = 2 := by
    nlinarith

  have hc2 : c = 3 := by
    nlinarith

  rw [ha2, hb2, hc2]
  norm_num