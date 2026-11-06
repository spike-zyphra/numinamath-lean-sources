import Mathlib

open Real
open scoped BigOperators

theorem inequalities_132330 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
  (h₃ : a^2 + b^2 = c^2) :
  a^4 + b^4 < c^4 := by
  have h4 : a^4 + b^4 = (a^2 + b^2)^2 - 2 * (a^2 * b^2) := by
    nlinarith [sq_nonneg (a^2 - b^2)]
  rw [h₃] at h4
  have h5 : 2 * (a^2 * b^2) > 0 := by
    have ha2 : a^2 > 0 := by nlinarith [h₀]
    have hb2 : b^2 > 0 := by nlinarith [h₁]
    have h6 : a^2 * b^2 > 0 := mul_pos ha2 hb2
    linarith [h6]
  linarith [h4, h5]