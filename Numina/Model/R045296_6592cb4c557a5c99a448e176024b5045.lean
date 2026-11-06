import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_312286 {a b c : ℝ} (h₀ : a^2 + b^2 = 1) (h₁ : b^2 + c^2 = 2)
  (h₂ : c^2 + a^2 = 2) :
  a * b + b * c + a * c ≥ 1 / 2 - sqrt 3 := by
  have h3 : a^2 + b^2 + c^2 = 5 / 2 := by
    nlinarith
  have ha2 : a^2 = 1 / 2 := by
    nlinarith
  have hb2 : b^2 = 1 / 2 := by
    nlinarith
  have hc2 : c^2 = 3 / 2 := by
    nlinarith
  nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]