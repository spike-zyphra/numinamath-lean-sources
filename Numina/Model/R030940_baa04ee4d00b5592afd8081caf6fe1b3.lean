import Mathlib

theorem algebra_21406 {a b c : ℝ} (h₀ : 6*a=5*b) (h₁ : 3*b=11*c) :
    36*a=110*c := by
  have h2 : 18 * a = 55 * c := by
    linarith [h₀, h₁]
  linarith [h2]