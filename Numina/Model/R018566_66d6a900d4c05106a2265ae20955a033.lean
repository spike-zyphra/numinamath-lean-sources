import Mathlib

theorem algebra_248720 (x y : ℝ) (h₁ : |y| ≤ 2 - x) (h₂ : x ≥ -1) :
    2 * x + y ≥ -5 := by
  cases' abs_le.mp h₁ with h₃ h₄
  linarith