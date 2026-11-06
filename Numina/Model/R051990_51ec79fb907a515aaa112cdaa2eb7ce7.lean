import Mathlib

theorem algebra_290760 {p q r : ℝ} (h₀ : p + q + r = 70) (h₁ : p = 2 * q) (h₂ : q = 3 * r) :
    p = 42 := by
  have hp : p = 6 * r := by
    linarith [h₁, h₂]
  have hr : r = 7 := by 
    linarith [h₀, hp, h₂]
  linarith [hr, hp]