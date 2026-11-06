import Mathlib

theorem algebra_95201 (blueberry raspberry grape cherry : ℕ)
(h₀ : blueberry + raspberry + grape + cherry = 280)
(h₁ : raspberry = 2 * blueberry)
(h₂ : grape = 3 * cherry)
(h₃ : cherry = 4 * raspberry) :
cherry = 64 := by
  omega