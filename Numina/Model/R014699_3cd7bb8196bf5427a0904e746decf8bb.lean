import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_278730 (x y z : ℝ) (h₀ : 0 ≤ x) (h₁ : 0 ≤ y) (h₂ : 0 ≤ z)
  (h₃ : x + y + z = 1) :
  -1/8 ≤ (z - x)*(z - y) ∧ (z - x)*(z - y) ≤ 1 := by 
  constructor
  · -- Prove the lower bound
    nlinarith [sq_nonneg (x - y), sq_nonneg (z - (1 / 4)), sq_nonneg (x + y - z), mul_nonneg h₀ h₁, mul_nonneg h₀ h₂, mul_nonneg h₁ h₂]
  · -- Prove the upper bound
    nlinarith [sq_nonneg (z - 1), sq_nonneg (x - y), mul_nonneg h₀ h₁, mul_nonneg h₀ h₂, mul_nonneg h₁ h₂]