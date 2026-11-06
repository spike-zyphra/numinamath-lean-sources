import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

theorem inequalities_5353
  (a b c d : ℝ)
  (h₀ : 0 < a)
  (h₁ : 0 < b)
  (h₂ : 0 < c)
  (h₃ : 0 < d) :
  -a + b + c - d ≥ 0 ∨ a * c - b * c + b * d ≥ 0 := by
  by_cases h : -a + b + c - d ≥ 0
  · -- Case where -a + b + c - d ≥ 0.
    left
    linarith
  · -- Case where -a + b + c - d < 0.
    have h1 : -a + b + c - d < 0 := by linarith
    have h2 : b + c < a + d := by linarith
    have h3 : a * c - b * c + b * d ≥ 0 := by
      nlinarith [sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (d - c), mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₀ h₃, mul_pos h₁ h₂, mul_pos h₁ h₃, mul_pos h₂ h₃]
    right
    linarith