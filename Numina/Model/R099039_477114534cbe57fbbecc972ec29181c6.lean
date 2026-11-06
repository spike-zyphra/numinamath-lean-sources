import Mathlib

theorem algebra_228663 (a : ℝ) (ha : 0 < a) (x₁ x₂ : ℝ) (hx₁ : x₁ > x₂) :
    (a > 1 → a ^ x₁ > a ^ x₂) ∧ (a < 1 → a ^ x₁ < a ^ x₂) := by
  constructor
  · -- Proof of the first implication: If a > 1 and x₁ > x₂, then a ^ x₁ > a ^ x₂
    intro ha1
    apply Real.rpow_lt_rpow_of_exponent_lt
    all_goals linarith
  · -- Proof of the second implication: If a < 1 and x₁ > x₂, then a ^ x₁ < a ^ x₂
    intro ha2
    apply Real.rpow_lt_rpow_of_exponent_gt
    all_goals linarith