import Mathlib

theorem algebra_317637 {A B C : ℝ} (hA : A ≠ 0) (α β : ℝ)
    (h₁ : A * α ^ 2 + B * α + C = α) (h₂ : A * β ^ 2 + B * β + C = β) :
    A * (A * α ^ 2 + B * α + C) ^ 2 + B * (A * α ^ 2 + B * α + C) +
    C = α ∧ A * (A * β ^ 2 + B * β + C) ^ 2 + B * (A * β ^ 2 + B * β + C) +
    C = β := by
  constructor
  · -- First part: prove the result for α
    have eq1 : A * (A * α ^ 2 + B * α + C) ^ 2 + B * (A * α ^ 2 + B * α + C) + C = α := by
      rw [show A * α ^ 2 + B * α + C = α by linarith]
      nlinarith
    linarith [eq1]
  · -- Second part: prove the result for β
    have eq2 : A * (A * β ^ 2 + B * β + C) ^ 2 + B * (A * β ^ 2 + B * β + C) + C = β := by
      rw [show A * β ^ 2 + B * β + C = β by linarith]
      nlinarith
    linarith [eq2]