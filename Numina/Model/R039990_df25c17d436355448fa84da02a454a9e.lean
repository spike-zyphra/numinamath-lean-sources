import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_107368 {f : ℝ → ℝ}
  (hf : f = λ x => sin x * sin (x - π / 4) / (exp (2 * x) + sin x ^ 2)) :
  ∃ F, Differentiable ℝ F ∧ ∀ x, F x = (sqrt 2 / 2) * x - (sqrt 2 / 4) * log (exp (2 * x) + sin x ^ 2) ∧ F 0 = 0 := by

  use λ x => (sqrt 2 / 2) * x - (sqrt 2 / 4) * log (exp (2 * x) + sin x ^ 2)
  constructor
  · -- Show F is differentiable
    apply Differentiable.sub
    · -- Show (sqrt 2 / 2) * x is differentiable
      apply Differentiable.mul
      · -- Show (sqrt 2 / 2) is differentiable
        simp
      · -- Show (fun x => x) is differentiable
        exact differentiable_id'
    · -- Show (sqrt 2 / 4) * log (exp (2 * x) + sin x ^ 2) is differentiable
      apply Differentiable.mul
      · -- Show (sqrt 2 / 4) is differentiable
        simp
      · -- Show log (exp (2 * x) + sin x ^ 2) is differentiable
        apply Differentiable.log
        apply Differentiable.add
        · -- Show exp (2 * x) is differentiable
          apply Differentiable.exp
          apply Differentiable.mul
          · -- Show (2 : ℝ) is differentiable
            simp
          · -- Show (fun x => x) is differentiable
            exact differentiable_id'
        · -- Show sin x ^ 2 is differentiable
          apply Differentiable.pow
          exact differentiable_sin
        all_goals
          intro x
          positivity
  · -- Show F x = (sqrt 2 / 2) * x - (sqrt 2 / 4) * log (exp (2 * x) + sin x ^ 2) and F 0 = 0
    intro x
    constructor
    · -- Show F x = (sqrt 2 / 2) * x - (sqrt 2 / 4) * log (exp (2 * x) + sin x ^ 2)
      rfl
    · -- Show F 0 = 0
      simp