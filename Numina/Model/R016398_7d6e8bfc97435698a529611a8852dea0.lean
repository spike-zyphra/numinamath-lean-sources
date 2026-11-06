import Mathlib

theorem calculus_156314 (f : ℝ → ℝ) (hf : f = fun x => x ^ 6) :
    ∃ F, Differentiable ℝ F ∧ ∀ x, deriv F x = f x := by
  use fun x => (1 / 7) * x ^ 7
  constructor
  · -- Differentiable
    apply Differentiable.mul
    · -- Show `x ↦ (1 / 7)` is differentiable, which is a constant
      exact differentiable_const (1 / 7)
    · -- Show `x ↦ x ^ 7` is differentiable
      apply Differentiable.pow
      exact differentiable_id'
  · -- deriv F x = f x
    intro x
    simp [hf]
    all_goals
      simp [deriv_pow, deriv_const, mul_comm]
      all_goals
        ring_nf