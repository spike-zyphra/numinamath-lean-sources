import Mathlib

theorem calculus_141617 (C : ℝ) (y : ℝ → ℝ) (hy : y = fun x => x^2 + C) :
    Differentiable ℝ y ∧ ∀ x, deriv y x = 2 * x ∧ ((y 1 = 2) ↔ C = 1) := by

  have h1 : Differentiable ℝ y := by
    rw [hy]
    apply Differentiable.add
    · -- The function fun x ↦ x ^ 2 is differentiable
      apply Differentiable.pow
      exact differentiable_id'
    · -- The function fun x ↦ C is differentiable (constant function)
      exact differentiable_const C
  have h2 : ∀ x, deriv y x = 2 * x ∧ ((y 1 = 2) ↔ C = 1) := by
    intro x
    rw [hy]
    have deriv_eq : deriv (fun x => x ^ 2 + C) x = 2 * x := by 
      simp [deriv_add, deriv_pow, deriv_const]
    refine ⟨deriv_eq, ?_⟩
    simp
    constructor <;> intro h <;> linarith
  exact ⟨h1, h2⟩

