import Mathlib

theorem calculus_156608 (v : ℝ → ℝ) (h : v = fun t => 3 * t ^ 2 - 1) :
    ∃ s : ℝ → ℝ, Differentiable ℝ s ∧ ∀ t, deriv s t = v t ∧ s 0 = 5 / 100 := by
  use fun t => t ^ 3 - t + 5 / 100
  constructor
  · -- Show differentiable
    apply Differentiable.add
    · -- Differentiable.add
      apply Differentiable.add
      · -- Differentiable.pow
        apply Differentiable.pow
        exact differentiable_id'
      · -- Differentiable.neg
        apply Differentiable.neg
        exact differentiable_id'
    · -- Differentiable.const
      exact differentiable_const (5 / 100 : ℝ)
  intro t
  constructor
  · -- Show that the derivative of s is v
    rw [h]
    simp [deriv_add, deriv_sub, deriv_pow, deriv_neg, deriv_id'', mul_comm]
    <;> field_simp
    <;> ring
  · -- Show that s 0 = 5 / 100
    norm_num