import Mathlib

open Real

theorem calculus_139698 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = -1/2 * exp (-x^2) * (x^4 + 2 * x^2 + 2)) :
    ∀ x, deriv f x = x^5 * exp (-x^2) := by 
  intro x
  rw [funext h₀]
  simp [deriv_mul, deriv_id'', mul_comm]
  all_goals 
    field_simp 
    <;> ring_nf 
    <;> field_simp [exp_pow] 
    <;> ring