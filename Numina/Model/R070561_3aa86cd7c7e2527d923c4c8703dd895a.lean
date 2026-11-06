import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_111514 (f : ℝ → ℝ) (hf : f = λ x => 2*x^3 + 3*x^2 - 12*x + 1) :
    ∀ x ∈ Ioo (-2) 1, deriv f x < 0 := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  have h1 : deriv f x = 6 * x^2 + 6 * x - 12 := by
    rw [hf]
    simp [deriv_add, deriv_sub, deriv_pow, deriv_const, mul_comm]
    all_goals field_simp
    <;> ring_nf <;> norm_num
    all_goals norm_num
    <;> ring_nf <;> norm_num
  rw [h1]
  nlinarith [sq_nonneg (x + 0.5), sq_nonneg (x + 2), sq_nonneg (x - 1)]
  all_goals norm_num
  all_goals nlinarith
  <;> linarith