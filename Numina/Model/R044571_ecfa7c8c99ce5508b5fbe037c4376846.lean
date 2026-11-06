import Mathlib

theorem algebra_155463 (f : ℝ → ℝ) (hf : f = fun x => 2 * x ^ 3 - 4 * x + 2) :
    ∀ x, deriv f x = 6 * x ^ 2 - 4 := by
  intro x
  rw [hf]
  simp [deriv_const, deriv_sub, deriv_add, deriv_pow, deriv_mul, mul_comm]
  all_goals
    field_simp
    <;> ring