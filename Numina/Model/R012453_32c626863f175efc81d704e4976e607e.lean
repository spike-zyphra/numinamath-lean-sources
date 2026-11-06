import Mathlib

open Real

theorem calculus_139944 {f : ℝ → ℝ}
    (hf : ∀ x, f x = (1 + x) * (2 + x^2) ^ ((1 : ℝ) / 2) * (3 + x^3) ^ ((1 : ℝ) / 3)) :
    deriv f (-1) = 3 ^ ((1 : ℝ) / 2) * 2 ^ ((1 : ℝ) / 3) := by
  have eq1 : f = fun x => (1 + x) * (2 + x^2) ^ ((1 : ℝ) / 2) * (3 + x^3) ^ ((1 : ℝ) / 3) := by
    funext x
    exact hf x
  rw [eq1]
  simp [deriv_mul, deriv_add, deriv_pow, deriv_id'', mul_comm]
  all_goals
    norm_num
    <;> ring_nf
    <;> norm_num
    <;> ring_nf
    <;> norm_num