import Mathlib

theorem calculus_136821 (f : ℝ → ℝ) (hf : f = fun x => 2 * x ^ 2 - 3 * x + 1) (x₀ : ℝ) (hx₀ : x₀ = 1) :
    deriv (fun x => -x + 1) x₀ = -1 / deriv f x₀ := by
  rw [hx₀]
  simp [hf, deriv_const, deriv_add, deriv_sub, deriv_pow, deriv_mul, mul_comm]
  all_goals norm_num