import Mathlib

open Real

theorem calculus_141225 (f : ℝ → ℝ → ℝ) (hf : f = fun x y => x^2 + x * y)
    (x y : ℝ) (hx : x = 2) (hy : y = 1) (Δx Δy : ℝ) (hΔx : Δx = 0.01) (hΔy : Δy = 0.02) :
    deriv (fun x => f x y) x * Δx + deriv (fun y => f x y) y * Δy = 0.09 ∧
    f (x + Δx) (y + Δy) - f x y = 0.0903 := by
  rw [hf]
  rw [hx, hy, hΔx, hΔy]
  simp [deriv_add, deriv_pow, deriv_mul, deriv_id'', mul_comm]
  all_goals norm_num [deriv_pow, deriv_const_mul, deriv_id'', mul_comm]
  all_goals norm_num