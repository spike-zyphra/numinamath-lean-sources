import Mathlib

theorem algebra_214981 (θ : ℝ) (x : ℝ) (hx : x = Real.cos θ) :
    Real.cos (3 * θ) = 4 * x^3 - 3 * x := by
  have h1 : Real.cos (3 * θ) = 4 * (Real.cos θ) ^ 3 - 3 * (Real.cos θ) := by
    rw [Real.cos_three_mul]
  rw [h1]
  rw [show Real.cos θ = x by linarith [hx]]
  all_goals
    ring