import Mathlib

theorem calculus_165753 (C1 C2 : ℝ) (y : ℝ → ℝ) (hy : y = fun x => C1 * x + C2) :
    ∀ x, iteratedDeriv 2 y x = 0 := by
  intro x 
  rw [hy]
  simp [iteratedDeriv_succ, deriv_add, deriv_mul, deriv_id'', mul_comm C1, mul_assoc]