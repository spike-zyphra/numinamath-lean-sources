import Mathlib

theorem calculus_141605 (C : ℝ) (y : ℝ → ℝ) (hy : y = fun x => C * x) :
    ∀ x, x * deriv y x - y x = 0 := by
  intro x
  have h1 : deriv y x = C := by
    rw [hy]
    simp [deriv_const_mul, deriv_id', mul_comm C, mul_assoc]
    all_goals ring_nf <;> simp [mul_comm C]
    all_goals ring
  rw [h1]
  rw [hy]
  simp [mul_comm C]
  all_goals ring
  all_goals linarith [mul_comm C x]