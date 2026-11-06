import Mathlib

theorem algebra_10388 (f : ℝ → ℝ) (hf : f = fun x => -x^2 - 6 * x + 12) :
  IsMaxOn f univ (-3) := by
  unfold IsMaxOn
  intro x hx
  simp [hf]
  nlinarith [sq_nonneg (x + 3)]