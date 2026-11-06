import Mathlib

theorem algebra_22032 (f : ℝ → ℝ) (hf : f = fun x => 9 * x ^ 2 + 18 * x + 7) :
    IsMinOn f (Set.univ : Set ℝ) (-1) := by
  unfold IsMinOn
  intro x hx
  simp [hf]
  have h1 : (x + 1) ^ 2 ≥ 0 := by apply sq_nonneg
  nlinarith [sq_nonneg (x + 1)]