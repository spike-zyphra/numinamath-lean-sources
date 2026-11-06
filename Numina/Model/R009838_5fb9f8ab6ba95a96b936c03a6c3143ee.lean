import Mathlib

theorem algebra_11644 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 + 11 * x - 5) :
  IsMinOn f univ (-11/2) := by
  unfold IsMinOn
  intro x hx
  have h1 : f (-11 / 2) = (-11 / 2) ^ 2 + 11 * (-11 / 2) - 5 := by
    rw [hf]
  have h2 : f (-11 / 2) = -141 / 4 := by
    rw [h1]
    norm_num
  have h3 : f x = x ^ 2 + 11 * x - 5 := by
    rw [hf]
  have h4 : f (-11 / 2) ≤ f x := by
    rw [h2, h3]
    nlinarith [sq_nonneg (x + 11 / 2)]
  exact h4