import Mathlib

theorem algebra_243175 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2) :
    ∀ x, ∃ y, f x = y ^ 2 - 4 * y + 2 := by
  intro x
  use 2 + Real.sqrt (2 + x ^ 2)
  have h1 : f x = x ^ 2 := by simp [hf]
  rw [h1]
  have h2 : (2 + Real.sqrt (2 + x ^ 2)) ^ 2 - 4 * (2 + Real.sqrt (2 + x ^ 2)) + 2 = x ^ 2 := by
    have h3 : Real.sqrt (2 + x ^ 2) ^ 2 = 2 + x ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [h3]
  linarith [h2]