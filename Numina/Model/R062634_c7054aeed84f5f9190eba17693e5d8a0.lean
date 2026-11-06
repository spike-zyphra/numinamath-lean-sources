import Mathlib

theorem algebra_112769 (x y : ℝ) (h₀ : x^2 + y^2 = 1) (h₁ : (1 / 4) * x + (1 / 9) * y = 1) :
    (x = -1 / 2 ∧ y = 3 / 2) ∨ (x = 1 / 2 ∧ y = -3 / 2) := by
  have h2 : 9 * x + 4 * y = 36 := by 
    linarith [h₁]
  have h3 : y = (36 - 9 * x) / 4 := by
    linarith
  rw [h3] at h₀
  ring_nf at h₀
  nlinarith [sq_nonneg (x * 97 - 648 * 48 / 97), sq_nonneg (x - -1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg ((36 - 9 * x) / 4 - 3 / 2), sq_nonneg ((36 - 9 * x) / 4 + 3 / 2)]