import Mathlib

theorem algebra_286529 (p q : ℝ) (h : ∃ x1 x2, x1^2 + x2^2 = 1 ∧ x1 + x2 = p ∧ x1 * x2 = q) :
    p^2 - 2 * q = 1 := by
  rcases h with ⟨x1, x2, h1, h2, h3⟩
  have h4 : x1^2 + x2^2 = (x1 + x2)^2 - 2 * (x1 * x2) := by
    ring
  rw [h2, h3] at h4
  linarith [h1, h4]