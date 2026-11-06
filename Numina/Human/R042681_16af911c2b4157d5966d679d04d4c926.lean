import Mathlib

theorem algebra_302763 {k : ℝ} (h : ∃ x1 x2, x1 ≠ x2 ∧ 8*x1^2 + 2*k*x1 + k - 1 = 0 ∧ 8*x2^2 + 2*k*x2 + k - 1 = 0 ∧ x1^2 + x2^2 = 1) :
    k = -2 := by
  obtain ⟨x1, x2, hx12, h1, h2, h3⟩ := h
  have h4 : k = -4 * (x1 + x2) := by
    apply (mul_left_inj' (sub_ne_zero_of_ne hx12)).mp
    linarith
  rw [h4]; simp
  nlinarith [sq_nonneg (x1 - x2)]
