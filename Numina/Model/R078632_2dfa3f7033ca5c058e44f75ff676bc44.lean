import Mathlib

theorem algebra_309027 {α : ℝ} (hα : α^3 + 3 * α - 1 = 0) :
    ¬∃ x y, x > 0 ∧ y < 0 ∧ y = α * x + 1 - α := by

  intro h
  rcases h with ⟨x, y, hx, hy, h_eq⟩

  have h2 : α > 0 := by
    nlinarith [sq_nonneg (α ^ 2), sq_nonneg (α - 1), sq_nonneg (α + 1), sq_nonneg (α)]
  have h4 : α < 1 := by 
    nlinarith [sq_nonneg (α ^ 2), sq_nonneg (α - 1), sq_nonneg (α + 1), sq_nonneg (α)]
  have h6 : 1 - α > 0 := by
    linarith
  have h5 : α * x > 0 := mul_pos h2 hx

  have h9 : α * x + (1 - α) ≥ 0 := by
    nlinarith [sq_nonneg (x * α - α), sq_nonneg (x - 1), sq_nonneg (α ^ 2), sq_nonneg (α - 1), sq_nonneg (α + 1), sq_nonneg (α), hα]

  have h8 : y ≥ 0 := by
    nlinarith [h_eq, h9]

  linarith