import Mathlib

theorem algebra_22122 {A B C D : ℝ} (h : ∀ x, (x^3 + 3 * x^2 - 12 * x + 36) / (x^4 - 16) =
    A / (x - 2) + B / (x + 2) + (C * x + D) / (x^2 + 4)) :
    A = 1 ∧ B = -2 ∧ C = 2 ∧ D = -3 := by

  have eqn1 := h 0
  have eqn2 := h 1
  have eqn3 := h 3
  have eqn4 := h (-1 : ℝ)
  have eqn5 := h 4
  have eqn6 := h (-3 : ℝ)

  norm_num at eqn1 eqn2 eqn3 eqn4 eqn5 eqn6

  have eqn7 : A = 1 := by
    linarith

  have eqn8 : B = -2 := by
    linarith

  have eqn9 : C = 2 := by
    linarith

  have eqn10 : D = -3 := by
    linarith

  exact ⟨eqn7, eqn8, eqn9, eqn10⟩