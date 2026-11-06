import Mathlib

theorem algebra_296977 {b : ℝ} (h : ∃ x, 1988*x^2+b*x+8891=0 ∧ 8891*x^2+b*x+1988=0) :
    b=10879 ∨ b=-10879 := by

  rcases h with ⟨x, h₁, h₂⟩

  -- Subtract the two equations to eliminate b*x
  have h_subtract : 6903 * x^2 - 6903 = 0 := by
    nlinarith

  -- Simplify to x^2 - 1 = 0
  have h_x_sq : x^2 - 1 = 0 := by
    linarith

  -- Thus x^2 = 1, therefore x is either 1 or -1
  have h_x_val : x = 1 ∨ x = -1 := by
    have : x^2 = 1 := by linarith
    have : x = 1 ∨ x = -1 := by
      rw [sq_eq_one_iff] at this
      exact this
    exact this

  rcases h_x_val with (h1 | h2)

  · -- Case where x = 1
    have h_b : b = -10879 := by
      rw [h1] at h₁
      linarith
    right
    linarith

  · -- Case where x = -1
    have h_b : b = 10879 := by
      rw [h2] at h₁
      linarith
    left
    linarith