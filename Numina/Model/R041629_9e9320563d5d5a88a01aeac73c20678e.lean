import Mathlib

theorem algebra_178593 {x y : ℝ} (h₀ : abs (x - 3) = 5 - y) (h₁ : abs (y - 5) + abs (x - 3) = x + y) :
    (x = 1 ∧ y = 3) ∨ (x = 7 ∧ y = 1) := by
  have h2 : y ≤ 5 := by
    linarith [abs_nonneg (x - 3), h₀]
  have h3 : abs (y - 5) = 5 - y := by
    rw [abs_of_nonpos]
    all_goals linarith
  have eq1 : (5 - y) + abs (x - 3) = x + y := by
    rw [h3] at h₁
    linarith
  have eq3 : x + 3 * y = 10 := by
    have eq2 : (5 - y) + (5 - y) = x + y := by
      linarith [h₀, eq1]
    linarith
  by_cases h4 : x ≥ 3
  · -- Case x ≥ 3.
    have hx1 : abs (x - 3) = x - 3 := by
      rw [abs_of_nonneg]
      linarith
    rw [hx1] at h₀
    have eq4 : x + y = 8 := by
      linarith
    have hy1 : y = 1 := by
      linarith [eq3, eq4]
    have hx7 : x = 7 := by
      linarith [eq4, hy1]
    right
    exact ⟨hx7, hy1⟩
  · -- Case x < 3.
    have hx1 : abs (x - 3) = 3 - x := by
      rw [abs_of_neg]
      linarith
      all_goals linarith
    rw [hx1] at h₀
    have eq4 : y - x = 2 := by
      linarith
    have hx1 : x = 1 := by
      have eq5 : y = x + 2 := by
        linarith [eq4]
      rw [eq5] at eq3
      linarith
    have hy3 : y = 3 := by
      linarith [hx1, eq4]
    left
    exact ⟨hx1, hy3⟩