import Mathlib

theorem algebra_2184
    (a : ℝ)
    (h : ¬(1 + (1 + 3 * a) / (2 * a) ≠ 0)) :
    a = -1 / 5 ∨ a = 0 := by
  have h1 : 1 + (1 + 3 * a) / (2 * a) = 0 := by
    simpa using h
  by_cases h2 : a = 0
  · -- Case where a = 0
    right
    exact h2
  · -- Case where a ≠ 0
    have h3 : 2 * a ≠ 0 := by
      intro h4
      apply h2
      linarith
    have eq1 : (1 + (1 + 3 * a) / (2 * a)) = (5 * a + 1) / (2 * a) := by
      field_simp [h3]
      ring
    rw [eq1] at h1
    have h4 : 5 * a + 1 = 0 := by
      have h5 : (5 * a + 1) / (2 * a) = 0 := h1
      have : 5 * a + 1 = 0 := by
        field_simp [h3] at h5 ⊢
        all_goals linarith
      assumption
    have ha : a = -1 / 5 := by linarith
    left
    exact ha