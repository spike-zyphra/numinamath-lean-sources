import Mathlib

theorem algebra_896 {a b : ℝ} (h : ∀ x : ℝ, (3 * a + 8 * b) * x + 7 ≠ 0) :
    a * b ≤ 0 := by
  have h1 : 3 * a + 8 * b = 0 := by
    by_contra h2
    have h3 : ∃ x : ℝ, (3 * a + 8 * b) * x + 7 = 0 := by
      use -7 / (3 * a + 8 * b)
      field_simp [h2]
      <;> linarith
    obtain ⟨x, hx⟩ := h3
    specialize h x
    contradiction

  have h2 : b = -3 / 8 * a := by
    linarith

  rw [h2]
  have h3 : a * (-3 / 8 * a) ≤ 0 := by
    have h4 : a ^ 2 ≥ 0 := by
      exact sq_nonneg a
    linarith [h4]
  linarith