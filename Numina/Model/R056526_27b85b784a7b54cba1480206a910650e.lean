import Mathlib

theorem algebra_8101 {a b : ℝ} (h₀ : a * b + 5 = 0) (h₁ : a - b = 5) : ¬ (a + b = 5) ∧ ¬ (a + b = 0) ∧ ¬ (a + b = 2) := by
  have h2 : a = b + 5 := by linarith
  rw [h2] at h₀
  have h3 : b^2 + 5 * b + 5 = 0 := by
    nlinarith
  have h4 : ¬ (a + b = 5) := by
    intro h
    have h5 : a + b = 5 := h
    rw [h2] at h5
    have hb : b = 0 := by
      nlinarith
    rw [hb] at h3
    nlinarith
  have h5 : ¬ (a + b = 0) := by
    intro h
    have h6 : a + b = 0 := h
    rw [h2] at h6
    have hb : b = -5 / 2 := by
      nlinarith
    rw [hb] at h3
    nlinarith
  have h6 : ¬ (a + b = 2) := by
    intro h
    have h7 : a + b = 2 := h
    rw [h2] at h7
    have hb : b = -3 / 2 := by
      nlinarith
    rw [hb] at h3
    nlinarith
  exact ⟨h4, h5, h6⟩