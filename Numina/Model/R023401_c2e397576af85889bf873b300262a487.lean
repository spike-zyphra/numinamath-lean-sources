import Mathlib

theorem algebra_228395 (f : ℝ → ℝ) (m : ℝ) (h₀ : ∀ x, f x = (x - 5) / (2 * x + m))
    (h₁ : ∀ x, ∃ y, f x = y ∧ f y = x) :
    m = -1 := by
  have h2 := h₁ 5
  rcases h2 with ⟨y, hy1, hy2⟩
  have h3 : f 5 = y := by linarith
  have h4 : f 5 = (5 - 5) / (2 * (5 : ℝ) + m) := h₀ 5
  rw [h4] at h3
  have h5 : y = (0 : ℝ) := by
    norm_num at h3
    linarith
  rw [show y = (0 : ℝ) by linarith] at hy2
  have h7 : f (0 : ℝ) = (0 - 5) / (2 * (0 : ℝ) + m) := h₀ 0
  have h8 : f (0 : ℝ) = (5 : ℝ) := by linarith [hy2]
  rw [h7] at h8
  have h9 : m ≠ 0 := by
    by_contra h
    rw [h] at h8
    norm_num at h8
    all_goals linarith
  have h10 : m = -1 := by
    field_simp [h9] at h8
    linarith
  exact h10