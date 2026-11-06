import Mathlib

theorem algebra_14614 {j k : ℝ} (h₀ : 5 * j - 42 * k = 1) (h₁ : 2 * k - j = 3) :
    j = -4 ∧ k = -1 / 2 := by
  have h2 : j = 2 * k - 3 := by
    linarith [h₁]
  have hk : k = -1 / 2 := by
    rw [h2] at h₀
    linarith
  have hj : j = -4 := by
    rw [hk] at h2
    linarith
  exact ⟨hj, hk⟩