import Mathlib

theorem algebra_16601 {f : ℝ → ℝ} (h : ∀ x y, f x * f y - f (x * y) = x + y) :
    f 2 = 3 := by
  have h1 := h 0 0
  simp at h1
  have h2 := h 0 1
  simp at h2
  have hf0 : f 0 = 1 := by
    have h3 : f 0 = 0 ∨ f 0 = 1 := by
      have : f 0 * (f 0 - 1) = 0 := by linarith 
      cases' (mul_eq_zero.mp this) with h4 h5
      · 
        left
        linarith
      · 
        right
        linarith
    cases' h3 with h6 h7
    · -- f 0 = 0
      rw [h6] at h2
      norm_num at h2
      all_goals linarith
    · 
      exact h7
  have eq1 := h 2 0
  simp [hf0] at eq1 
  linarith