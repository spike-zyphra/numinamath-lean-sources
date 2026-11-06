import Mathlib

theorem algebra_279117 (a : ℕ → ℝ) (h₀ : a 0 = 30) (h₁ : a 16 = 110)
    (h₂ : ∃ d, ∀ n, a n = a 0 + d * n) :
    a 8 = 70 := by
  rcases h₂ with ⟨d, hd⟩
  have h3 : a 16 = a 0 + d * 16 := hd 16
  rw [h₀] at h3
  rw [h₁] at h3
  have hd_val : d = 5 := by
    linarith
  have h4 : a 8 = a 0 + d * 8 := hd 8
  rw [h₀, hd_val] at h4
  norm_num at h4
  linarith