import Mathlib

theorem algebra_186262 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : d / v = 5) (h₃ : d / (1.25 * v) = 1 / 5 + 5) :
    d = 150 := by
  have h4 : v = d / 5 := by
    have h5 : v ≠ 0 := by
      linarith
    field_simp [h5] at h₂ ⊢
    linarith
  rw [h4] at h₃
  have h5 : d > 0 := h₀
  have h7 : d / (1.25 * (d / 5)) = 4 := by
    field_simp [show d ≠ 0 by linarith]
    <;> ring_nf <;> field_simp [show d ≠ 0 by linarith] <;> linarith
  rw [h7] at h₃
  norm_num at h₃ 
  all_goals linarith