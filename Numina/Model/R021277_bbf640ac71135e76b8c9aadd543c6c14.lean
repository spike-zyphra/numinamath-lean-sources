import Mathlib

theorem algebra_208265 {f : ℝ → ℝ → ℝ} (h₀ : ∀ x, f x x = 0) (h₁ : ∀ x y z, f x (f y z) = f x y + z) :
    f 1993 1935 = 58 := by
  have h2 : ∀ x, f x 0 = x := by
    intro x
    have h3 : f x 0 = x := by
      have h4 : f x (f x x) = f x x + x := h₁ x x x
      rw [h₀ x] at h4
      norm_num at h4 ⊢
      linarith
    assumption
  have h3 : f 1993 1935 = 58 := by
    have h4 : f 1993 (f 1935 1935) = f 1993 1935 + 1935 := by
      apply h₁ 1993 1935 1935
    have h5 : f 1935 1935 = (0 : ℝ) := by
      apply h₀ 1935
    rw [h5] at h4
    have h6 : f 1993 (0 : ℝ) = (1993 : ℝ) := by
      apply h2 1993
    rw [h6] at h4
    linarith
  tauto