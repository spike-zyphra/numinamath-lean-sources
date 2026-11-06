import Mathlib

theorem other_54831 (f : ℝ → ℝ)
    (h₀ : MonotoneOn f (Set.Icc 0 1))
    (h₁ : ∀ x, f (x / 3) = f x / 2)
    (h₂ : ∀ x, f (10 * x) = 2018 - f x)
    (h₃ : f 1 = 2018) :
    f (12 / 13) = 2018 := by
  have h4 : f 0 = 0 := by
    have h5 := h₁ 0
    norm_num at h5
    linarith
  have h6 : f 0 = 2018 - f 0 := by
    specialize h₂ 0
    norm_num at h₂
    linarith
  rw [h4] at h6
  linarith