import Mathlib

theorem algebra_237138 (a b c d : ℝ) (h₀ : a + b + c + d = 89.6)
    (h₁ : (1 / 2) * a = (1 / 3) * b) (h₂ : (1 / 3) * b = (1 / 4) * c)
    (h₃ : (1 / 4) * c = (1 / 5) * d) :
    a = 12.8 ∧ b = 19.2 ∧ c = 25.6 ∧ d = 32 := by
  have eq1 : 3 * a = 2 * b := by
    linarith
  have eq2 : 4 * b = 3 * c := by
    linarith
  have eq3 : 5 * c = 4 * d := by
    linarith
  have h4 : a = 12.8 := by
    norm_num at h₀ eq1 eq2 eq3 ⊢
    linarith
  have h5 : b = 19.2 := by
    norm_num at h₀ eq1 eq2 eq3 ⊢
    linarith
  have h6 : c = 25.6 := by
    norm_num at h₀ eq1 eq2 eq3 ⊢
    linarith
  have h7 : d = 32 := by
    norm_num at h₀ eq1 eq2 eq3 ⊢
    linarith
  exact ⟨h4, h5, h6, h7⟩