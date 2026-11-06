import Mathlib

theorem algebra_238243 (d c r : ℝ)
    (h₀ : d + c + r = 17)
    (h₁ : 2*d + c + r = 29)
    (h₂ : 2*d + 3*c + r = 35) :
    d = 12 ∧ c = 3 ∧ r = 2 := by 
  have hd : d = 12 := by
    linarith
  have h3 : c + r = 5 := by 
    rw [hd] at h₀
    linarith
  have h4 : 3 * c + r = 11 := by
    rw [hd] at h₂
    linarith
  have hc : c = 3 := by 
    linarith [h3, h4]
  have hr : r = 2 := by
    linarith [h3, hc]
  exact ⟨hd, hc, hr⟩