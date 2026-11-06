import Mathlib

theorem number_theory_57116 {s g : ℕ} (h₀ : s < 100) (h₁ : g < 100) (h₂ : ∃ k, k^2 = 100 * g + s) (h₃ : ∃ m, m^2 = 100 * (g + 13) + (s + 13)) : s + g = 55 := by
  rcases h₂ with ⟨k, hk⟩
  rcases h₃ with ⟨m, hm⟩
  have h4 : m^2 = k^2 + 1313 := by
    nlinarith
  have h8 : k < 100 := by
    nlinarith [show 100 * g + s < 10000 by nlinarith [h₀, h₁], hk]
  have h9 : m < 107 := by
    nlinarith [h4, h8]
  interval_cases k <;> interval_cases m <;> omega