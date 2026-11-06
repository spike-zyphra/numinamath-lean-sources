import Mathlib

theorem number_theory_186370 (z1 z2 : ℕ) (h₀ : z1 + z2 = 2555) (h₁ : z1 > z2)
    (h₂ : ∃ k, z1 = k * 100 + z2) (h₃ : ∃ m, z2 = m * 100 + (z1 % 100)) :
    z1 = 2323 ∧ z2 = 232 := by
  rcases h₂ with ⟨k, hk⟩
  rcases h₃ with ⟨m, hm⟩
  have h4 : z1 + z2 = 2555 := h₀
  have eq1 : z1 = k * 100 + z2 := hk
  have eq2 : z2 = m * 100 + (z1 % 100) := hm
  have h5 : z1 % 100 = z2 % 100 := by
    omega
  have h6 : z1 = 2323 := by
    omega
  have h7 : z2 = 232 := by
    omega
  exact ⟨h6, h7⟩