import Mathlib

theorem number_theory_228249 (n : ℕ) (h₀ : n > 0) (h₁ : ∃ x y, x * 15 + y * 20 = n / 2 ∧ x + y = 2)
    (h₂ : ∃ z w, z * 15 + w * 20 = n / 4 ∧ z + w = 3) :
    n = 150 := by
  rcases h₁ with ⟨x, y, h₁₁, h₁₂⟩
  rcases h₂ with ⟨z, w, h₂₁, h₂₂⟩
  have h₁₂' : x ≤ 2 := by 
    omega
  have h₂₂' : z ≤ 3 := by 
    omega
  interval_cases x <;> interval_cases z <;> omega