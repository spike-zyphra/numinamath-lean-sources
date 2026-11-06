import Mathlib

theorem number_theory_143676 (n : ℕ) (h₀ : Even n) (h₁ : Even (n + 2)) (h₂ : Even (n + 4)) :
    3 ∣ n + (n + 2) + (n + 4) := by 
  have h3 : n + (n + 2) + (n + 4) = 3 * (n + 2) := by 
    omega 
  rw [h3]
  exact ⟨n + 2, by ring⟩