import Mathlib

theorem number_theory_214742 (v : ℕ → ℤ)
    (h₀ : v 0 = 0)
    (h₁ : v 1 = 1)
    (h₂ : ∀ n, v (n + 1) = 8 * v n - v (n - 1)) :
    ¬∃ α β : ℕ, α > 0 ∧ β > 0 ∧ ∃ n, v n = 3 ^ α * 5 ^ β := by
  have eq1 := h₂ 0
  simp [h₀] at eq1 
  nlinarith [h₁, eq1]