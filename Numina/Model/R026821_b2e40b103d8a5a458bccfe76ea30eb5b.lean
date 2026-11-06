import Mathlib

theorem algebra_237565 (borche m father : ℕ)
    (h₀ : m = 3 * borche) (h₁ : father = m + 4) (h₂ : borche + m + father = 88) :
    borche = 12 ∧ m = 36 ∧ father = 40 := by 
  have eq1 : father = 3 * borche + 4 := by
    rw [h₁, h₀]
    all_goals omega
  have eq2 : borche + m + father = 88 := h₂
  rw [show m = 3 * borche by omega, show father = 3 * borche + 4 by omega] at eq2
  have eq3 : borche = 12 := by
    omega
  have eq4 : m = 36 := by
    rw [h₀]
    omega
  have eq5 : father = 40 := by
    omega
  exact ⟨eq3, eq4, eq5⟩