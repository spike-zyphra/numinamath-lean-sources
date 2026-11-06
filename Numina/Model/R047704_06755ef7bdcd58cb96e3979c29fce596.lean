import Mathlib

theorem algebra_171105 {r b g : ℕ} (h₀ : r + b + g = 675)
    (h₁ : r / 2 = b * (2 / 3 : ℚ)) (h₂ : b * (2 / 3 : ℚ) = g * (3 / 4 : ℚ)) :
    r / 2 = 225 ∧ b * (2 / 3 : ℚ) = 225 ∧ g * (3 / 4 : ℚ) = 225 := by
  have eq1 : (3 : ℚ) * (r : ℚ) = (4 : ℚ) * (b : ℚ) := by
    have eq3 : (r : ℚ) / 2 = (b : ℚ) * (2 / 3 : ℚ) := by
      simpa using h₁
    field_simp at eq3 ⊢
    linarith
  have eq4 : (8 : ℚ) * (b : ℚ) = (9 : ℚ) * (g : ℚ) := by
    have eq5 : (b : ℚ) * (2 / 3 : ℚ) = (g : ℚ) * (3 / 4 : ℚ) := by
      simpa using h₂
    field_simp at eq5 ⊢
    linarith
  have eq3 : 3 * (r : ℤ) = 4 * (b : ℤ) := by
    have eq1' : (3 : ℚ) * (r : ℚ) = (4 : ℚ) * (b : ℚ) := eq1
    have eq2 : (3 * (r : ℤ) : ℚ) = (4 * (b : ℤ) : ℚ) := by
      simpa using eq1'
    exact_mod_cast eq2
  have eq6 : 8 * (b : ℤ) = 9 * (g : ℤ) := by
    have eq4' : (8 : ℚ) * (b : ℚ) = (9 : ℚ) * (g : ℚ) := eq4
    have eq5 : (8 * (b : ℤ) : ℚ) = (9 * (g : ℤ) : ℚ) := by
      simpa using eq4'
    exact_mod_cast eq5
  omega