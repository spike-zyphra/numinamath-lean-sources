import Mathlib

theorem algebra_237575 {a b c d : ℤ} (h₀ : a + b + c + d = 100) (h₁ : a + c + d = 65)
    (h₂ : a + b + c = 78) (h₃ : a = b - 10) :
    a = 25 ∧ b = 35 ∧ c = 18 ∧ d = 22 := by

  have eq5 : 2 * b + c = 88 := by
    linarith [h₃, h₂]

  have eq6 : 2 * b + c + d = 110 := by 
    linarith [h₃, h₀]

  have eq7 : b + c + d = 75 := by 
    linarith [h₃, h₁]

  have eq8 : b = 35 := by
    linarith [eq6, eq7]

  have eq9 : c = 18 := by
    linarith [eq5, eq8]

  have eq10 : d = 22 := by
    linarith [eq7, eq8, eq9]

  have eq11 : a = 25 := by
    linarith [h₃, eq8]

  exact ⟨eq11, eq8, eq9, eq10⟩