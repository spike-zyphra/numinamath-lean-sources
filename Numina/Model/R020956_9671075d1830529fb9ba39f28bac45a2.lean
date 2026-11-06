import Mathlib

theorem algebra_156707 (a b c : ℝ) (h₀ : a * 1 + b * 2 + c * 1 * 2 = 3)
    (h₁ : a * 2 + b * 3 + c * 2 * 3 = 4) (d : ℝ) (hd : d ≠ 0)
    (h₂ : ∀ x, a * x + b * d + c * x * d = x) : d = 4 := by

  have eq1 := h₂ 1
  have eq2 := h₂ 0
  have eq3 := h₂ 2
  have eq4 : b * d = 0 := by
    linarith
  
  have eq5 : b = 0 := by
    apply (mul_left_inj' hd).mp
    linarith

  have eq6 : c = -1 := by
    have eq7 : a + 2 * b + 2 * c = 3 := by 
      linarith
    have eq8 : 2 * a + 3 * b + 6 * c = 4 := by 
      linarith
    rw [eq5] at eq7 eq8
    linarith

  have eq7 : a = 5 := by
    have eq3' : a + 2 * b + 2 * c = 3 := by
      linarith
    rw [eq5, eq6] at eq3'
    linarith

  have eq8 : a + b * d + c * d = 1 := by 
    specialize h₂ 1
    linarith

  rw [eq5, eq6, eq7] at eq8
  linarith