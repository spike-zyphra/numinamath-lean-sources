import Mathlib

theorem algebra_220644 (a b c : ℝ) (h₀ : a * 1 + b * 2 + c * 1 * 2 = 3)
    (h₁ : a * 2 + b * 3 + c * 2 * 3 = 4) (d : ℝ) (hd : d ≠ 0) (h₂ : ∀ x, a * x + b * d + c * x * d = x) :
    d = 4 := by

  have eq1 : a + 2 * b + 2 * c = 3 := by
    nlinarith

  have eq2 : 2 * a + 3 * b + 6 * c = 4 := by
    nlinarith
  
  have eq3 := h₂ 0
  have eq4 : b * d = 0 := by 
    nlinarith

  have hb : b = 0 := by
    cases (mul_eq_zero.mp eq4) with
    | inl h => 
      linarith
    | inr h => 
      exfalso
      apply hd
      linarith

  have eq5 := h₂ 1
  rw [hb] at eq5
  have eq6 : a + c * d = 1 := by
    nlinarith
  
  have eq7 : a + 2 * c = 3 := by 
    rw [hb] at eq1
    linarith

  have eq8 : 2 * a + 6 * c = 4 := by 
    rw [hb] at eq2
    linarith
  
  have hc : c = -1 := by
    nlinarith [eq7, eq8]

  have ha : a = 5 := by 
    linarith [eq7, hc]

  rw [ha, hc] at eq6
  nlinarith