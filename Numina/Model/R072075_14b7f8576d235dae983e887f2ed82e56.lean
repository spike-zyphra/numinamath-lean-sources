import Mathlib

theorem algebra_14292 {a b c : ℤ} (h1 : ∀ x, x^2 + 15 * x + 54 = (x + a) * (x + b)) (h2 : ∀ x, x^2 - 17 * x + 72 = (x - b) * (x - c)) : a + b + c = 23 := by
  have eq1 := h1 0
  have eq2 := h1 1
  have eq3 := h1 (-1)
  have eq4 := h2 0
  have eq5 := h2 1
  have eq6 := h2 (-1)
  ring_nf at eq1 eq2 eq3 eq4 eq5 eq6

  have h3 : a + b = 15 := by
    nlinarith
  
  have h4 : b + c = 17 := by
    nlinarith
  
  have h5 : b = 9 ∨ b = 6 := by
    have h3' : a = 15 - b := by linarith
    rw [h3'] at eq1 
    have h : b^2 - 15 * b + 54 = 0 := by 
      nlinarith 
    have h6 : (b - 9) * (b - 6) = 0 := by 
      nlinarith 
    cases (mul_eq_zero.1 h6) with
    | inl h7 =>
      left 
      linarith 
    | inr h8 =>
      right 
      linarith 
  rcases h5 with (hb | hb)
  · -- Case 1: b = 9
    have ha : a = 6 := by 
      linarith 
    have hc : c = 8 := by 
      linarith 
    linarith 
  · -- Case 2: b = 6
    have ha : a = 9 := by 
      linarith 
    have hc : c = 11 := by 
      linarith 
    rw [show b = 6 by linarith, show c = 11 by linarith] at eq4
    all_goals nlinarith