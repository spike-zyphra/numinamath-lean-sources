import Mathlib

theorem algebra_15234 {a b c : ℝ} (ha : a ≠ 0) (h : ∀ x, (5*x^2-3*x+7/3)*(a*x^2+b*x+c) = 15*x^4 - 14*x^3 + 20*x^2 - 25/3*x + 14/3) :
    b = -1 := by 
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 3
  have eq5 := h 4
  ring_nf at eq1 eq2 eq3 eq4 eq5
  have h1 : c = 2 := by
    linarith
  -- Substitute c = 2 into the other equations to solve for a and b
  have h2 : a = 3 := by
    rw [h1] at eq2 eq3 eq4 eq5
    linarith
  -- Substitute a = 3 and c = 2 into the equations to solve for b
  have h3 : b = -1 := by
    rw [h1, h2] at eq2 eq3 eq4 eq5
    linarith
  exact h3