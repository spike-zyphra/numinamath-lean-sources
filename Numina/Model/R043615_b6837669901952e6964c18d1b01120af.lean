import Mathlib

theorem algebra_197382 {a b c : ℝ} (ha : a ≠ 0) (h : ∀ x, 2*x^4+x^3-41*x^2+83*x-45 = (a*x^2+b*x+c)*(x^2+4*x+9)) :
    a = 2 ∧ b = -7 ∧ c = 5 := by 
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 3
  have eq5 := h 4
  have eq6 := h 5
  ring_nf at eq1 eq2 eq3 eq4 eq5 eq6 
  have hc : c = -5 := by linarith [eq1]
  have ha' : a = 2 := by nlinarith [eq2, eq3, eq4, eq5, hc]
  have hb : b = -7 := by nlinarith [eq2, eq3, eq4, eq5, hc, ha']
  rw [hc] at eq6
  rw [ha'] at eq6
  rw [hb] at eq6
  nlinarith