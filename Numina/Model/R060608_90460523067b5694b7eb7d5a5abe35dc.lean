import Mathlib

theorem algebra_2395 {a b c : ℝ} (h : ∀ x, 2*x^2-3*x-1=a*(x-1)^2+b*(x-1)+c) :
    (a+b)/c=-3/2 := by
  have eq1 := h 1
  have eq2 := h 0
  have eq3 := h 2
  norm_num at eq1 eq2 eq3
  have hc : c = -2 := by linarith
  have h5 : c ≠ 0 := by linarith [hc]
  have eq4 : a = 2 := by 
    nlinarith
  have eq5 : b = 1 := by 
    nlinarith [eq4, hc]
  rw [eq4, eq5, hc]
  all_goals norm_num