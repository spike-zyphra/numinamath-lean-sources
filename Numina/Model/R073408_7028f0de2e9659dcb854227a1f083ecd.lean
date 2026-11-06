import Mathlib

theorem algebra_2806 {a b c d : ℝ} (h : ∀ x, 5*x^3-34*x^2+94*x-81=a*(x-2)^3+b*(x-2)^2+c*(x-2)+d) :
    a*d+b*c=-17 := by

  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 3
  have eq5 := h 4
  norm_num at eq1 eq2 eq3 eq4 eq5
  
  have ha : a = 5 := by
    linarith

  have hb : b = -4 := by
    linarith

  have hc : c = 18 := by
    linarith

  have hd : d = 11 := by
    linarith

  rw [ha, hb, hc, hd]
  norm_num
  all_goals linarith
  all_goals linarith
  all_goals linarith
  all_goals linarith
  all_goals linarith
  all_goals linarith
  all_goals linarith