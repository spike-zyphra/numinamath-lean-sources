import Mathlib

theorem algebra_10664 {a : ℝ} (h : ∃ x y, ∀ t, (4*t^2-12*t+a) = (x+y*t)^2) :
    a = 9 := by 
  rcases h with ⟨x, y, h_eq⟩
  have eq1 := h_eq 0
  have eq2 := h_eq 1
  have eq3 := h_eq 2
  nlinarith [eq1, eq2, eq3]
  all_goals nlinarith