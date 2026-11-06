import Mathlib

theorem algebra_208126 :
    ¬∃ f g : Polynomial ℝ, ∀ x y : ℝ, x^200 * y^200 + 1 = f.eval x * g.eval y := by 
  intro h
  rcases h with ⟨f, g, h⟩
  have eq1 := h 1 1
  norm_num at eq1
  have eq2 := h 1 0
  norm_num at eq2
  have eq3 := h 0 1
  norm_num at eq3
  have eq4 := h 0 0
  norm_num at eq4
  nlinarith [sq_nonneg (f.eval 1 - f.eval 0), sq_nonneg (g.eval 1 - g.eval 0), 
          sq_nonneg (f.eval 0), sq_nonneg (g.eval 0), 
          sq_nonneg (f.eval 1), sq_nonneg (g.eval 1)]