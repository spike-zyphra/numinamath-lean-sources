import Mathlib

theorem algebra_130532 :
    ¬∃ f g : Polynomial ℝ, ∀ x y : ℝ, x ^ 200 * y ^ 200 + 1 = f.eval x * g.eval y := by 
  rintro ⟨f, g, h⟩
  have eq1 := h 1 1
  have eq2 := h 0 0
  have eq3 := h 0 1
  have eq4 := h 1 0
  norm_num at eq1 eq2 eq3 eq4 
  nlinarith [sq_nonneg (f.eval 1 * g.eval 1 - 2), sq_nonneg (f.eval 0 * g.eval 0 - 1), sq_nonneg (f.eval 0 * g.eval 1 - 1), sq_nonneg (f.eval 1 * g.eval 0 - 1)]