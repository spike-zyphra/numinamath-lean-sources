import Mathlib

theorem algebra_214743 :
    ¬∃ f g : Polynomial ℝ, ∀ x y : ℝ, x^200 * y^200 + 1 = f.eval x * g.eval y := by
  rintro ⟨f, g, h⟩
  have eq1 := h 0 0
  have eq2 := h 0 1
  have eq3 := h 1 0
  have eq4 := h 1 1
  norm_num at eq1 eq2 eq3 eq4
  have h1 : f.eval 0 ≠ 0 := by
    by_contra h1
    rw [h1] at eq1 eq2
    nlinarith
  have h2 : g.eval 0 ≠ 0 := by
    by_contra h2
    rw [h2] at eq1 eq3
    nlinarith
  have eq5 : g.eval 1 = g.eval 0 := by
    apply (mul_left_inj' h1).mp
    linarith
  have eq6 : f.eval 1 = f.eval 0 := by
    apply (mul_right_inj' h2).mp
    linarith
  rw [eq6, eq5] at eq4
  nlinarith