import Mathlib
open Real
theorem algebra_94616 {x : ℝ} (hx : x ≠ 0) (h : 2003 / 2004 * x + 1 + 1 / x = 0) :
∃ y:ℝ, 2003/2004 * y + 1 + 1 / y = 0 ∧ 1/x + 1/y = -1 := by
  have eq1 : 2003 / 2004 * x^2 + x + 1 = 0 := by
    have h1 : 2003 / 2004 * x + 1 + 1 / x = 0 := h
    have h2 : x ≠ 0 := hx
    field_simp at h1
    nlinarith
  use -2004/2003 - x
  constructor
  · -- Show that $y$ is a root of the original equation
    have h2 : 2003 / 2004 * x^2 + x + 1 = 0 := eq1
    field_simp [(show (-2004 / 2003 - x : ℝ) ≠ 0 by
      by_contra h'
      have eq3 : -2004 / 2003 - x = 0 := by linarith
      have eq4 : x = -2004 / 2003 := by linarith
      rw [eq4] at eq1
      norm_num at eq1
      all_goals linarith
    )]
    nlinarith
  · -- Show that $ \frac{1}{x} + \frac{1}{y} = -1$
    have h2 : 2003 / 2004 * x^2 + x + 1 = 0 := eq1
    field_simp [(show (-2004 / 2003 - x : ℝ) ≠ 0 by
      by_contra h'
      have eq3 : -2004 / 2003 - x = 0 := by linarith
      have eq4 : x = -2004 / 2003 := by linarith
      rw [eq4] at eq1
      norm_num at eq1
      all_goals linarith
    )]
    nlinarith [sq_pos_of_ne_zero hx, sq_nonneg (x + 2004 / 2003), sq_nonneg (x + (-2004 / 2003 - x))]