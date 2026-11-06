import Mathlib

/- If the root of the equation $\frac{2x+a}{x+2}=-1$ with $x$ as the unknown is a negative number, then the range of the real number $a$ is ___          ___. -/
theorem algebra_2231 (a : ℝ) (h : ∃ x : ℝ, x < 0 ∧ (2 * x + a) / (x + 2) = -1) :
    a > -2 ∧ a ≠ 4 := by
  rcases h with ⟨x, hx1, heq⟩
  have hx2 : x + 2 ≠ 0 := by
    by_contra h'
    have eq1 : x = -2 := by linarith
    rw [eq1] at heq
    norm_num at heq
  have eq1 : 2 * x + a = - (x + 2) := by
    have h1 : x + 2 ≠ 0 := hx2
    field_simp [h1] at heq
    linarith
  have eq2 : x = (-2 - a) / 3 := by
    linarith
  have ha1 : a > -2 := by
    rw [eq2] at hx1
    linarith
  have ha2 : a ≠ 4 := by
    by_contra h'
    have eq3 : x = -2 := by
      rw [show a = 4 by linarith] at eq2
      norm_num at eq2 ⊢
      linarith
    have h4 : x + 2 = 0 := by linarith
    contradiction
  exact ⟨ha1, ha2⟩