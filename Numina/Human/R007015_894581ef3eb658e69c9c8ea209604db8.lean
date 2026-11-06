import Mathlib

/- Masha has a quadratic of the form $x^2+bx+1$, where $b$ is a specific positive number. Using her knowledge of how to complete the square, Masha is able to rewrite this quadratic in the form $(x+m)^2-63$. What is $b$? -/
theorem algebra_22001 {b : ℝ} (hb : b > 0) (h : ∀ x, x^2 + b * x + 1 = (x + m)^2 - 63) :
    b = 16 := by
  -- considering the constant terms, we have $m ^ 2 = 64$, so $m = 8, -8$
  have meq : m = 8 ∨ m = -8 := by
    have eq := h 0
    apply sub_eq_zero_of_eq at eq
    have eq2 : 0 ^ 2 + b * 0 + 1 - ((0 + m) ^ 2 - 63) = (8 - m) * (m + 8) := by
      ring_nf
    rw [eq, zero_eq_mul] at eq2
    rcases eq2 with eq2 | eq2
    left
    linarith
    right
    linarith
  -- if $m = 8$ then $b = 16$, else $b$ would be negative, a contradiciton
  rcases meq with meq | meq
  any_goals
  have eq := h (-m)
  simp [meq] at eq
  linarith