import Mathlib

/- Given that $\alpha $, $\beta $ are the two roots of the equation $x^2-3x-5=0$, then the value of $\frac{25}{2\alpha -1}+\frac{13}{\alpha +2\beta }+{{\beta }^{2}}$ is ___          ___. -/
theorem algebra_4198 {α β : ℝ} (h : α ≠ β) (h1 : α ^ 2 - 3 * α - 5 = 0) (h2 : β ^ 2 - 3 * β - 5 = 0) :
    25 / (2 * α - 1) + 13 / (α + 2 * β) + β ^ 2 = 12 := by
  have h3 : α + β = 3 := by
    have subtraction : (α - β) * (α + β - 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp subtraction) with h4 h5
    · -- case $\alpha - \beta = 0$, so $\alpha = \beta$
      exfalso
      exact h (by linarith)
    · -- case $\alpha + \beta - 3 = 0$, so $\alpha + \beta = 3$
      linarith

  have h4 : α * β = -5 := by
    nlinarith [sq_pos_of_ne_zero (show (α - β : ℝ) ≠ 0 by
      intro h5
      apply h
      linarith
    ), h3]

  have h5 : 2 * α - 1 ≠ 0 := by
    by_contra H
    have h6 : α = 1 / 2 := by linarith
    rw [h6] at h1
    nlinarith

  have h6 : α + 2 * β ≠ 0 := by
    by_contra H
    have eq : α + 2 * β = 0 := by linarith
    nlinarith [sq_pos_of_ne_zero (show (α - β) ≠ 0 by intro h7; apply h; linarith), h3, h4]

  have h7 : β ^ 2 = 3 * β + 5 := by
    nlinarith

  have eq : 25 / (2 * α - 1) + 13 / (α + 2 * β) + β ^ 2 = 12 := by
    field_simp [h5, h6]
    nlinarith [sq_pos_of_ne_zero (show α - β ≠ 0 by
      intro h7
      apply h
      linarith
    ), sq_nonneg (α - β), sq_nonneg (2 * α - 1), sq_nonneg (α + 2 * β), h1, h2, h3, h4]

  exact eq