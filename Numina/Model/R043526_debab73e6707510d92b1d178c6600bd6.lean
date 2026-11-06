import Mathlib

/- Given that $\alpha$ and $\beta$ are the two real roots of the equation $x^2-3x-5=0$, then the value of $\frac{25}{2 \alpha -1}+ \frac{13}{\alpha +2 \beta}+ \beta^2$ is ___          ___. -/
theorem algebra_4797 {α β : ℝ} (h : α^2-3*α-5=0) (h' : β^2-3*β-5=0)
  (h'' : α≠β) : 25/(2*α-1)+13/(α+2*β)+β^2=12 := by
  have h1 : α + β = 3 := by
    have h2 : α^2 - 3 * α - 5 = 0 := h
    have h3 : β^2 - 3 * β - 5 = 0 := h'
    have h4 : (α - β) * (α + β - 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case h5 = α - β = 0
      exfalso
      apply h''
      linarith
    · -- Case h6 = α + β - 3 = 0
      linarith
  have h2 : α * β = -5 := by
    have h3 : α + β = 3 := h1
    have eq1 : α^2 = 3 * α + 5 := by linarith [h]
    have eq2 : β^2 = 3 * β + 5 := by linarith [h']
    have eq3 : (α + β) ^ 2 = 9 := by
      rw [show (α + β) = 3 by linarith [h3]]
      norm_num
    have eq4 : α^2 + β^2 + 2 * (α * β) = 9 := by
      linarith [eq3]
    have eq5 : α^2 + β^2 = 3 * α + 5 + (3 * β + 5) := by
      linarith [eq1, eq2]
    have eq6 : α^2 + β^2 = 3 * (α + β) + 10 := by
      nlinarith [eq5, h3]
    have eq7 : α^2 + β^2 = 3 * 3 + 10 := by
      rw [show α + β = 3 by linarith [h3]] at eq6
      linarith
    have eq8 : α^2 + β^2 = 19 := by
      linarith [eq7]
    have eq9 : α * β = -5 := by
      nlinarith [eq4, eq8, h3]
    exact eq9
  have h2_a : 2 * α - 1 ≠ 0 := by
    by_contra h3
    have eq1 : α = 1 / 2 := by linarith
    rw [eq1] at h
    nlinarith
  have h7Denom : α + 2 * β ≠ 0 := by
    by_contra h3
    have eq1 : α = -2 * β := by linarith
    rw [eq1] at h
    have h6 : α + β = 3 := h1
    have h5 : β^2 - 3 * β - 5 = 0 := h'
    have eq2 : α = -2 * β := eq1
    have eq3 : -2 * β + β = 3 := by
      linarith [eq2, h1]
    have eq4 : - (β) = 3 := by
      nlinarith [eq3]
    have eq5 : β = -3 := by
      linarith
    rw [eq5] at h'
    nlinarith
  have h4 : 25 / (2 * α - 1) + 13 / (α + 2 * β) + β^2 = 12 := by
    field_simp [(show 2 * α - 1 ≠ 0 by assumption), (show α + 2 * β ≠ 0 by assumption)]
    nlinarith [sq_nonneg (α - β), sq_nonneg (α + β - 3), sq_nonneg (α * β + 5), sq_pos_of_ne_zero (show α - β ≠ 0 by intro h1; apply h''; linarith), h, h']
  exact h4