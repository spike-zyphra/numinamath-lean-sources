import Mathlib

open Real

/- Given $x>0$ and $x=\frac{10}{3+\dfrac{10}{3+\cdots }}$, find the value of $x$.

 -/
theorem algebra_6908 {x : ℝ} (hx : x > 0) (h : x = 10 / (3 + 10 / (3 + 10 / (3 + x)))) : x = 2 := by
  have h1 : 3 + x > 0 := by linarith
  have h2 : 3 + 10 / (3 + x) > 0 := by
    have hx1_1 : 3 + x > 0 := by linarith
    have hx1_2 : 10 / (3 + x) > 0 := by
      apply div_pos
      norm_num
      all_goals linarith
    linarith
  have h3 : 3 + 10 / (3 + 10 / (3 + x)) > 0 := by
    have h4 : 3 + 10 / (3 + x) > 0 := h2
    have h5 : 10 / (3 + 10 / (3 + x)) > 0 := by
      apply div_pos
      norm_num
      all_goals linarith
    linarith
  field_simp [(show 3 + x ≠ 0 by linarith), (show 3 + 10 / (3 + x) ≠ 0 by
    by_contra h0
    have hx1_1 : 3 + x > 0 := by linarith
    have hx1_2 : 10 / (3 + x) > 0 := by
      apply div_pos
      norm_num
      all_goals linarith
    have hx1_3 : 3 + 10 / (3 + x) > 0 := by linarith
    linarith
  ), (show 3 + 10 / (3 + 10 / (3 + x)) ≠ 0 by
    by_contra h0
    have hx1_1 : 3 + 10 / (3 + x) > 0 := h2
    have hx1_2 : 10 / (3 + 10 / (3 + x)) > 0 := by
      apply div_pos
      norm_num
      all_goals linarith
    have hx1_3 : 3 + 10 / (3 + 10 / (3 + x)) > 0 := by linarith
    linarith
  )] at h
  have h4 : x ^ 2 + 3 * x - 10 = 0 := by
    nlinarith [sq_pos_of_pos hx, sq_nonneg (x + 5), sq_nonneg (x - 2), mul_pos hx hx]
  have h5 : (x - 2) * (x + 5) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h5) with h6 h7
  · -- Case where $x = 2$
    linarith
  · -- Case where $x = -5$, which contradicts $x > 0$
    linarith