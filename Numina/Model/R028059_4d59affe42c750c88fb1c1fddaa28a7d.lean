import Mathlib

/- If real numbers $x$ and $y$ satisfy $\frac{x+22}{y}+\frac{290}{xy}=\frac{26-y}{x}$, find $xy$.

 -/
theorem algebra_13784 {x y : ℝ} (hy : y ≠ 0) (hxy : x * y ≠ 0) (h : (x + 22) / y + 290 / (x * y) = (26 - y) / x) :
    x * y = -143 := by
  have hx : x ≠ 0 := by
    intro h0
    have : x * y = 0 := by
      rw [h0]
      norm_num
    contradiction
  have eq1 : x * (x + 22) + 290 = y * (26 - y) := by 
    have eq2 : (x + 22) / y + 290 / (x * y) = (26 - y) / x := h
    have eq3 : x * y ≠ 0 := hxy
    have eq4 : ((x + 22) / y + 290 / (x * y)) * (x * y) = ((26 - y) / x) * (x * y) := by 
      rw [eq2]
    have eq5 : ((x + 22) / y + 290 / (x * y)) * (x * y) = x * (x + 22) + 290 := by 
      field_simp [show y ≠ 0 by exact hy, show x ≠ 0 by exact hx]
      <;> ring
    have eq6 : ((26 - y) / x) * (x * y) = y * (26 - y) := by
      field_simp [show x ≠ 0 by exact hx, show y ≠ 0 by exact hy]
      <;> ring
    rw [eq5] at eq4
    rw [eq6] at eq4
    linarith 
  have eq2 : (x + 11) ^ 2 + (y - 13) ^ 2 = 0 := by 
    nlinarith 
  have eq3 : (x + 11) ^ 2 = 0 := by
    linarith [sq_nonneg (x + 11), sq_nonneg (y - 13)]
  have eq4 : (y - 13) ^ 2 = 0 := by
    linarith [sq_nonneg (x + 11), sq_nonneg (y - 13)]
  have eq5 : x + 11 = 0 := by
    rwa [sq_eq_zero_iff] at eq3 
  have eq6 : x = -11 := by
    linarith
  have eq7 : y - 13 = 0 := by
    rwa [sq_eq_zero_iff] at eq4 
  have eq8 : y = 13 := by
    linarith
  rw [eq6, eq8]
  all_goals
    norm_num