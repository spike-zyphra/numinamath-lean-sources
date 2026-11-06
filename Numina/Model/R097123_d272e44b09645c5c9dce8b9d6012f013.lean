import Mathlib

theorem algebra_12963 {α β : ℝ} (h : α^2 - 20 * α - 19 = 0) (h' : β^2 - 20 * β - 19 = 0)
    (h'' : α ≠ β) : α^3 + β^3 = 9140 := by
  have eq1 : α^2 - β^2 = 20 * (α - β) := by
    nlinarith
  have eq2 : (α - β) * (α + β - 20) = 0 := by
    nlinarith [eq1]
  cases' (mul_eq_zero.mp eq2) with eq3 eq4
  · -- Case $\alpha - \beta = 0$
    exfalso
    apply h''
    linarith
  · -- Case $\alpha + \beta - 20 = 0$
    have h2 : α + β = 20 := by linarith
    have h3 : α^2 + β^2 = 20 * (α + β) + 38 := by
      nlinarith
    have h4 : α * β = -19 := by
      rw [h2] at h3
      nlinarith [h3, h2]
    have eq5 : α^3 + β^3 = (α + β) ^ 3 - 3 * (α * β) * (α + β) := by
      ring
    rw [eq5, h2, h4]
    norm_num