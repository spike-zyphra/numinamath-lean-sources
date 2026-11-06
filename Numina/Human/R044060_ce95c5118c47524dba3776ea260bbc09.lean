import Mathlib

/- Solve in $\mathbb{R}$ the equation :
$(x+1)^5 + (x+1)^4(x-1) + (x+1)^3(x-1)^2 +$ $ (x+1)^2(x-1)^3 + (x+1)(x-1)^4 + (x-1)^5 =$ $ 0$. -/
theorem algebra_90511 : {x : ℝ | (x + 1)^5 + (x + 1)^4 * (x - 1) + (x + 1)^3 * (x - 1)^2 +
    (x + 1)^2 * (x - 1)^3 + (x + 1) * (x - 1)^4 + (x - 1)^5 = 0} = {0} := by
  ext x
  simp
  constructor
  <;> intro h
  <;> nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 + 2 * x + 1)]
