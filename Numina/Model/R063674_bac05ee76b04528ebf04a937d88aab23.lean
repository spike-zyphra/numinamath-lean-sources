import Mathlib

/- If $\sqrt{2x+1}+\sqrt{3y-2}=4$, then the range of values for $2x+3y$ is ___          ___. -/
theorem algebra_10923 (x y : ℝ) (hx : 0 ≤ 2 * x + 1) (hy : 0 ≤ 3 * y - 2)
    (h : Real.sqrt (2 * x + 1) + Real.sqrt (3 * y - 2) = 4) :
    9 ≤ 2 * x + 3 * y ∧ 2 * x + 3 * y ≤ 17 := by
  let a := Real.sqrt (2 * x + 1)
  let b := Real.sqrt (3 * y - 2)
  have h1 : a + b = 4 := h
  have ha2 : a ^ 2 = 2 * x + 1 := Real.sq_sqrt hx
  have hb2 : b ^ 2 = 3 * y - 2 := Real.sq_sqrt hy
  have eq1 : 2 * x + 3 * y = a^2 + b^2 + 1 := by
    linarith [ha2, hb2]
  have eq2 : b = 4 - a := by linarith
  have eq3 : 2 * x + 3 * y = 2 * a^2 - 8 * a + 17 := by
    rw [eq1, eq2]
    ring
  have ha_nonneg : 0 ≤ a := by positivity
  have ha_le : a ≤ 4 := by
    have hbl : 0 ≤ b := by positivity
    linarith [h1, hbl]
  have h9 : 9 ≤ 2 * a^2 - 8 * a + 17 := by
    nlinarith [sq_nonneg (a - 2), ha_nonneg, ha_le]
  have h17 : 2 * a^2 - 8 * a + 17 ≤ 17 := by
    nlinarith [sq_nonneg (a - 4), ha_nonneg, ha_le]
  constructor
  · linarith [eq3, h9]
  · linarith [eq3, h17]