import Mathlib

theorem algebra_103889 (x y : ℝ) (h : x^2 + y^2 + x * y = 1) :
    x + y ≤ 2 * Real.sqrt 3 / 3 := by
  have h1 : (x + y) ^ 2 ≤ 4 / 3 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x + 2 * y), sq_nonneg (2 * x + y)]
  have h2 : (x + y) ≤ Real.sqrt (4 / 3) := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have h3 : Real.sqrt (4 / 3) = 2 * Real.sqrt 3 / 3 := by
    have h4 : Real.sqrt (4 / 3) = Real.sqrt (4 / 3) := by rfl
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num [Real.sq_sqrt]
    <;> linarith [Real.sqrt_nonneg 3]
  linarith [h2, h3]